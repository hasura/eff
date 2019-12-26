{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect2.Internal where

import Control.Monad
import Control.Natural (type (~>))
import Data.Kind (Constraint, Type)
import Data.Primitive.SmallArray
import GHC.Exts (Any, magicDict, Proxy#, proxy#)
import Unsafe.Coerce (unsafeCoerce)
import Data.Type.Equality
import Data.Proxy

type EffectK = (Type -> Type) -> Type -> Type

data HandlersK
  -- | @'ROOT' r@
  = ROOT Type
  -- | @'PROMPT' eff s i hs@
  | PROMPT EffectK Type Type HandlersK

type family R hs where
  R ('ROOT r) = r
  R ('PROMPT _ _ _ hs) = R hs

type family EffKs hs where
  EffKs ('ROOT _) = '[]
  EffKs ('PROMPT eff _ _ hs) = eff ': EffKs hs

class KnownLength (xs :: [k]) where
  lengthVal :: Int
instance KnownLength '[] where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance KnownLength xs => KnownLength (x ': xs) where
  lengthVal = lengthVal @_ @xs + 1
  {-# INLINE lengthVal #-}

class KnownLengthH (hs :: HandlersK) where
  lengthValH :: Int
instance KnownLengthH ('ROOT r) where
  lengthValH = 0
  {-# INLINE lengthValH #-}
instance KnownLengthH hs => KnownLengthH ('PROMPT eff s i hs) where
  lengthValH = lengthValH @hs + 1
  {-# INLINE lengthValH #-}

class KnownIndex (x :: k) (xs :: [k]) where
  indexVal :: Int
instance {-# OVERLAPPING #-} KnownLength xs => KnownIndex x (x ': xs) where
  indexVal = lengthVal @_ @xs
  {-# INLINE indexVal #-}
instance KnownIndex x xs => KnownIndex x (y ': xs) where
  indexVal = indexVal @_ @x @xs
  {-# INLINE indexVal #-}

class KnownIndexH (hs :: (HandlersK, HandlersK)) where
  indexValH :: Int
instance {-# OVERLAPPING #-} KnownLengthH hs => KnownIndexH '(hs, ('PROMPT eff s i hs)) where
  indexValH = lengthValH @hs
  {-# INLINE indexValH #-}
instance KnownIndexH '(as, bs) => KnownIndexH '(as, ('PROMPT eff s i bs)) where
  indexValH = indexValH @'(as, bs)
  {-# INLINE indexValH #-}

class (KnownIndex a b, KnownLength b) => a :< b
instance (KnownIndex a b, KnownLength b) => a :< b

class (KnownIndexH '(a, b), KnownLengthH b) => a :<< b
instance (KnownIndexH '(a, b), KnownLengthH b) => a :<< b

-- | Like ':<<', but only at the type level; the evidence will be erased at runtime. This is
-- slightly more efficient, since it doesn’t have to be passed around, but of course it means the
-- index value cannot actually be accessed.
type family a :<<! b :: Constraint where
  a :<<! a = ()
  a :<<! 'PROMPT _ _ _ b = a :<<! b

data WithLengthH a r = WithLengthH (KnownLengthH a => Proxy a -> r)
withLengthH :: forall a r. Int -> (KnownLengthH a => Proxy a -> r) -> r
withLengthH n f = magicDict (WithLengthH f) n (Proxy @a)
{-# INLINE withLengthH #-}

data WithIndexH a r = WithIndexH (KnownIndexH a => Proxy a -> r)
withIndexH :: forall a r. Int -> (KnownIndexH a => Proxy a -> r) -> r
withIndexH n f = magicDict (WithIndexH f) n (Proxy @a)
{-# INLINE withIndexH #-}


-- | If one 'HandlersK' is contained within the other, their roots must be equal.
rootsEq :: hs :<< hs' => R hs :~: R hs'
rootsEq = unsafeCoerce Refl
{-# INLINE rootsEq #-}

withRootsEq :: forall hs hs' r. hs :<< hs' => (R hs ~ R hs' => r) -> r
withRootsEq a = case rootsEq @hs @hs' of Refl -> a
{-# INLINE withRootsEq #-}

data Handler eff s i hs = Handler
  { hState :: s
  , hSend :: !(forall a hs'. ('PROMPT eff s i hs :<<! hs') => eff (Eff (EffKs hs')) a -> EffH hs' a)
  , hCont :: !(i -> Handlers hs -> R hs)
  }

-- | An array of 'Handler's stored in reverse order.
newtype Handlers (hs :: HandlersK) = Handlers { unHandlers :: SmallArray Any }

root :: Handlers ('ROOT r)
root = Handlers mempty
{-# INLINE root #-}

pushPrompt :: Handler eff s i hs -> Handlers hs -> Handlers ('PROMPT eff s i hs)
pushPrompt h (Handlers hs) = Handlers $ runSmallArray do
  let len = sizeofSmallArray hs
  hs' <- newSmallArray (len + 1) (error "pushPrompt: value left uninitialized")
  copySmallArray hs' 0 hs 0 len
  writeSmallArray hs' len (unsafeCoerce h)
  pure hs'

-- | Creates a new prompt and pushes it, synthesizing evidence for @('PROMPT eff s i hs :<< hs')@
-- from the length of the current handler stack.
pushPromptWithEvidence
  :: forall eff s i hs
   . s
  -> (forall hs'. ('PROMPT eff s i hs :<< hs') => eff (Eff (EffKs hs')) ~> EffH hs')
  -> (i -> Handlers hs -> R hs)
  -> Handlers hs
  -> Handlers ('PROMPT eff s i hs)
pushPromptWithEvidence s f k hs =
  let !idx = sizeofSmallArray $ unHandlers hs
      !len = idx + 1
      f' :: forall hs'. eff (Eff (EffKs hs')) ~> EffH hs'
      f' e = withLengthH @hs' len \_ -> withIndexH @'( 'PROMPT eff s i hs, hs') idx \_ -> f e
  in pushPrompt (Handler s f' k) hs
{-# INLINE pushPromptWithEvidence #-}

peekPrompt :: Handlers ('PROMPT eff s i hs) -> Handler eff s i hs
peekPrompt (Handlers hs) = unsafeCoerce $ indexSmallArray hs (sizeofSmallArray hs - 1)
{-# INLINE peekPrompt #-}

popPrompt :: Handlers ('PROMPT eff s i hs) -> (Handler eff s i hs, Handlers hs)
popPrompt (Handlers hs) =
  let idx = sizeofSmallArray hs - 1
      !h = unsafeCoerce $ indexSmallArray hs idx
      !hs' = Handlers $ cloneSmallArray hs 0 idx
  in (h, hs')

lookupPrompt :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => Handlers hs' -> Handler eff s i hs
lookupPrompt (Handlers hs) =
  let idx = indexValH @'( 'PROMPT eff s i hs, hs')
  in unsafeCoerce $ indexSmallArray hs idx
{-# INLINE lookupPrompt #-}

replacePrompt
  :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs')
  => Handler eff s i hs -> Handlers hs' -> Handlers hs'
replacePrompt h (Handlers hs) = Handlers $ runSmallArray do
  hs' <- thawSmallArray hs 0 (sizeofSmallArray hs)
  let idx = indexValH @'( 'PROMPT eff s i hs, hs')
  writeSmallArray hs' idx (unsafeCoerce h)
  pure hs'

takePromptsUpTo :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => Handlers hs' -> Handlers hs
takePromptsUpTo (Handlers hs) =
  let len = indexValH @'( 'PROMPT eff s i hs, hs')
  in Handlers $ cloneSmallArray hs 0 len
{-# INLINE takePromptsUpTo #-}

withHandler
  :: forall eff hs' r. (eff :< EffKs hs')
  => Handlers hs'
  -> (forall s i hs. ('PROMPT eff s i hs :<<! hs') => Handler eff s i hs -> r)
  -> r
withHandler (Handlers hs) f =
  let idx = indexVal @_ @eff @(EffKs hs') in
    case unsafeCoerce $ indexSmallArray hs idx of
      (h :: Handler eff s i hs) ->
        case unsafeCoerce Refl :: ('PROMPT eff s i hs :<<! hs') :~: (() :: Constraint) of
          Refl -> f h
{-# INLINE withHandler #-}

newtype EffH hs a = EffH { unEffH :: (a -> Handlers hs -> R hs) -> Handlers hs -> R hs }

runH :: EffH ('ROOT a) a -> a
runH (EffH m) = m (\v _ -> v) root
{-# INLINE runH #-}

instance Functor (EffH hs) where
  fmap f (EffH m) = EffH \k -> m \a -> k (f a)
  {-# INLINE fmap #-}

instance Applicative (EffH hs) where
  pure a = EffH ($ a)
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (EffH hs) where
  EffH m >>= f = EffH \k -> m \a -> unEffH (f a) k
  {-# INLINE (>>=) #-}

sendH :: forall eff hs. (eff :< EffKs hs) => eff (Eff (EffKs hs)) ~> EffH hs
sendH e = EffH \k hs -> withHandler @eff @hs hs \h -> unEffH (hSend h e) k hs
{-# INLINE sendH #-}

escapeH :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => EffH ('PROMPT eff s i hs) ~> EffH hs'
escapeH (EffH m) = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \k (Handlers hs) ->
  let len = indexValH @'( 'PROMPT eff s i hs, hs') + 1
      -- split out the handlers present in the handler’s original context
      !hs_len = Handlers $ cloneSmallArray hs 0 len
      k' a (Handlers hs_len') = k a $! Handlers $ runSmallArray do
        -- combine the modified handlers with the extra handlers in the local context
        hs' <- thawSmallArray hs 0 (sizeofSmallArray hs)
        copySmallArray hs' 0 hs_len' 0 len
        pure hs'
  in m k' hs_len

abortH :: forall eff s i hs hs' a. ('PROMPT eff s i hs :<< hs') => i -> EffH hs' a
abortH a = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \_ hs ->
  let h = lookupPrompt @eff @s @i @hs hs
  in hCont h a $! takePromptsUpTo @eff @s @i @hs hs

getH :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => EffH hs' s
getH = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \k !hs ->
  -- Note: we are explicitly strict in `hs` so that GHC will eagerly apply `hState` and avoid
  -- retaining the entire `hs` value without needing to be strict in the state value itself.
  k (hState $ lookupPrompt @eff @s @i @hs hs) hs

putH :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => s -> EffH hs' ()
putH s = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \k hs ->
  let !h' = (lookupPrompt @eff @s @i @hs hs) { hState = s }
      !hs' = replacePrompt @eff @s @i @hs h' hs
  in k () hs'

handleH
  :: s
  -> (forall hs'. ('PROMPT eff s i hs :<< hs') => eff (Eff (EffKs hs')) ~> EffH hs')
  -> EffH ('PROMPT eff s i hs) i
  -> EffH hs i
handleH s f (EffH m) = EffH \k hs0 ->
  let !hs1 = pushPromptWithEvidence s f k hs0
      k' a hs1' = let (h', hs0') = popPrompt hs1' in hCont h' a hs0'
  in m k' hs1


newtype Eff effs a = Eff { unEff :: forall hs. effs ~ EffKs hs => EffH hs a }

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff (fmap f m)
  {-# INLINE fmap #-}
instance Applicative (Eff effs) where
  pure a = Eff (pure a)
  {-# INLINE pure #-}
  Eff f <*> Eff g = Eff (f <*> g)
  {-# INLINE (<*>) #-}
instance Monad (Eff effs) where
  Eff m >>= f = Eff (m >>= unEff . f)
  {-# INLINE (>>=) #-}

run :: Eff '[] a -> a
run (Eff m) = runH m
{-# INLINE run #-}

send :: forall eff effs. (eff :< effs) => eff (Eff effs) ~> Eff effs
send e = Eff $ sendH e
{-# INLINE send #-}


newtype HandlerM eff effs s i effs' a = HandlerM
  { unHandlerM :: forall hs hs'
     . ( 'PROMPT eff s i hs :<< hs'
       , effs ~ EffKs hs
       , effs' ~ EffKs hs'
       )
    => Proxy# hs -> Proxy# hs' -> EffH hs' a
  }

instance Functor (HandlerM eff effs s i effs') where
  fmap f (HandlerM m) = HandlerM \hs hs' -> fmap f (m hs hs')
  {-# INLINE fmap #-}
instance Applicative (HandlerM eff effs s i effs') where
  pure a = HandlerM \_ _ -> pure a
  {-# INLINE pure #-}
  HandlerM f <*> HandlerM g = HandlerM \hs hs' -> f hs hs' <*> g hs hs'
  {-# INLINE (<*>) #-}
instance Monad (HandlerM eff effs s i effs') where
  HandlerM m >>= f = HandlerM \hs hs' -> m hs hs' >>= \a -> unHandlerM (f a) hs hs'
  {-# INLINE (>>=) #-}

bind :: Eff effs' ~> HandlerM eff effs s i effs'
bind (Eff m) = HandlerM \_ _ -> m
{-# INLINE bind #-}

escape :: forall eff effs s i effs'. Eff (eff ': effs) ~> HandlerM eff effs s i effs'
escape (Eff m) = HandlerM \(_ :: Proxy# hs) (_ :: Proxy# hs') -> escapeH @eff @s @i @hs @hs' m
{-# INLINE escape #-}

abort :: forall eff effs s i effs' a. i -> HandlerM eff effs s i effs' a
abort a = HandlerM \(_ :: Proxy# hs) (_ :: Proxy# hs') -> abortH @eff @s @i @hs @hs' a
{-# INLINE abort #-}

getS :: forall eff effs s i effs'. HandlerM eff effs s i effs' s
getS = HandlerM \(_ :: Proxy# hs) (_ :: Proxy# hs') -> getH @eff @s @i @hs @hs'
{-# INLINE getS #-}

putS :: forall eff effs s i effs'. s -> HandlerM eff effs s i effs' ()
putS s = HandlerM \(_ :: Proxy# hs) (_ :: Proxy# hs') -> putH @eff @s @i @hs @hs' s
{-# INLINE putS #-}

handle
  :: forall eff s i effs
   . s
  -> (forall effs'. eff (Eff effs') ~> HandlerM eff effs s i effs')
  -> Eff (eff ': effs) i
  -> Eff effs i
handle s f (Eff m) =
  let m' :: forall hs. (effs ~ EffKs hs) => EffH hs i
      m' =
        let f' :: forall hs'. ('PROMPT eff s i hs :<< hs') => eff (Eff (EffKs hs')) ~> EffH hs'
            f' e = unHandlerM (f e) (proxy# @_ @hs) (proxy# @_ @hs')
        in handleH s f' m
  in Eff m'
{-# INLINE handle #-}
