{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Control.Effect2.Internal where

import Control.Monad
import Control.Natural (type (~>))
import Data.Kind (Constraint, Type)
import Data.Primitive.SmallArray
import GHC.Exts (Any, magicDict, Proxy#, proxy#)
import Unsafe.Coerce (unsafeCoerce)
import Data.Type.Equality hiding (type (==))
import Data.Proxy
-- import Data.Coerce
import Control.Exception (assert)

type EffectK = (Type -> Type) -> Type -> Type

data HandlersK
  -- | @'ROOT' r@
  = ROOT Type
  -- | @'PROMPT' eff s i hs@
  | PROMPT EffectK Type Type HandlersK

type family R hs where
  R ('ROOT r) = r
  R ('PROMPT _ _ _ hs) = R hs

-- | If one 'HandlersK' is contained within the other, their roots must be equal.
rootsEq :: hs :<< hs' => R hs :~: R hs'
rootsEq = unsafeCoerce Refl
{-# INLINE rootsEq #-}

withRootsEq :: forall hs hs' r. hs :<< hs' => (R hs ~ R hs' => r) -> r
withRootsEq a = case rootsEq @hs @hs' of Refl -> a
{-# INLINE withRootsEq #-}

type family EffKs hs where
  EffKs ('ROOT _) = '[]
  EffKs ('PROMPT eff _ _ hs) = eff ': EffKs hs

-- type family IsPseudo (eff :: EffectK) :: Bool where
--   IsPseudo (Handle _ _) = 'True
--   IsPseudo eff = 'False
--
-- -- | The visibility of the 'Privileged' constructor is used as a proof that pseudo-effects can be
-- -- (unsafely!) discharged.
-- newtype Privileged (eff :: EffectK) m a = Privileged (eff m a)
-- type Pseudo eff = (IsPseudo eff ~ 'True, Coercible eff (Privileged eff))
--
-- -- | No pseudo-effects are inhabited, so forcing an effect value is sufficient as a proof that it is
-- -- not a pseudo-effect.
-- prune :: forall eff m a r. eff m a -> (IsPseudo eff ~ 'False => r) -> r
-- prune !_ f = case unsafeCoerce Refl of (Refl :: IsPseudo eff :~: 'False) -> f
-- {-# INLINE prune #-}
--
-- type family Prune (effs :: [EffectK]) :: [EffectK] where
--   Prune (eff ': effs) = PruneIf (IsPseudo eff) eff effs
--   Prune '[] = '[]
-- type family PruneIf c eff effs where
--   PruneIf 'True _ effs = Prune effs
--   PruneIf 'False eff effs = eff ': Prune effs

class KnownLength (xs :: [EffectK]) where
  lengthVal :: Int
instance KnownLength '[] where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance KnownLength xs => KnownLength (x ': xs) where
  lengthVal = lengthVal @xs + 1
  {-# INLINE lengthVal #-}

-- class KnownLength (xs :: [EffectK]) where
--   lengthVal :: Int
-- instance KnownLength '[] where
--   lengthVal = 0
--   {-# INLINE lengthVal #-}
-- instance KnownLength' (IsPseudo x) xs => KnownLength (x ': xs) where
--   lengthVal = lengthVal' @(IsPseudo x) @xs
--   {-# INLINE lengthVal #-}
--
-- class KnownLength' (c :: Bool) (xs :: [EffectK]) where
--   lengthVal' :: Int
-- instance KnownLength xs => KnownLength' 'False xs where
--   lengthVal' = lengthVal @xs
--   {-# INLINE lengthVal' #-}
-- instance KnownLength xs => KnownLength' 'True xs where
--   lengthVal' = lengthVal @xs + 1
--   {-# INLINE lengthVal' #-}

class KnownLengthH (hs :: HandlersK) where
  lengthValH :: Int
instance KnownLengthH ('ROOT r) where
  lengthValH = 0
  {-# INLINE lengthValH #-}
instance KnownLengthH hs => KnownLengthH ('PROMPT eff s i hs) where
  lengthValH = lengthValH @hs + 1
  {-# INLINE lengthValH #-}

class KnownIndex (x :: EffectK) (xs :: [EffectK]) where
  indexVal :: Int
-- instance KnownIndex' (IsPseudo x) x xs => KnownIndex x xs where
--   indexVal = indexVal' @(IsPseudo x) @x @xs
--   {-# INLINE indexVal #-}
instance {-# OVERLAPPING #-} KnownLength xs => KnownIndex x (x ': xs) where
  indexVal = lengthVal @xs
  {-# INLINE indexVal #-}
instance KnownIndex x xs => KnownIndex x (y ': xs) where
  indexVal = indexVal @x @xs
  {-# INLINE indexVal #-}

-- class KnownIndex' (c :: Bool) (x :: EffectK) (xs :: [EffectK]) where
--   indexVal' :: Int
-- instance KnownIndex' 'True x xs where
--   indexVal' = error "indexVal: internal error: tried to use index of pseudo-effect"
--   {-# INLINE indexVal' #-}
-- instance {-# OVERLAPPING #-} KnownLength xs => KnownIndex' 'False x (x ': xs) where
--   indexVal' = lengthVal @xs
--   {-# INLINE indexVal' #-}
-- instance KnownIndex x xs => KnownIndex' 'False x (y ': xs) where
--   indexVal' = indexVal @x @xs
--   {-# INLINE indexVal' #-}

class KnownIndexH (hs :: (HandlersK, HandlersK)) where
  indexValH :: Int
instance KnownIndexH' (as == bs) as bs => KnownIndexH '(as, bs) where
  indexValH = indexValH' @(as == bs) @as @bs

type family a == b where
  a == a = 'True
  a == b = 'False

class KnownIndexH' (c :: Bool) (as :: HandlersK) (bs :: HandlersK) where
  indexValH' :: Int
instance KnownLengthH hs => KnownIndexH' 'True hs hs where
  indexValH' = lengthValH @hs - 1
  {-# INLINE indexValH' #-}
instance KnownIndexH '(as, bs) => KnownIndexH' 'False as ('PROMPT eff s i bs) where
  indexValH' = indexValH @'(as, bs)
  {-# INLINE indexValH' #-}

-- type KnownIndex' eff effs = KnownIndexIf (IsPseudo eff) eff effs
-- type family KnownIndexIf c eff effs where
--   KnownIndexIf 'False eff effs = KnownIndex eff effs
--   KnownIndexIf 'True eff _ = Pseudo eff

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

-- data WithLength a r = WithLength (KnownLength a => Proxy a -> r)
-- withLength :: forall a r. Int -> (KnownLength a => Proxy a -> r) -> r
-- withLength n f = magicDict (WithLength f) n (Proxy @a)
-- {-# INLINE withLength #-}

data WithLengthH a r = WithLengthH (KnownLengthH a => Proxy a -> r)
withLengthH :: forall a r. Int -> (KnownLengthH a => Proxy a -> r) -> r
withLengthH n f = magicDict (WithLengthH f) n (Proxy @a)
{-# INLINE withLengthH #-}

data WithIndexH a r = WithIndexH (KnownIndexH a => Proxy a -> r)
withIndexH :: forall a r. Int -> (KnownIndexH a => Proxy a -> r) -> r
withIndexH n f = magicDict (WithIndexH f) n (Proxy @a)
{-# INLINE withIndexH #-}

withLengthFromIndexH :: forall hs hs' r. KnownIndexH '(hs, hs') => (KnownLengthH hs => r) -> r
withLengthFromIndexH x = withLengthH @hs (indexValH @'(hs, hs') + 1) \_ -> x
{-# INLINE withLengthFromIndexH #-}

-- withSameLength :: forall effs hs r. (effs ~ EffKs hs, KnownLengthH hs) => (KnownLength effs => r) -> r
-- withSameLength f = withLength @effs (lengthValH @hs) \_ -> f
-- {-# INLINE withSameLength #-}

data Handler eff s i hs = Handler
  { hState :: s
  , hSend :: !(forall a hs'. ('PROMPT eff s i hs :<<! hs') => eff (Eff (EffKs hs')) a -> EffH hs' a)
  , hCont :: !(i -> Handlers ('PROMPT eff s i hs) -> R hs)
  -- ^ The continuation of this prompt. When a prompt is first installed via 'handleH', 'hCont' is
  -- initialized to a continuation that pops the prompt, then returns to the parent metacontinuation
  -- frame. 'hCont' can be further extended by uses of 'shiftH'; each use extends the continuation
  -- from the “outside in,” so earlier uses of 'shiftH' wrap later uses.
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
  -> (i -> Handlers ('PROMPT eff s i hs) -> R hs)
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

popPrompt :: Handlers ('PROMPT eff s i hs) -> Handlers hs
popPrompt (Handlers hs) = Handlers $ cloneSmallArray hs 0 (sizeofSmallArray hs - 1)
{-# INLINE popPrompt #-}

lookupPrompt :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => Handlers hs' -> Handler eff s i hs
lookupPrompt (Handlers hs) =
  let idx = indexValH @'( 'PROMPT eff s i hs, hs')
  in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    unsafeCoerce $ indexSmallArray hs idx
{-# INLINE lookupPrompt #-}

withPromptAfter
  :: forall hs hs' r. (hs :<< hs')
  => Handlers hs'
  -> (forall eff s i. Handler eff s i hs -> r)
  -- ^ called when there is a prompt after the given index
  -> ((hs ~ hs') => r)
  -- ^ called when the given index refers to the last prompt
  -> r
withPromptAfter (Handlers hs) f g =
  let len = lengthValH @hs'
      idx = indexValH @'(hs, hs')
  in assert (idx >= 0) $ assert (len > 0) $ assert (idx < len) $ assert (len == sizeofSmallArray hs) if
    | idx == len - 1 -> case unsafeCoerce Refl of (Refl :: hs :~: hs') -> g
    | otherwise -> f $! unsafeCoerce (indexSmallArray hs (idx + 1))
{-# INLINE withPromptAfter #-}

replacePrompt
  :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs')
  => Handler eff s i hs -> Handlers hs' -> Handlers hs'
replacePrompt h (Handlers hs) = Handlers $ runSmallArray do
  hs' <- thawSmallArray hs 0 (sizeofSmallArray hs)
  let idx = indexValH @'( 'PROMPT eff s i hs, hs')
  writeSmallArray hs' idx (unsafeCoerce h)
  pure hs'

takePrompts :: forall hs hs'. (hs :<< hs') => Handlers hs' -> Handlers hs
takePrompts (Handlers hs) =
  let idx = indexValH @'(hs, hs')
  in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    Handlers $ cloneSmallArray hs 0 (idx + 1)
{-# INLINE takePrompts #-}

replacePrompts :: forall hs hs'. (hs :<< hs') => Handlers hs -> Handlers hs' -> Handlers hs'
replacePrompts (Handlers hs) (Handlers hs') = Handlers $ runSmallArray do
  hs'' <- thawSmallArray hs' 0 (sizeofSmallArray hs')
  let idx = indexValH @'(hs, hs')
  assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    copySmallArray hs'' 0 hs 0 (idx + 1)
  pure hs''

takePromptsUpTo :: forall eff s i hs hs'. ('PROMPT eff s i hs :<< hs') => Handlers hs' -> Handlers hs
takePromptsUpTo (Handlers hs) =
  let idx = indexValH @'( 'PROMPT eff s i hs, hs')
  in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    Handlers $ cloneSmallArray hs 0 idx
{-# INLINE takePromptsUpTo #-}

withHandler
  :: forall eff hs' r. (eff :< EffKs hs')
  => Handlers hs'
  -> (forall s i hs. ('PROMPT eff s i hs :<<! hs') => Handler eff s i hs -> r)
  -> r
withHandler (Handlers hs) f =
  let idx = indexVal @eff @(EffKs hs') in
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

liftH :: forall hs hs'. (hs :<< hs') => EffH hs ~> EffH hs'
liftH (EffH m) = withRootsEq @hs @hs' $ EffH \k hs ->
  m (\a hs' -> k a $! replacePrompts hs' hs) $! takePrompts hs
{-# INLINE liftH #-}

sendH :: forall eff hs. (eff :< EffKs hs) => eff (Eff (EffKs hs)) ~> EffH hs
sendH e = EffH \k hs -> withHandler @eff @hs hs \h -> unEffH (hSend h e) k hs
{-# INLINE sendH #-}

abortH :: forall eff s i hs hs' a. ('PROMPT eff s i hs :<< hs') => i -> EffH hs' a
abortH a = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \_ hs ->
  let h = lookupPrompt @eff @s @i @hs hs
  in hCont h a $! takePrompts @('PROMPT eff s i hs) hs

shiftH
  :: forall eff s i hs hs' a. ('PROMPT eff s i hs :<< hs')
  => ((a -> EffH ('PROMPT eff s i hs) i) -> EffH ('PROMPT eff s i hs) i)
  -> EffH hs' a
shiftH f = withRootsEq @('PROMPT eff s i hs) @hs' $ EffH \kn hs ->
  let !idx = indexValH @'( 'PROMPT eff s i hs, hs')

      m :: (i -> Handlers ('PROMPT eff s i hs) -> R hs) -> Handlers ('PROMPT eff s i hs) -> R hs
      m = unEffH $ f \a -> EffH \k1 (Handlers hs1) ->
        assert (idx == sizeofSmallArray hs1 - 1) $
          kn a $! Handlers $ runSmallArray do
            -- copy the original set of prompts for a fresh copy of all local state
            hs' <- thawSmallArray (unHandlers hs) 0 (sizeofSmallArray $ unHandlers hs)
            -- replace more global prompts with their updated versions
            copySmallArray hs' 0 hs1 0 idx
            -- extend the metacontinuation of the prompt we’re capturing up to
            let !h' = (unsafeCoerce $ indexSmallArray hs1 idx) { hCont = k1 }
            writeSmallArray hs' idx (unsafeCoerce h')
            pure hs'

      !hs0 = takePrompts @('PROMPT eff s i hs) hs
      !k0 = hCont (peekPrompt hs0)
  in m k0 hs0

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
  :: forall eff s i hs
   . s
  -> (forall hs'. ('PROMPT eff s i hs :<< hs') => eff (Eff (EffKs hs')) ~> EffH hs')
  -> EffH ('PROMPT eff s i hs) i
  -> EffH hs i
handleH s f (EffH m) = EffH \k0 hs ->
  let k1 a hs' = k0 a $! popPrompt hs'
      kn a hs' = hCont (peekPrompt hs') a hs'
  in m kn $! pushPromptWithEvidence s f k1 hs


newtype Eff effs a = Eff { unEff :: forall hs. effs ~ EffKs hs => EffH hs a }

mkEff :: forall effs a. (forall hs. effs ~ EffKs hs => Proxy# hs -> EffH hs a) -> Eff effs a
mkEff f = Eff (f (proxy# @_ @hs) :: forall hs. effs ~ EffKs hs => EffH hs a)
{-# INLINE mkEff #-}

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


newtype Handle k effs a = Handle { unHandle :: forall hs. (effs ~ EffKs hs, k :<< hs) => EffH hs a }

mkHandle :: forall k effs a. (forall hs. (effs ~ EffKs hs, k :<< hs) => Proxy# hs -> EffH hs a) -> Handle k effs a
mkHandle f = Handle (f (proxy# @_ @hs) :: forall hs. (effs ~ EffKs hs, k :<< hs) => EffH hs a)

instance Functor (Handle k effs) where
  fmap f (Handle m) = Handle (fmap f m)
  {-# INLINE fmap #-}
instance Applicative (Handle k effs) where
  pure a = Handle (pure a)
  {-# INLINE pure #-}
  Handle f <*> Handle g = Handle (f <*> g)
  {-# INLINE (<*>) #-}
instance Monad (Handle k effs) where
  Handle m >>= f = Handle (m >>= unHandle . f)
  {-# INLINE (>>=) #-}

class Handling eff s i effs k | k -> eff s i effs where
  withHandling' :: (forall hs. (k ~ 'PROMPT eff s i hs, effs ~ EffKs hs) => Proxy# hs -> r) -> r
instance (k ~ 'PROMPT eff s i hs, effs ~ EffKs hs) => Handling eff s i effs k where
  withHandling' f = f (proxy# @_ @hs)
  {-# INLINE withHandling' #-}

withHandling
  :: forall k eff s i effs r. Handling eff s i effs k
  => (forall hs. (k ~ 'PROMPT eff s i hs, effs ~ EffKs hs) => Proxy# hs -> r) -> r
withHandling = withHandling' @eff @s @i @effs @k
{-# INLINE withHandling #-}

bind :: Eff effs ~> Handle k effs
bind (Eff m) = Handle m
{-# INLINE bind #-}

escape :: forall eff s i effs k effs'. Handling eff s i effs k => Eff (eff ': effs) ~> Handle k effs'
escape (Eff m) = withHandling @k \(_ :: Proxy# hs) -> Handle $ liftH @('PROMPT eff s i hs) m
{-# INLINE escape #-}

abort :: forall eff s i effs k effs' a. Handling eff s i effs k => i -> Handle k effs' a
abort a = withHandling @k \(_ :: Proxy# hs) -> Handle $ abortH @eff @s @i @hs a
{-# INLINE abort #-}

getS :: forall eff s i effs k effs'. Handling eff s i effs k => Handle k effs' s
getS = withHandling @k \(_ :: Proxy# hs) -> Handle $ getH @eff @s @i @hs
{-# INLINE getS #-}

putS :: forall eff s i effs k effs'. Handling eff s i effs k => s -> Handle k effs' ()
putS s = withHandling @k \(_ :: Proxy# hs) -> Handle $ putH @eff @s @i @hs s
{-# INLINE putS #-}

shift
  :: forall eff s i effs k effs' a. Handling eff s i effs k
  => ((a -> Handle k (eff ': effs) i) -> Handle k (eff ': effs) i)
  -> Handle k effs' a
shift f = withHandling @k \(_ :: Proxy# hs) -> mkHandle \(_ :: Proxy# hs') ->
  withLengthFromIndexH @k @hs' $ shiftH @eff @s @i @hs \k ->
    unHandle $ f \a -> Handle $ liftH $ k a
{-# INLINE shift #-}

handle
  :: forall eff s i effs
   . s
  -> (forall k effs'. Handling eff s i effs k => eff (Eff effs') ~> Handle k effs')
  -> Eff (eff ': effs) i
  -> Eff effs i
handle s f (Eff m) = mkEff \(_ :: Proxy# hs) ->
  handleH s (\e -> unHandle @('PROMPT eff s i hs) $ f e) m
{-# INLINE handle #-}
