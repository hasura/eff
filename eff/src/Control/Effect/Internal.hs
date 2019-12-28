{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal where

import Control.Exception (assert)
import Control.Monad
import Control.Natural (type (~>))
import Data.Kind (Constraint, Type)
import Data.Primitive.SmallArray
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (Any, Proxy#, proxy#)
import GHC.TypeLits (ErrorMessage(..), TypeError)
import Unsafe.Coerce (unsafeCoerce)

with :: a :~: b -> (a ~ b => r) -> r
with Refl x = x
{-# INLINE with #-}

axiom :: forall a b. a :~: b
axiom = unsafeCoerce Refl
{-# INLINE axiom #-}

axiomC :: forall a. a :~: (() :: Constraint)
axiomC = axiom
{-# INLINE axiomC #-}

type Effect = (Type -> Type) -> Type -> Type

data Cell (s :: Type) :: Effect
data Handle (eff :: Effect) (i :: Type) (effs :: [Effect]) :: Effect

type family Handles eff :: Constraint where
  Handles (Cell s) = NoHandling Cell (Cell s)
  Handles (Handle eff i effs) = NoHandling Handle (Handle eff i effs)
  Handles _ = ()
type family NoHandling c eff where
  NoHandling c eff = TypeError
    ( 'Text "no instance for ‘" ':<>: 'ShowType eff ':<>: 'Text "’;"
    ':$$: 'Text "  " ':<>: 'ShowType c ':<>: 'Text " is a primitive effect and cannot be handled" )

-- | GHC doesn’t provide a very easy way to propagate negative information, so it’s hard to connect
-- the 'Handles' constraint to its implication for ':->'. This casts away the constraint manually.
withHandles
  :: forall eff i effs hs r. (Handles eff, effs :-> hs)
  => ((eff ': effs) :-> 'PROMPT eff i hs => r) -> r
withHandles = with $ axiomC @((eff ': effs) :-> 'PROMPT eff i hs)
{-# INLINE withHandles #-}

data HandlersK
  = ROOT Type
  | CELL Type HandlersK
  | PROMPT Effect Type HandlersK

type family R hs where
  R ('ROOT r) = r
  R ('CELL _ hs) = R hs
  R ('PROMPT _ _ hs) = R hs

-- | If one 'HandlersK' is contained within the other, their roots must be equal.
rootsEq :: hs :<< hs' => R hs :~: R hs'
rootsEq = axiom
{-# INLINE rootsEq #-}

withRootsEq :: forall hs hs' r. hs :<< hs' => (R hs ~ R hs' => r) -> r
withRootsEq = with (rootsEq @hs @hs')
{-# INLINE withRootsEq #-}

type family EffKs hs where
  EffKs ('ROOT _) = '[]
  EffKs ('CELL s hs) = (Cell s ': EffKs hs)
  EffKs ('PROMPT eff _ hs) = eff ': EffKs hs

type family effs :-> hs :: Constraint where
  '[] :-> 'ROOT _ = ()
  (Cell s ': effs) :-> 'CELL s' hs = (s ~ s', effs :-> hs)
  (Handle eff i effs ': effs') :-> 'PROMPT eff' i' hs = (Handles eff, eff ~ eff', effs ~ effs', i ~ i', effs :-> hs)
  (eff ': effs) :-> 'PROMPT eff' _ hs = (eff ~ eff', effs :-> hs)

-- GHC sadly doesn’t automatically infer superclasses for closed type families returning
-- constraints, so the following axioms are sometimes necessary to get reduction of (:->) to move
-- forward.

decompCell
  :: forall s effs hs r. (Cell s ': effs) :-> hs
  => (forall hs'. hs ~ 'CELL s hs' => Proxy# hs' -> r) -> r
decompCell f = with (axiom @hs @('CELL s hs')) (f (proxy# @_ @hs')) :: forall (hs' :: HandlersK). r
{-# INLINE decompCell #-}

decompHandle
  :: forall eff i effs effs' hs r. (Handle eff i effs ': effs') :-> hs
  => (forall hs'. hs ~ 'PROMPT eff i hs' => Proxy# hs' -> r) -> r
decompHandle f = with (axiom @hs @('PROMPT eff i hs')) (f (proxy# @_ @hs')) :: forall (hs' :: HandlersK). r
{-# INLINE decompHandle #-}

class KnownLength (a :: k) where
  lengthVal :: Int
instance KnownLength '[] where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance KnownLength xs => KnownLength (x ': xs) where
  lengthVal = lengthVal @_ @xs + 1
  {-# INLINE lengthVal #-}

instance KnownLength ('ROOT r) where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance KnownLength hs => KnownLength ('PROMPT eff i hs) where
  lengthVal = lengthVal @_ @hs + 1
  {-# INLINE lengthVal #-}

class KnownIndex (x :: Effect) (xs :: [Effect]) where
  indexVal :: Int
instance {-# OVERLAPPING #-} KnownLength xs => KnownIndex x (x ': xs) where
  indexVal = lengthVal @_ @xs
  {-# INLINE indexVal #-}
instance KnownIndex x xs => KnownIndex x (y ': xs) where
  indexVal = indexVal @x @xs
  {-# INLINE indexVal #-}

class KnownIndexH as bs where
  indexValH :: Int
instance KnownIndexH' (as == bs) as bs => KnownIndexH as bs where
  indexValH = indexValH' @_ @(as == bs) @as @bs

type family a == b where
  a == a = 'True
  a == b = 'False

class KnownIndexH' (c :: Bool) (as :: k) (bs :: k) where
  indexValH' :: Int
instance KnownLength as => KnownIndexH' 'True as as where
  indexValH' = lengthVal @_ @as - 1
  {-# INLINE indexValH' #-}
instance KnownIndexH as bs => KnownIndexH' 'False as (b ': bs) where
  indexValH' = indexValH @as @bs
  {-# INLINE indexValH' #-}
instance KnownIndexH as bs => KnownIndexH' 'False as ('PROMPT eff i bs) where
  indexValH' = indexValH @as @bs
  {-# INLINE indexValH' #-}

class (KnownIndex a b, KnownLength b) => a :< b
instance (KnownIndex a b, KnownLength b) => a :< b

class (KnownIndexH a b, KnownLength b) => a :<< b
instance (KnownIndexH a b, KnownLength b) => a :<< b

-- -- | Like ':<<', but only at the type level; the evidence will be erased at runtime. This is
-- -- slightly more efficient, since it doesn’t have to be passed around, but of course it means the
-- -- index value cannot actually be accessed.
-- type family a :<<! b :: Constraint where
--   a :<<! a = ()
--   a :<<! 'PROMPT _ _ b = a :<<! b

newtype WithLength a r = WithLength (KnownLength a => r)
withLength :: forall a r. Int -> (KnownLength a => r) -> r
withLength n x = unsafeCoerce (WithLength @a x) n
{-# INLINE withLength #-}

newtype WithIndex a b r = WithIndex (KnownIndex a b => r)
withIndex :: forall a b r. Int -> (KnownIndex a b => r) -> r
withIndex n x = unsafeCoerce (WithIndex @a @b x) n
{-# INLINE withIndex #-}

newtype WithIndexH a b r = WithIndexH (KnownIndexH a b => r)
withIndexH :: forall a b r. Int -> (KnownIndexH a b => r) -> r
withIndexH n x = unsafeCoerce (WithIndexH @a @b x) n
{-# INLINE withIndexH #-}

withLengthFromIndexH :: forall hs hs' r. KnownIndexH hs hs' => (KnownLength hs => r) -> r
withLengthFromIndexH = withLength @hs (indexValH @hs @hs' + 1)
{-# INLINE withLengthFromIndexH #-}

-- discardEvidenceH :: forall a b r. a :<< b => (a :<<! b => r) -> r
-- discardEvidenceH x = case unsafeCoerce Refl of (Refl :: (a :<<! b) :~: (() :: Constraint)) -> x
-- {-# INLINE discardEvidenceH #-}

withSubFrames
  :: forall effs effs' fs' r. (effs :<< effs', effs' :-> fs')
  => (forall fs. (fs :<< fs', effs :-> fs, R fs ~ R fs') => Proxy# fs -> r) -> r
withSubFrames f =
  ( withIndexH @fs @fs' (indexValH @effs @effs')
  $ withLength @fs' (lengthVal @_ @effs')
  $ withRootsEq @fs @fs'
  $ with (axiomC @(effs :-> fs))
  $ f (proxy# @_ @fs)
  ) :: forall (fs :: HandlersK). r
{-# INLINE withSubFrames #-}

withHandleIndex
  :: forall eff i effs effs' hs hs' r. (effs :-> hs, effs' :-> hs', 'PROMPT eff i hs :<< hs')
  => (Handle eff i effs :< effs' => r) -> r
withHandleIndex x =
  withLength @effs' (lengthVal @_ @hs') $
  withIndex @(Handle eff i effs) @effs' (indexValH @('PROMPT eff i hs) @hs') x
{-# INLINE withHandleIndex #-}

withEffectFrame
  :: forall eff effs' hs' r. (effs' :-> hs', eff :< effs')
  => (forall effs hs. ((eff ': effs) :-> hs, hs :<< hs', R hs ~ R hs') => Proxy# effs -> Proxy# hs -> r) -> r
withEffectFrame f =
  ( withLength @hs' (lengthVal @_ @effs')
  $ withIndexH @hs @hs' (indexVal @eff @effs')
  $ withRootsEq @hs @hs'
  $ with (axiomC @((eff ': effs) :-> hs))
  $ f (proxy# @_ @effs) (proxy# @_ @hs)
  ) :: forall (effs :: [Effect]) (hs :: HandlersK). r
{-# INLINE withEffectFrame #-}

type family Frame fs where
  Frame ('CELL s _) = s
  Frame ('PROMPT eff i hs) = Handler eff i hs

data Handler eff i hs = Handler
  { hSend :: forall effs' hs'. (effs' :-> hs', 'PROMPT eff i hs :<< hs')
          => Proxy# hs' -> eff (Eff effs') ~> Eff effs'
  , hCont :: i -> Handlers ('PROMPT eff i hs) -> R hs
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

pushFrame :: forall f fs. Frame (f fs) -> Handlers fs -> Handlers (f fs)
pushFrame h (Handlers hs) = Handlers $ runSmallArray do
  let len = sizeofSmallArray hs
  hs' <- newSmallArray (len + 1) (error "pushFrame: value left uninitialized")
  copySmallArray hs' 0 hs 0 len
  writeSmallArray hs' len (unsafeCoerce h)
  pure hs'

peekFrame :: Handlers fs -> Frame fs
peekFrame (Handlers hs) = unsafeCoerce $ indexSmallArray hs (sizeofSmallArray hs - 1)
{-# INLINE peekFrame #-}

popFrame :: forall f fs. Handlers (f fs) -> Handlers fs
popFrame (Handlers fs) = Handlers $ cloneSmallArray fs 0 (sizeofSmallArray fs - 1)
{-# INLINE popFrame #-}

lookupFrame :: forall fs fs'. fs :<< fs' => Handlers fs' -> Frame fs
lookupFrame (Handlers hs) =
  let idx = indexValH @fs @fs'
  in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    unsafeCoerce $ indexSmallArray hs idx
{-# INLINE lookupFrame #-}

-- withPromptAfter
--   :: forall hs hs' r. (hs :<< hs')
--   => Handlers hs'
--   -> (forall eff i. Handler eff i hs -> r)
--   -- ^ called when there is a prompt after the given index
--   -> ((hs ~ hs') => r)
--   -- ^ called when the given index refers to the last prompt
--   -> r
-- withPromptAfter (Handlers hs) f g =
--   let len = lengthValH @hs'
--       idx = indexValH @'(hs, hs')
--   in assert (idx >= 0) $ assert (len > 0) $ assert (idx < len) $ assert (len == sizeofSmallArray hs) if
--     | idx == len - 1 -> case unsafeCoerce Refl of (Refl :: hs :~: hs') -> g
--     | otherwise -> f $! unsafeCoerce (indexSmallArray hs (idx + 1))
-- {-# INLINE withPromptAfter #-}

replaceFrame :: forall fs fs'. fs :<< fs' => Frame fs -> Handlers fs' -> Handlers fs'
replaceFrame h (Handlers hs) = Handlers $ runSmallArray do
  hs' <- thawSmallArray hs 0 (sizeofSmallArray hs)
  let idx = indexValH @fs @fs'
  writeSmallArray hs' idx (unsafeCoerce h)
  pure hs'

takeFrames :: forall hs hs'. hs :<< hs' => Handlers hs' -> Handlers hs
takeFrames (Handlers hs) =
  let idx = indexValH @hs @hs'
  in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    Handlers $ cloneSmallArray hs 0 (idx + 1)
{-# INLINE takeFrames #-}

replaceFrames :: forall hs hs'. hs :<< hs' => Handlers hs -> Handlers hs' -> Handlers hs'
replaceFrames (Handlers hs) (Handlers hs') = Handlers $ runSmallArray do
  hs'' <- thawSmallArray hs' 0 (sizeofSmallArray hs')
  let idx = indexValH @hs @hs'
  assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
    copySmallArray hs'' 0 hs 0 (idx + 1)
  pure hs''

-- takeFramesUpTo :: forall f fs fs'. f fs :<< fs' => Handlers fs' -> Handlers fs
-- takeFramesUpTo (Handlers hs) =
--   let idx = indexValH @_ @'(f fs, fs')
--   in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
--     Handlers $ cloneSmallArray hs 0 idx
-- {-# INLINE takeFramesUpTo #-}

withHandler
  :: forall eff effs hs' r. (eff :< effs, effs :-> hs')
  => Handlers hs'
  -> (forall i hs. 'PROMPT eff i hs :<< hs' => Proxy# i -> Proxy# hs -> Handler eff i hs -> r)
  -> r
withHandler (Handlers hs) f =
  let idx = indexVal @eff @effs in
  case unsafeCoerce $ indexSmallArray hs idx of
    (h :: Handler eff i hs) ->
      withIndexH @('PROMPT eff i hs) @hs' idx $
      withLength @hs' (lengthVal @_ @effs) $
        f (proxy# @_ @i) (proxy# @_ @hs) h
{-# INLINE withHandler #-}


newtype Eff effs a = Eff { unEff :: forall hs. effs :-> hs
                                 => (a -> Handlers hs -> R hs)
                                 -> Handlers hs -> R hs }

mkEff :: forall effs a. (forall hs. effs :-> hs => Proxy# hs -> (a -> Handlers hs -> R hs) -> Handlers hs -> R hs) -> Eff effs a
mkEff f = Eff (f (proxy# @_ @hs) :: forall hs. effs :-> hs => (a -> Handlers hs -> R hs) -> Handlers hs -> R hs)
{-# INLINE mkEff #-}

run :: Eff '[] a -> a
run (Eff m) = m (\v _ -> v) root
{-# INLINE run #-}

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff \k -> m \a -> k (f a)
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff ($ a)
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \k -> m \a -> unEff (f a) k
  {-# INLINE (>>=) #-}

lift :: forall effs effs'. effs :<< effs' => Eff effs ~> Eff effs'
lift (Eff m) = mkEff \(_ :: Proxy# hs') k hs ->
  withSubFrames @effs @effs' @hs' \(_ :: Proxy# hs) ->
    m @hs (\a hs' -> k a $! replaceFrames hs' hs) $! takeFrames hs

liftH :: forall eff effs effs' i. Handle eff i effs :< effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = mkEff \(_ :: Proxy# hs') k hs ->
  withEffectFrame @(Handle eff i effs) @effs' @hs' \(_ :: Proxy# effs'') (_ :: Proxy# hs) ->
  decompHandle @eff @i @effs @effs'' @hs \(_ :: Proxy# hs'') ->
  withHandles @eff @i @effs @hs'' $
    m @hs (\a hs' -> k a $! replaceFrames hs' hs) $! takeFrames hs

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = mkEff \(p :: Proxy# hs') k hs ->
  withHandler @eff @effs @hs' hs \_ _ h ->
    unEff (hSend h p e) k hs

abort :: forall eff i a effs effs'. Handle eff i effs :< effs' => i -> Eff effs' a
abort a = mkEff \(_ :: Proxy# hs') _ hs ->
  withEffectFrame @(Handle eff i effs) @effs' @hs' \(_ :: Proxy# effs'') (_ :: Proxy# hs) ->
  decompHandle @eff @i @effs @effs'' @hs \_ ->
    hCont (lookupFrame @hs hs) a $! takeFrames @hs hs

-- shiftH
--   :: forall eff i hs hs' a. ('PROMPT eff i hs :<< hs')
--   => ((a -> EffH ('PROMPT eff i hs) i) -> EffH ('PROMPT eff i hs) i)
--   -> EffH hs' a
-- shiftH f = withRootsEq @('PROMPT eff i hs) @hs' $ EffH \kn hs ->
--   let !idx = indexValH @'( 'PROMPT eff i hs, hs')
--
--       m :: (i -> Handlers ('PROMPT eff i hs) -> R hs) -> Handlers ('PROMPT eff i hs) -> R hs
--       m = unEffH $ f \a -> EffH \k1 (Handlers hs1) ->
--         assert (idx == sizeofSmallArray hs1 - 1) $
--           kn a $! Handlers $ runSmallArray do
--             -- copy the original set of prompts for a fresh copy of all local state
--             hs' <- thawSmallArray (unHandlers hs) 0 (sizeofSmallArray $ unHandlers hs)
--             -- replace more global prompts with their updated versions
--             copySmallArray hs' 0 hs1 0 idx
--             -- extend the metacontinuation of the prompt we’re capturing up to
--             let !h' = (unsafeCoerce $ indexSmallArray hs1 idx) { hCont = k1 }
--             writeSmallArray hs' idx (unsafeCoerce h')
--             pure hs'
--
--       !hs0 = takeFrames @('PROMPT eff i hs) hs
--       !k0 = hCont (peekFrame hs0)
--   in m k0 hs0

getC :: forall s effs. Cell s :< effs => Eff effs s
getC = mkEff \(_ :: Proxy# fs) k fs ->
  withEffectFrame @(Cell s) @effs @fs \(_ :: Proxy# effs') (_ :: Proxy# fs') ->
  decompCell @s @effs' @fs' \_ ->
    (k $! lookupFrame @fs' fs) fs

putC :: forall s effs. Cell s :< effs => s -> Eff effs ()
putC s = mkEff \(_ :: Proxy# fs) k fs ->
  withEffectFrame @(Cell s) @effs @fs \(_ :: Proxy# effs') (_ :: Proxy# fs') ->
  decompCell @s @effs' @fs' \_ ->
    k () $! replaceFrame @fs' s fs

runCell :: forall s effs. s -> Eff (Cell s ': effs) ~> Eff effs
runCell s (Eff m) = Eff \k hs -> m (\a hs' -> k a $! popFrame hs') $! pushFrame @('CELL s) s hs

handle
  :: forall eff a effs. Handles eff
  => (forall effs'. Handle eff a effs :< effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m) = mkEff \(_ :: Proxy# hs) k0 hs -> withHandles @eff @a @effs @hs
  let k1 a hs' = k0 a $! popFrame hs'
      kn a hs' = hCont (peekFrame hs') a hs'
      f' :: forall effs' hs'. (effs' :-> hs', 'PROMPT eff a hs :<< hs')
         => Proxy# hs' -> eff (Eff effs') ~> Eff effs'
      f' _ e = withHandleIndex @eff @a @effs @effs' @hs @hs' $ f e
  in m kn $! pushFrame (Handler @eff f' k1) hs
