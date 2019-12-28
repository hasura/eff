{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Effect.Internal where

import Control.Exception (assert)
import Control.Monad
import Control.Monad.ST
import Control.Natural (type (~>))
import Data.Kind (Constraint, Type)
import Data.Primitive.ByteArray
import Data.Primitive.SmallArray
import Data.Primitive.MachDeps (sIZEOF_INT)
import Data.Type.Equality ((:~:)(..))
import GHC.Exts (Any, Int#, Proxy#, proxy#)
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

assertM :: Applicative m => Bool -> m ()
assertM b = assert b $ pure ()
{-# INLINE assertM #-}

type Effect = (Type -> Type) -> Type -> Type

data Cell (s :: Type) :: Effect

type family Handles eff :: Constraint where
  Handles (Cell s) = NoHandling Cell (Cell s)
  Handles _ = ()
type family NoHandling c eff where
  NoHandling c eff = TypeError
    ( 'Text "no instance for ‘" ':<>: 'ShowType eff ':<>: 'Text "’;"
    ':$$: 'Text "  " ':<>: 'ShowType c ':<>: 'Text " is a primitive effect and cannot be handled" )

data FramesK
  = ROOT Type
  | CELL Type FramesK
  | PROMPT Effect Type FramesK

type family R hs where
  R ('ROOT r) = r
  R ('CELL _ hs) = R hs
  R ('PROMPT _ _ hs) = R hs

-- -- | If one 'FramesK' is contained within the other, their roots must be equal.
-- rootsEq :: hs :<< hs' => R hs :~: R hs'
-- rootsEq = axiom
-- {-# INLINE rootsEq #-}

-- withRootsEq :: forall hs hs' r. hs :<< hs' => (R hs ~ R hs' => r) -> r
-- withRootsEq = with (rootsEq @hs @hs')
-- {-# INLINE withRootsEq #-}

type family EffKs hs where
  EffKs ('ROOT _) = '[]
  EffKs ('CELL s hs) = (Cell s ': EffKs hs)
  EffKs ('PROMPT eff _ hs) = eff ': EffKs hs

-- class KnownLength (a :: k) where
--   lengthVal :: Int
-- instance KnownLength '[] where
--   lengthVal = 0
--   {-# INLINE lengthVal #-}
-- instance KnownLength xs => KnownLength (x ': xs) where
--   lengthVal = lengthVal @_ @xs + 1
--   {-# INLINE lengthVal #-}

-- instance KnownLength ('ROOT r) where
--   lengthVal = 0
--   {-# INLINE lengthVal #-}
-- instance KnownLength hs => KnownLength ('PROMPT eff i hs) where
--   lengthVal = lengthVal @_ @hs + 1
--   {-# INLINE lengthVal #-}

type family a == b where
  a == a = 'True
  a == b = 'False

class (eff :: Effect) :< (effs :: [Effect]) where
  indexVal :: Int
instance {-# OVERLAPPING #-} eff :< (eff ': effs) where
  indexVal = 0
  {-# INLINE indexVal #-}
instance eff :< effs => eff :< (eff' ': effs) where
  indexVal = indexVal @eff @effs + 1
  {-# INLINE indexVal #-}

class (effs :: [Effect]) :<< (effs' :: [Effect]) where
  subIndexVal :: Int
instance SubIndex (effs == effs') effs effs' => effs :<< effs' where
  subIndexVal = subIndexVal' @(effs == effs') @effs @effs'
  {-# INLINE subIndexVal #-}

class SubIndex (c :: Bool) (effs :: [Effect]) (effs' :: [Effect]) where
  subIndexVal' :: Int
instance SubIndex 'True effs effs where
  subIndexVal' = 0
  {-# INLINE subIndexVal' #-}
instance effs :<< effs' => SubIndex 'False effs (eff ': effs') where
  subIndexVal' = subIndexVal @effs @effs' + 1
  {-# INLINE subIndexVal' #-}

-- class KnownIndexH as bs where
--   indexValH :: Int

-- class KnownIndexH as bs where
--   indexValH :: Int
-- instance KnownIndexH' (as == bs) as bs => KnownIndexH as bs where
--   indexValH = indexValH' @_ @(as == bs) @as @bs
--
-- type family a == b where
--   a == a = 'True
--   a == b = 'False
--
-- class KnownIndexH' (c :: Bool) (as :: k) (bs :: k) where
--   indexValH' :: Int
-- instance KnownLength as => KnownIndexH' 'True as as where
--   indexValH' = lengthVal @_ @as - 1
--   {-# INLINE indexValH' #-}
-- instance KnownIndexH as bs => KnownIndexH' 'False as (b ': bs) where
--   indexValH' = indexValH @as @bs
--   {-# INLINE indexValH' #-}
-- instance KnownIndexH as bs => KnownIndexH' 'False as ('PROMPT eff i bs) where
--   indexValH' = indexValH @as @bs
--   {-# INLINE indexValH' #-}

-- class KnownIndex a b => a :< b
-- instance KnownIndex a b => a :< b

-- class (KnownIndexH a b, KnownLength b) => a :<< b
-- instance (KnownIndexH a b, KnownLength b) => a :<< b

-- | Like ':<<', but only at the type level; it carries no actual evidence. This is slightly more
-- efficient, since it doesn’t have to be passed around, but of course it means the index value
-- cannot actually be accessed.
type family a :<<! b :: Constraint where
  a :<<! a = ()
  a :<<! 'PROMPT _ _ b = a :<<! b

-- newtype WithLength a r = WithLength (KnownLength a => r)
-- withLength :: forall a r. Int -> (KnownLength a => r) -> r
-- withLength n x = unsafeCoerce (WithLength @a x) n
-- {-# INLINE withLength #-}
--
-- newtype WithIndex a b r = WithIndex (KnownIndex a b => r)
-- withIndex :: forall a b r. Int -> (KnownIndex a b => r) -> r
-- withIndex n x = unsafeCoerce (WithIndex @a @b x) n
-- {-# INLINE withIndex #-}

-- newtype WithSubIndex a b r = WithSubIndex (SubIndex a b => r)
-- withSubIndex :: forall a b r. Int -> (SubIndex a b => r) -> r
-- withSubIndex n x = unsafeCoerce (WithSubIndex @a @b x) n
-- {-# INLINE withSubIndex #-}

-- withLengthFromIndexH :: forall hs hs' r. KnownIndexH hs hs' => (KnownLength hs => r) -> r
-- withLengthFromIndexH = withLength @hs (indexValH @hs @hs' + 1)
-- {-# INLINE withLengthFromIndexH #-}

-- discardEvidenceH :: forall a b r. a :<< b => (a :<<! b => r) -> r
-- discardEvidenceH x = case unsafeCoerce Refl of (Refl :: (a :<<! b) :~: (() :: Constraint)) -> x
-- {-# INLINE discardEvidenceH #-}

-- withSubFrames
--   :: forall effs effs' fs' r. (effs :<< effs', effs' :-> fs')
--   => (forall fs. (fs :<< fs', effs :-> fs, R fs ~ R fs') => Proxy# fs -> r) -> r
-- withSubFrames f =
--   ( withIndexH @fs @fs' (indexValH @effs @effs')
--   $ withLength @fs' (lengthVal @_ @effs')
--   $ withRootsEq @fs @fs'
--   $ with (axiomC @(effs :-> fs))
--   $ f (proxy# @_ @fs)
--   ) :: forall (fs :: FramesK). r
-- {-# INLINE withSubFrames #-}
--
-- withHandleIndex
--   :: forall eff i effs effs' hs hs' r. (effs :-> hs, effs' :-> hs', 'PROMPT eff i hs :<< hs')
--   => (Handle eff i effs :< effs' => r) -> r
-- withHandleIndex x =
--   withLength @effs' (lengthVal @_ @hs') $
--   withIndex @(Handle eff i effs) @effs' (indexValH @('PROMPT eff i hs) @hs') x
-- {-# INLINE withHandleIndex #-}
--
-- withEffectFrame
--   :: forall eff effs' hs' r. (effs' :-> hs', eff :< effs')
--   => (forall effs hs. ((eff ': effs) :-> hs, hs :<< hs', R hs ~ R hs') => Proxy# effs -> Proxy# hs -> r) -> r
-- withEffectFrame f =
--   ( withLength @hs' (lengthVal @_ @effs')
--   $ withIndexH @hs @hs' (indexVal @eff @effs')
--   $ withRootsEq @hs @hs'
--   $ with (axiomC @((eff ': effs) :-> hs))
--   $ f (proxy# @_ @effs) (proxy# @_ @hs)
--   ) :: forall (effs :: [Effect]) (hs :: FramesK). r
-- {-# INLINE withEffectFrame #-}

newtype Eff effs a = Eff
  { unEff :: forall hs. (a -> Frames hs -> R hs) -> effs :->> hs -> Frames hs -> R hs }

mkEff :: forall effs a. (forall hs. Proxy# hs -> (a -> Frames hs -> R hs) -> effs :->> hs -> Frames hs -> R hs) -> Eff effs a
mkEff f = Eff (f (proxy# @_ @hs) :: forall hs. (a -> Frames hs -> R hs) -> effs :->> hs -> Frames hs -> R hs)
{-# INLINE mkEff #-}

-- | An array of metacontinuation 'Frame's. Newer frames are added to the /end/ of the array, so the
-- array is stored “backwards” relative to the order the frames appear in 'FramesK'. This ensures
-- indexes into 'Frames' are stable—an index will refer to the same frame even if new frames are
-- added later.
newtype Frames (fs :: FramesK) = Frames { unFrames :: SmallArray Any }

type family Frame fs where
  Frame ('CELL s _) = s
  Frame ('PROMPT eff i hs) = Handler eff i hs

data Handler eff i hs = Handler
  { hSend :: forall effs' hs' a. 'PROMPT eff i hs :<<! hs' => eff (Eff effs') a
          -> (a -> Frames hs' -> R hs') -> effs' :->> hs' -> Frames hs' -> R hs'
  , hCont :: i -> Frames ('PROMPT eff i hs) -> R hs
  -- ^ The continuation of this prompt. When a prompt is first installed via 'handleH', 'hCont' is
  -- initialized to a continuation that pops the prompt, then returns to the parent metacontinuation
  -- frame. 'hCont' can be further extended by uses of 'shiftH'; each use extends the continuation
  -- from the “outside in,” so earlier uses of 'shiftH' wrap later uses.
  }

-- | The /target indirection vector/, which maps each effect in the row of effects to a particular
-- handler. This layer of indirection incurs a small performance cost, but it allows far greater
-- flexibility in how the row of effects may be manipulated.
--
-- Without the indirection, the row of effects would need to be exactly the same length as the stack
-- of metacontinuation frames, and each effect would be handled by its corresponding frame. This
-- makes it impossible for a handler to locally introduce a new effect and handle it immediately
-- without the effect leaking out into the handler’s type. The indirection vector allows effects to
-- be added underneath existing effects, reordered, and deduplicated.
--
-- __Unlike__ 'Frames', ':->>' is ordered from newest to oldest, so the target for the first element
-- of @effs@ is always stored at index @0@. This is convenient because it allows indexes into the
-- array to be more easily calculated at compile-time from the type information, and it isn’t
-- important that the indexes by dynamically stable in the same way it is for 'Frames'.
newtype (effs :: [Effect]) :->> (fs :: FramesK) = Targets { unTargets :: ByteArray }
newtype (eff :: Effect) :-> (fs :: FramesK) = Target { unTarget :: Int }

runByteArray :: (forall s. ST s (MutableByteArray s)) -> ByteArray
runByteArray m = runST (unsafeFreezeByteArray =<< m)
{-# INLINE runByteArray #-}

rootFrames :: Frames ('ROOT r)
rootFrames = Frames mempty
{-# INLINE rootFrames #-}

rootTargets :: '[] :->> 'ROOT r
rootTargets = Targets mempty
{-# INLINE rootTargets #-}

weakenTargets :: effs :->> fs -> effs :->> f fs
weakenTargets (Targets ts) = Targets ts
{-# INLINE weakenTargets #-}

pushFrame :: forall f fs. Frame (f fs) -> Frames fs -> Frames (f fs)
pushFrame h (Frames hs) = Frames $ runSmallArray do
  let len = sizeofSmallArray hs
  hs' <- newSmallArray (len + 1) (error "pushFrame: value left uninitialized")
  copySmallArray hs' 0 hs 0 len
  writeSmallArray hs' len (unsafeCoerce h)
  pure hs'

pushTarget :: forall eff effs fs. eff :-> fs -> effs :->> fs -> (eff ': effs) :->> fs
pushTarget (Target t) (Targets ts) = Targets $ runByteArray do
  let len = sizeofByteArray ts
  assertM $ len >= 0
  assertM $ (len `mod` sIZEOF_INT) == 0
  ts' <- newByteArray (len + sIZEOF_INT)
  writeByteArray ts' 0 t
  copyByteArray ts' sIZEOF_INT ts 0 len
  pure ts'

dropTargets :: forall effs effs' fs. effs :<< effs' => effs' :->> fs -> effs :->> fs
dropTargets (Targets ts) = Targets $ runByteArray do
  let idx = subIndexVal @effs @effs' * sIZEOF_INT
      len = sizeofByteArray ts - idx
  assertM $ idx >= 0
  assertM $ len >= 0
  assertM $ (len `mod` sIZEOF_INT) == 0
  ts' <- newByteArray len
  copyByteArray ts' 0 ts idx len
  pure ts'

-- replaceTargets :: forall effs effs' fs. effs :<< effs' => effs :->> fs -> effs' :->> fs -> effs' :->> fs
-- replaceTargets (Targets ts) (Targets ts') = Targets $ runByteArray do
--   let idx = subIndexVal @effs @effs' * sIZEOF_INT
--   assertM $ idx >= 0
--   assertM $ sizeofByteArray ts >= 0
--   assertM $ (sizeofByteArray ts `mod` sIZEOF_INT) == 0
--   assertM $ sizeofByteArray ts' >= 0
--   assertM $ (sizeofByteArray ts' `mod` sIZEOF_INT) == 0
--   ts'' <- newByteArray (sizeofByteArray ts')
--   copyByteArray ts'' 0 ts' 0 idx
--   copyByteArray ts'' idx ts 0 (sizeofByteArray ts)
--   pure ts''

peekFrame :: Frames fs -> Frame fs
peekFrame (Frames fs) = unsafeCoerce $ indexSmallArray fs (sizeofSmallArray fs - 1)
{-# INLINE peekFrame #-}

popFrame :: forall f fs. Frames (f fs) -> Frames fs
popFrame (Frames fs) = Frames $ cloneSmallArray fs 0 (sizeofSmallArray fs - 1)
{-# INLINE popFrame #-}

-- lookupFrame :: forall fs fs'. fs :<< fs' => Frames fs' -> Frame fs
-- lookupFrame (Frames hs) =
--   let idx = indexValH @fs @fs'
--   in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
--     unsafeCoerce $ indexSmallArray hs idx
-- {-# INLINE lookupFrame #-}

-- withPromptAfter
--   :: forall hs hs' r. (hs :<< hs')
--   => Frames hs'
--   -> (forall eff i. Handler eff i hs -> r)
--   -- ^ called when there is a prompt after the given index
--   -> ((hs ~ hs') => r)
--   -- ^ called when the given index refers to the last prompt
--   -> r
-- withPromptAfter (Frames hs) f g =
--   let len = lengthValH @hs'
--       idx = indexValH @'(hs, hs')
--   in assert (idx >= 0) $ assert (len > 0) $ assert (idx < len) $ assert (len == sizeofSmallArray hs) if
--     | idx == len - 1 -> case unsafeCoerce Refl of (Refl :: hs :~: hs') -> g
--     | otherwise -> f $! unsafeCoerce (indexSmallArray hs (idx + 1))
-- {-# INLINE withPromptAfter #-}

-- replaceFrame :: forall fs fs'. fs :<< fs' => Frame fs -> Frames fs' -> Frames fs'
-- replaceFrame h (Frames hs) = Frames $ runSmallArray do
--   hs' <- thawSmallArray hs 0 (sizeofSmallArray hs)
--   let idx = indexValH @fs @fs'
--   writeSmallArray hs' idx (unsafeCoerce h)
--   pure hs'
--
-- takeFrames :: forall hs hs'. hs :<< hs' => Frames hs' -> Frames hs
-- takeFrames (Frames hs) =
--   let idx = indexValH @hs @hs'
--   in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
--     Frames $ cloneSmallArray hs 0 (idx + 1)
-- {-# INLINE takeFrames #-}
--
-- replaceFrames :: forall hs hs'. hs :<< hs' => Frames hs -> Frames hs' -> Frames hs'
-- replaceFrames (Frames hs) (Frames hs') = Frames $ runSmallArray do
--   hs'' <- thawSmallArray hs' 0 (sizeofSmallArray hs')
--   let idx = indexValH @hs @hs'
--   assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
--     copySmallArray hs'' 0 hs 0 (idx + 1)
--   pure hs''

-- takeFramesUpTo :: forall f fs fs'. f fs :<< fs' => Frames fs' -> Frames fs
-- takeFramesUpTo (Frames hs) =
--   let idx = indexValH @_ @'(f fs, fs')
--   in assert (idx >= 0) $ assert (idx < sizeofSmallArray hs) $
--     Frames $ cloneSmallArray hs 0 idx
-- {-# INLINE takeFramesUpTo #-}

-- | Looks up a 'Handler' for @eff@ via the 'targets' indirection vector.
withHandler
  :: forall eff effs fs' r. eff :< effs
  => effs :->> fs' -> Frames fs'
  -> (forall i fs. 'PROMPT eff i fs :<<! fs' => Proxy# i -> Proxy# fs -> Handler eff i fs -> r) -> r
withHandler (Targets ts) (Frames fs) f =
  let idx = indexByteArray ts (indexVal @eff @effs)
  in case unsafeCoerce $ indexSmallArray fs idx of
    (h :: Handler eff i fs) -> with (axiomC @('PROMPT eff i fs :<<! fs')) $
      f (proxy# @_ @i) (proxy# @_ @fs) h
{-# INLINE withHandler #-}

-- -- | Converts a @effs ':<<' effs'@ constraint into a @fs ':<<' fs'@ constraint.
-- withSubHandler
--   :: forall eff effs fs' r. eff :< effs

run :: Eff '[] a -> a
run (Eff m) = m (\v _ -> v) rootTargets rootFrames
{-# INLINE run #-}

instance Functor (Eff effs) where
  fmap f (Eff m) = Eff \k -> m \a -> k (f a)
  {-# INLINE fmap #-}

instance Applicative (Eff effs) where
  pure a = Eff \k _ -> k a
  {-# INLINE pure #-}
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad (Eff effs) where
  Eff m >>= f = Eff \k ts -> m (\a -> unEff (f a) k ts) ts
  {-# INLINE (>>=) #-}

lift :: forall effs effs'. effs :<< effs' => Eff effs ~> Eff effs'
lift (Eff m) = Eff \k ts -> m k $! dropTargets ts

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = Eff \k ts fs -> withHandler @eff ts fs \_ _ h -> hSend h e k ts fs

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = mkEff \(_ :: Proxy# fs') _ ts fs ->
  -- TODO: extract into safer interface
  let !idx_t = subIndexVal @(eff ': effs) @effs' * sIZEOF_INT
      !idx_f = assert (idx_t >= 0) $ assert (idx_t < sizeofByteArray (unTargets ts)) $
        indexByteArray (unTargets ts) idx_t
  in ( let fs' :: Frames ('PROMPT eff i fs)
           !fs' = assert (idx_f >= 0) $ assert (idx_f < sizeofSmallArray (unFrames fs)) $
             Frames $ cloneSmallArray (unFrames fs) 0 (idx_f + 1)
       in with (axiom @(R fs) @(R fs')) $ hCont (peekFrame fs') a fs'
     ) :: forall (fs :: FramesK). R fs'

-- shiftH
--   :: forall eff i hs hs' a. ('PROMPT eff i hs :<< hs')
--   => ((a -> EffH ('PROMPT eff i hs) i) -> EffH ('PROMPT eff i hs) i)
--   -> EffH hs' a
-- shiftH f = withRootsEq @('PROMPT eff i hs) @hs' $ EffH \kn hs ->
--   let !idx = indexValH @'( 'PROMPT eff i hs, hs')
--
--       m :: (i -> Frames ('PROMPT eff i hs) -> R hs) -> Frames ('PROMPT eff i hs) -> R hs
--       m = unEffH $ f \a -> EffH \k1 (Frames hs1) ->
--         assert (idx == sizeofSmallArray hs1 - 1) $
--           kn a $! Frames $ runSmallArray do
--             -- copy the original set of prompts for a fresh copy of all local state
--             hs' <- thawSmallArray (unFrames hs) 0 (sizeofSmallArray $ unFrames hs)
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

-- getC :: forall s effs. Cell s :< effs => Eff effs s
-- getC = mkEff \(_ :: Proxy# fs) k fs ->
--   withEffectFrame @(Cell s) @effs @fs \(_ :: Proxy# effs') (_ :: Proxy# fs') ->
--   decompCell @s @effs' @fs' \_ ->
--     (k $! lookupFrame @fs' fs) fs
--
-- putC :: forall s effs. Cell s :< effs => s -> Eff effs ()
-- putC s = mkEff \(_ :: Proxy# fs) k fs ->
--   withEffectFrame @(Cell s) @effs @fs \(_ :: Proxy# effs') (_ :: Proxy# fs') ->
--   decompCell @s @effs' @fs' \_ ->
--     k () $! replaceFrame @fs' s fs
--
-- runCell :: forall s effs. s -> Eff (Cell s ': effs) ~> Eff effs
-- runCell s (Eff m) = Eff \k hs -> m (\a hs' -> k a $! popFrame hs') $! pushFrame @('CELL s) s hs

class (eff ': effs) :<< effs' => Handling eff effs (i :: Type) effs' | eff effs' -> i effs

newtype WithHandling eff effs i effs' r = WithHandling (Handling eff effs i effs' => r)
withHandlerIndex :: forall eff effs i effs' r. Int -> (Handling eff effs i effs' => r) -> r
withHandlerIndex n x = unsafeCoerce (WithHandling @eff @effs @i @effs' x) n
{-# INLINE withHandlerIndex #-}

handle
  :: forall eff a effs. Handles eff
  => (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m) = mkEff \(_ :: Proxy# hs) k0 ts0 fs0 ->
  let k1 a fs2 = k0 a $! popFrame fs2
      k2 a fs2 = hCont (peekFrame fs2) a fs2

      !idx = sizeofSmallArray $ unFrames fs0
      -- TODO: make Target construction safer
      !ts1 = pushTarget (Target idx) (weakenTargets ts0)
      !len = sizeofByteArray $ unTargets ts1

      f' :: forall effs' hs' b. eff (Eff effs') b
         -> (b -> Frames hs' -> R hs') -> effs' :->> hs' -> Frames hs' -> R hs'
      f' e k ts =
        let len' = sizeofByteArray $ unTargets ts
            !idx' = assert (((len' - len) `mod` sIZEOF_INT) == 0) $
              (len' - len) `div` sIZEOF_INT
        in withHandlerIndex @eff @effs @a @effs' idx' $ unEff (f e) k ts
      !fs1 = pushFrame (Handler @eff f' k1) fs0
  in m k2 ts1 fs1
