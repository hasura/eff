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
import GHC.TypeLits (ErrorMessage(..), Nat, TypeError)
import Unsafe.Coerce (unsafeCoerce)

with :: a :~: b -> (a ~ b => r) -> r
with Refl x = x
{-# INLINE with #-}

axiom :: forall a b. a :~: b
axiom = unsafeCoerce Refl
{-# INLINE axiom #-}

type Holds = (~) (() :: Constraint)
type Proof = (:~:) (() :: Constraint)

axiomC :: forall a. Proof a
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

-- | Primitive effects are uninhabited, so we can obtain a proof of 'Handles' by forcing an effect
-- value.
handles :: eff m a -> Proof (Handles eff)
handles !_ = axiomC
{-# INLINE handles #-}

data FramesK
  = ROOT Type
  | CELL Type FramesK
  | PROMPT Effect Type FramesK

type FrameK = FramesK -> FramesK

type family R hs where
  R ('ROOT r) = r
  R ('CELL _ hs) = R hs
  R ('PROMPT _ _ hs) = R hs

type family FrameEffect f where
  FrameEffect ('CELL s) = Cell s
  FrameEffect ('PROMPT eff _) = eff

withHandlesImpliesPrompt
  :: forall eff f r. (Handles eff, eff ~ FrameEffect f) => (forall i. f ~ 'PROMPT eff i => r) -> r
withHandlesImpliesPrompt x = with (axiom @f @('PROMPT eff i)) x :: forall (i :: Type). r
{-# INLINE withHandlesImpliesPrompt #-}

decomposeCell :: forall s f. Cell s ~ FrameEffect f => f :~: 'CELL s
decomposeCell = axiom
{-# INLINE decomposeCell #-}

-- | If one 'FramesK' is contained within the other, their roots must be equal.
rootsEq :: hs :<<! hs' => R hs :~: R hs'
rootsEq = axiom
{-# INLINE rootsEq #-}

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

class Length (fs :: FramesK) where
  lengthVal :: Int
instance Length ('ROOT r) where
  lengthVal = 0
  {-# INLINE lengthVal #-}
instance Length fs => Length ('CELL s fs) where
  lengthVal = lengthVal @fs + 1
  {-# INLINE lengthVal #-}
instance Length fs => Length ('PROMPT eff i fs) where
  lengthVal = lengthVal @fs + 1
  {-# INLINE lengthVal #-}

class (f :: FrameK) :<# (fs :: FramesK) where
  indexValF :: Int
instance {-# OVERLAPPING #-} Length (f fs) => f :<# f fs where
  indexValF = lengthVal @(f fs) - 1
  {-# INLINE indexValF #-}
instance f :<# fs => f :<# f' fs where
  indexValF = indexValF @f @fs
  {-# INLINE indexValF #-}

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

class (fs :: FramesK) :<<# (fs' :: FramesK) where
  subIndexValF :: Int
instance {-# OVERLAPPING #-} Length fs => fs :<<# fs where
  subIndexValF = lengthVal @fs - 1
  {-# INLINE subIndexValF #-}
instance (ffs' ~ f fs', fs :<<# fs') => fs :<<# ffs' where
  subIndexValF = subIndexValF @fs @fs'
  {-# INLINE subIndexValF #-}

newtype WithLength fs r = WithLength (Length fs => r)
withLength :: forall fs r. Int -> (Length fs => r) -> r
withLength n x = unsafeCoerce (WithLength @fs x) $! n
{-# INLINE withLength #-}

withLengthOf :: forall fs r. Frames fs -> (Length fs => r) -> r
withLengthOf (Frames fs) = withLength @fs (sizeofSmallArray fs)
{-# INLINE withLengthOf #-}

newtype WithSubIndexF fs fs' r = WithSubIndexF (fs :<<# fs' => r)
withSubIndexF :: forall fs fs' r. Int -> (fs :<<# fs' => r) -> r
withSubIndexF n x = unsafeCoerce (WithSubIndexF @fs @fs' x) $! n
{-# INLINE withSubIndexF #-}

withWeakenSubIndex :: forall f fs fs' r. f fs :<<# fs' => (fs :<<# fs' => r) -> r
withWeakenSubIndex = withSubIndexF @fs @fs' (subIndexValF @(f fs) @fs' - 1)
{-# INLINE withWeakenSubIndex #-}

-- | Like ':<<', but only at the type level; it carries no actual evidence. This is slightly more
-- efficient, since it doesn’t have to be passed around, but of course it means the index value
-- cannot actually be accessed.
type family fs :<<! fs' :: Constraint where
  fs :<<! fs = ()
  fs :<<! _ fs' = fs :<<! fs'

eraseSub :: forall fs fs'. fs :<<# fs' => Proof (fs :<<! fs')
eraseSub = subIndexValF @fs @fs' `seq` axiom
{-# INLINE eraseSub #-}

attachSub :: forall fs fs' r. (Length fs, fs :<<! fs') => (fs :<<# fs' => r) -> r
attachSub = withSubIndexF @fs @fs' (subIndexValF @fs @fs)
{-# INLINE attachSub #-}

weakenSub :: forall fs f fs'. fs :<<! fs' => Proof (fs :<<! f fs')
weakenSub = axiom
{-# INLINE weakenSub #-}

transSub :: forall fs1 fs2 fs3. (fs1 :<<! fs2, fs2 :<<! fs3) => Proof (fs1 :<<! fs3)
transSub = axiom
{-# INLINE transSub #-}

transAttachSub :: forall fs1 fs2 fs3 r. (fs1 :<<# fs2, fs2 :<<! fs3) => (fs1 :<<# fs3 => r) -> r
transAttachSub = withSubIndexF @fs1 @fs3 (subIndexValF @fs1 @fs2)
{-# INLINE transAttachSub #-}

type family effs :->>! fs :: Constraint where {}
eraseTargets :: forall effs fs. effs :->> fs -> Proof (effs :->>! fs)
eraseTargets !_ = axiom
{-# INLINE eraseTargets #-}

newtype Eff effs a = Eff
  { unEff :: forall fs. (a -> Frames fs -> R fs) -> effs :->> fs -> Frames fs -> R fs }

mkEff :: forall effs a. (forall fs. Proxy# fs -> (a -> Frames fs -> R fs) -> effs :->> fs -> Frames fs -> R fs) -> Eff effs a
mkEff f = Eff (f (proxy# @_ @fs) :: forall fs. (a -> Frames fs -> R fs) -> effs :->> fs -> Frames fs -> R fs)
{-# INLINE mkEff #-}

-- | An array of metacontinuation 'Frame's. Newer frames are added to the /end/ of the array, so the
-- array is stored “backwards” relative to the order the frames appear in 'FramesK'. This ensures
-- indexes into 'Frames' are stable—an index will refer to the same frame even if new frames are
-- added later.
newtype Frames (fs :: FramesK) = Frames { unFrames :: SmallArray Any }

type family Frame fs where
  Frame ('CELL s _) = s
  Frame ('PROMPT eff i fs) = Handler eff i fs

data Handler eff i fs = Handler
  { hSend :: forall effs' fs' a. Holds ('PROMPT eff i fs :<<! fs') => eff (Eff effs') a
          -> (a -> Frames fs' -> R fs') -> effs' :->> fs' -> Frames fs' -> R fs'
  , hCont :: i -> Frames fs -> R fs
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

noTargets :: '[] :->> fs
noTargets = Targets mempty
{-# INLINE noTargets #-}

weakenTargets :: fs :<<! fs' => effs :->> fs -> effs :->> fs'
weakenTargets (Targets ts) = Targets ts
{-# INLINE weakenTargets #-}

pushFrame :: forall f fs. Frame (f fs) -> Frames fs -> Frames (f fs)
pushFrame h (Frames hs) = Frames $ runSmallArray do
  let len = sizeofSmallArray hs
  hs' <- newSmallArray (len + 1) (error "pushFrame: value left uninitialized")
  copySmallArray hs' 0 hs 0 len
  writeSmallArray hs' len (unsafeCoerce h)
  pure hs'

newTarget :: forall f fs. f :<# fs => FrameEffect f :-> fs
newTarget = Target $ indexValF @f @fs
{-# INLINE newTarget #-}

lookupTarget :: forall eff effs fs. eff :< effs => effs :->> fs -> eff :-> fs
lookupTarget (Targets ts) = Target $ indexByteArray ts (indexVal @eff @effs)

pushTarget :: forall eff effs fs. eff :-> fs -> effs :->> fs -> (eff ': effs) :->> fs
pushTarget (Target t) (Targets ts) = Targets $ runByteArray do
  let len = sizeofByteArray ts
  assertM $ len >= 0
  assertM $ (len `mod` sIZEOF_INT) == 0
  ts' <- newByteArray (len + sIZEOF_INT)
  writeByteArray ts' 0 t
  copyByteArray ts' sIZEOF_INT ts 0 len
  pure ts'

popTarget :: forall eff effs fs. (eff ': effs) :->> fs -> effs :->> fs
popTarget (Targets ts) = Targets $ runByteArray do
  let len = sizeofByteArray ts - sIZEOF_INT
  assertM $ len >= 0
  assertM $ (len `mod` sIZEOF_INT) == 0
  ts' <- newByteArray len
  copyByteArray ts' 0 ts sIZEOF_INT len
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

peekFrame :: Frames fs -> Frame fs
peekFrame (Frames fs) = unsafeCoerce $ indexSmallArray fs (sizeofSmallArray fs - 1)
{-# INLINE peekFrame #-}

popFrame :: forall f fs. Frames (f fs) -> Frames fs
popFrame (Frames fs) = Frames $ cloneSmallArray fs 0 (sizeofSmallArray fs - 1)
{-# INLINE popFrame #-}

indexFrame :: forall fs fs'. fs :<<# fs' => Frames fs' -> Frame fs
indexFrame (Frames fs) = unsafeCoerce $ indexSmallArray fs (subIndexValF @fs @fs')
{-# INLINE indexFrame #-}

setFrame :: forall fs fs'. fs :<<# fs' => Frame fs -> Frames fs' -> Frames fs'
setFrame f (Frames fs) = Frames $ runSmallArray do
  fs' <- thawSmallArray fs 0 (sizeofSmallArray fs)
  writeSmallArray fs' (subIndexValF @fs @fs') (unsafeCoerce f)
  pure fs'

takeFrames :: forall fs fs'. fs :<<# fs' => Frames fs' -> Frames fs
takeFrames (Frames hs) =
  let len = subIndexValF @fs @fs' + 1
  in assert (len >= 0) $ assert (len <= sizeofSmallArray hs) $
    Frames $ cloneSmallArray hs 0 len
{-# INLINE takeFrames #-}

lookupFrame
  :: forall eff fs' r. eff :-> fs' -> Frames fs'
  -> (forall f fs. (eff ~ FrameEffect f, Holds (f fs :<<! fs')) => Proxy# f -> Proxy# fs -> Frame (f fs) -> r) -> r
lookupFrame (Target t) (Frames fs) f =
  ( assert (t >= 0)
  $ assert (t < sizeofSmallArray fs)
  $ with (axiom @eff @(FrameEffect f))
  $ with (axiomC @(f fs :<<! fs'))
  $ f @f @fs proxy# proxy# (unsafeCoerce $ indexSmallArray fs t)
  ) :: forall (f :: FrameK) (fs :: FramesK). r
{-# INLINE lookupFrame #-}

replaceFrame
  :: forall eff fs
   . eff :-> fs
  -> Frames fs
  -> (forall f fs'. eff ~ FrameEffect f => Proxy# f -> Proxy# fs' -> Frame (f fs'))
  -> Frames fs
replaceFrame (Target t) (Frames fs) f =
  ( assert (t >= 0)
  $ assert (t < sizeofSmallArray fs)
  $ with (axiom @eff @(FrameEffect f))
  $ Frames $ runSmallArray do
      fs' <- thawSmallArray fs 0 (sizeofSmallArray fs)
      writeSmallArray fs' t (unsafeCoerce $ f @f @fs' proxy# proxy#)
      pure fs'
  ) :: forall (f :: FrameK) (fs' :: FramesK). Frames fs

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

run :: Eff '[] a -> a
run (Eff m) = m (\v _ -> v) noTargets rootFrames
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

liftH :: forall eff effs i effs'. Handling eff effs i effs' => Eff (eff ': effs) ~> Eff effs'
liftH (Eff m) = mkEff \(_ :: Proxy# fs') k ts' ->
  withHandlingTargets' @eff ts' \(_ :: Proxy# fs) _ ts ->
  with (eraseSub @('PROMPT eff i fs) @fs') $
    m k (weakenTargets ts)

send :: forall eff effs. eff :< effs => eff (Eff effs) ~> Eff effs
send e = mkEff \(_ :: Proxy# fs) k ts fs ->
  lookupFrame (lookupTarget @eff ts) fs \(_ :: Proxy# f) (_ :: Proxy# fs') h ->
    with (handles e) $ withHandlesImpliesPrompt @eff @f $ hSend h e k ts fs

abort :: forall eff effs i effs' a. Handling eff effs i effs' => i -> Eff effs' a
abort a = mkEff \(_ :: Proxy# fs') _ ts' fs' ->
  withHandlingTargets' @eff ts' \(_ :: Proxy# fs) _ _ ->
  with (eraseSub @('PROMPT eff i fs) @fs') $
  with (rootsEq @('PROMPT eff i fs) @fs') $
  withWeakenSubIndex @('PROMPT eff i) @fs @fs' $
    hCont (indexFrame @('PROMPT eff i fs) fs') a $! takeFrames @fs fs'

shift
  :: forall eff effs i effs' a. Handling eff effs i effs'
  => ((a -> Eff effs i) -> Eff effs i) -> Eff effs' a
shift f = mkEff \(_ :: Proxy# fsn) kn tsn fsn ->
  withHandlingTargets' @eff tsn \(_ :: Proxy# fs0) ts0 _ ->
  with (eraseSub @('PROMPT eff i fs0) @fsn) $
  with (rootsEq @('PROMPT eff i fs0) @fsn) $
  withWeakenSubIndex @('PROMPT eff i) @fs0 @fsn
    let !h0 = indexFrame @('PROMPT eff i fs0) fsn

        m :: Eff effs i
        m = f \a -> mkEff \(_ :: Proxy# fs1) k1 ts1 fs1 ->
          -- Here’s where all the magic happens. The continuation `kn` is wired to run the current
          -- prompt to completion, then pop it and call the parent frame’s continuation, `hCont`.
          -- This process happens transitively, eventually reaching the root continuation.
          --
          -- To capture a portion of the continuation, all we have to do is “redirect” the return
          -- from a given prompt by replacing its `hCont` with a continuation that actually goes
          -- somewhere else. In this case, we replace it with `k1`, so it actually jumps into
          -- whatever computation `f` places the resulting `Eff` computation in.
          --
          -- That is exactly what we want, but unfortunately, the current type used for the
          -- continuation inside `Eff` doesn’t really understand the effect of this redirection.
          -- The continuation expects `hCont` to still be a continuation into the underlying frame,
          -- one that eventually returns `R fsn`.
          --
          -- Rather than plumb this information through properly, we just cheat and call
          -- `unsafeCoerce`. This actually is safe to the best of my knowledge, but it’s still
          -- troubling. I would love to find a way to capture this in the type system, but I haven’t
          -- come up with anything workable yet.
          with (axiom @(R fs0) @(R fs1)) $ -- Evil!! Depends on the aforementioned redirection.
            let k :: i -> Frames fs -> R fs1
                k a _ = k1 a fs1 -- This does the redirection, dropping the old frames completely.
                !h0' = h0 { hCont = k }
            in kn a $! setFrame @('PROMPT eff i fs0) h0' fsn

    in unEff m (hCont h0) ts0 $! takeFrames @fs0 fsn

getC :: forall s effs. Cell s :< effs => Eff effs s
getC = Eff \k ts fs ->
  lookupFrame (lookupTarget @(Cell s) ts) fs \(_ :: Proxy# f) _ !s ->
    with (decomposeCell @s @f) k s fs

putC :: forall s effs. Cell s :< effs => s -> Eff effs ()
putC s = mkEff \(_ :: Proxy# fs) k ts fs ->
  k () $! replaceFrame (lookupTarget @(Cell s) ts) fs \(_ :: Proxy# f) _ ->
    with (decomposeCell @s @f) s

runCell :: forall s effs. s -> Eff (Cell s ': effs) ~> Eff effs
runCell s (Eff m) = mkEff \(_ :: Proxy# fs) k ts fs ->
  withLengthOf fs $
  with (weakenSub @fs @('CELL s) @fs)
    let !ts' = pushTarget (newTarget @('CELL s)) (weakenTargets ts)
        !fs' = pushFrame @('CELL s) s fs
    in m (\a fs' -> k a $! popFrame fs') ts' fs'

class Handling eff effs i effs' | eff effs' -> i effs where
  withHandlingTargets :: WithHandlingTargets eff effs i effs'

withHandlingTargets'
  :: forall eff effs i effs' fs' r
   . Handling eff effs i effs'
  => effs' :->> fs'
  -> (forall fs. (Length ('PROMPT eff i fs), 'PROMPT eff i fs :<<# fs')
      => Proxy# fs -> effs :->> fs -> (eff ': effs) :->> 'PROMPT eff i fs -> r)
  -> r
withHandlingTargets' ts f =
  with (eraseTargets ts)
    let WithHandlingTargets wht = withHandlingTargets @eff @effs @i @effs'
    in wht @fs' proxy# f
{-# INLINE withHandlingTargets' #-}

newtype WithHandlingTargets eff effs i effs' = WithHandlingTargets
  (forall fs' r
   . Holds (effs' :->>! fs')
  => Proxy# fs'
  -> (forall fs. (Length ('PROMPT eff i fs), 'PROMPT eff i fs :<<# fs')
      => Proxy# fs
      -> effs :->> fs
      -> (eff ': effs) :->> 'PROMPT eff i fs
      -> r)
  -> r)

newtype WithHandling eff effs i effs' r = WithHandling (Handling eff effs i effs' => r)
withHandling
  :: forall eff effs i effs' r. WithHandlingTargets eff effs i effs'
  -> (Handling eff effs i effs' => r) -> r
withHandling ts x = unsafeCoerce (WithHandling @eff @effs @i @effs' x) ts
{-# INLINE withHandling #-}

handle
  :: forall eff a effs. Handles eff
  => (forall effs'. Handling eff effs a effs' => eff (Eff effs') ~> Eff effs')
  -> Eff (eff ': effs) a
  -> Eff effs a
handle f (Eff m) = mkEff \(_ :: Proxy# fs) k0 ts0 fs0 ->
  withLengthOf fs0 $
  with (weakenSub @fs @('PROMPT eff a) @fs)
    let k2 :: a -> Frames ('PROMPT eff a fs) -> R fs
        k2 a fs2 = hCont (peekFrame fs2) a $! popFrame fs2

        -- TODO: make Target construction safer
        !idx = sizeofSmallArray $ unFrames fs0
        !ts1 = pushTarget (Target idx) (weakenTargets ts0)

        f' :: forall effs' fs' b. Holds ('PROMPT eff a fs :<<! fs') => eff (Eff effs') b
           -> (b -> Frames fs' -> R fs') -> effs' :->> fs' -> Frames fs' -> R fs'
        f' e k ts =
          attachSub @('PROMPT eff a fs) @fs' $
          withHandling @eff @effs @a @effs'
            (WithHandlingTargets \(_ :: Proxy# fs'') g ->
              -- `fs' :<<! fs''` must hold, because in the type signature for `handle`, `effs'` is a
              -- skolem! Therefore, the only way `effs' :->>! fs''` could ever be satisfied is if an
              -- `effs' :->> fs''` were constructed from the `ts` we receive here, which must be a
              -- subcomputation of `f e`.
              --
              -- This is really the essence of what a 'Handling' constraint means, and this axiom is
              -- the linchpin that makes everything work.
              with (axiomC @(fs' :<<! fs'')) $
              transAttachSub @('PROMPT eff a fs) @fs' @fs'' $
              -- TODO: could make ts0 a slice into ts1 instead of a separate array to save a small
              -- bit of memory
              g proxy# ts0 ts1)
            (unEff (f e) k ts)

    in m k2 ts1 $! pushFrame (Handler @eff f' k0) fs0

class Swizzle effs effs' where
  swizzleTargets :: effs' :->> fs -> effs :->> fs
instance {-# INCOHERENT #-} Swizzle effs effs where
  swizzleTargets = id
  {-# INLINE swizzleTargets #-}
instance {-# INCOHERENT #-} Swizzle effs effs' => Swizzle effs (eff ': effs') where
  swizzleTargets ts = swizzleTargets @effs @effs' $! popTarget ts
  {-# INLINE swizzleTargets #-}
instance Swizzle '[] effs where
  swizzleTargets _ = noTargets
  {-# INLINE swizzleTargets #-}
instance (eff :< effs', Swizzle effs effs') => Swizzle (eff ': effs) effs' where
  swizzleTargets ts = pushTarget (lookupTarget @eff ts) $! swizzleTargets @effs ts

-- | A magician hands you a deck of cards.
--
-- “Take some cards off the top,” she tells you, “then put them back in any order you like.”
--
-- That’s what 'swizzle' does. If you picture the list of effects @effs@ like a deck of cards,
-- 'swizzle' allows you to rearrange it arbitrarily, so long as all the cards you started with are
-- still /somewhere/ in the deck when you’re finished. In fact, 'swizzle' is even more powerful than
-- that, as you may also add entirely new cards into the deck, as many as you please! You just can’t
-- take any cards out.
--
-- As it happens, the metaphor is apt for more reason than one, because 'swizzle' is slightly
-- magical. Under the hood, it tries its absolute best to figure out what you mean. Usually it does
-- a pretty good job, but sometimes it doesn’t get it quite right, and you may receive a rather
-- mystifying type error. In that case, fear not: all you need to do is offer it a little help by
-- adding some type annotations (or using @TypeApplications@).
swizzle :: Swizzle effs effs' => Eff effs ~> Eff effs'
swizzle (Eff m) = Eff \k ts -> m k (swizzleTargets ts)
{-# INLINE swizzle #-}
