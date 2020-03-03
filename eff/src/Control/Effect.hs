{-| @eff@ is a fast, flexible, easy to use effect system for Haskell. @eff@
makes it easy to write composable, modular effects and effect handlers without
sacrificing performance. Broadly speaking, @eff@ provides the following
features:

  * The 'Eff' monad, which provides an extremely flexible set of control
    operations that can be used to implement a variety of effects.

  * A standard library of built-in effects and effect handlers, including common
    effects like 'Reader', 'State', and 'Error'.

  * A framework for defining your own effects and effect handlers, which can
    either be built from scratch using the 'Eff' primitives or by delegating to
    an existing handler.

@eff@ is far from the first effect system for Haskell, but it differentiates
itself from existing libraries in the following respects:

  * @eff@ is built atop a direct, low-level implementation of delimited
    continuations to provide the best performance possible.

  * @eff@ provides a simpler, more streamlined API for handling effects.

  * Like @polysemy@ and @fused-effects@ (but unlike @freer-simple@), @eff@
    supports so called “scoped” effect operations like 'local' and 'catch', but
    unlike @polysemy@ and @fused-effects@ (and also unlike
    @transformers@/@mtl@), @eff@ provides a consistent semantics for such
    operations regardless of handler order.

@eff@ aspires to be a turnkey replacement for most traditional uses of monad
transformers. @eff@ provides comparable performance to @transformers@ and @mtl@
with less complexity, less boilerplate, and a simpler semantics. -}
module Control.Effect (
  -- * The @Eff@ monad
    Eff
  , run
  , lift
  , lift1

  -- * Defining new effects
  , Effect
  , send
  , (:<)
  , (:<<)

  -- * Handling effects
  -- ** Simple effect handlers
  , interpret
  -- ** Advanced effect handlers
  , Handle
  , handle
  , liftH
  , abort
  , control
  , locally

  -- * Performing I/O
  , IOE(..)
  , MonadIO(..)
  , runIO

  -- * Re-exports
  , (&)
  , (>>>)
  -- ** Built-in effects
  , module Control.Effect.Coroutine
  , module Control.Effect.Error
  , module Control.Effect.NonDet
  , module Control.Effect.Reader
  , module Control.Effect.State.Strict
  , module Control.Effect.Writer.Strict
  ) where

import Control.Applicative
import Control.Category ((>>>))
import Control.Monad.IO.Class
import Data.Function

import Control.Effect.Base
import Control.Effect.Coroutine
import Control.Effect.Error
import Control.Effect.Internal
import Control.Effect.NonDet
import Control.Effect.Reader
import Control.Effect.State.Strict
import Control.Effect.Writer.Strict
