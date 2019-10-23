{-# LANGUAGE CPP #-}

{-|

This library is an implementation of an /extensible effect system/ for Haskell, a general-purpose
solution for tracking effects at the type level and handling them in various ways. The term “effect”
as used by this library is very general: it encompasses things most people consider side-effects,
such as generating random values, interacting with the file system, or mutating state, but it also
includes globally-pure but locally-impure operations such as access to an immutable global
environment or exception handling.

The traditional approach to effect composition in Haskell is /monad transformers/, but programming
against a concrete stack of monad transformers can make reuse difficult and tethers a program to a
particular implementation of each effect. The @mtl@ library provides a partial solution to this
problem by providing a typeclass for each effect, which allow programmers to parameterize
computations over the monad they are executed in. However, that technique has problems of its own,
most notably that it requires /m/×/n/ instances be written for code that uses /m/ distinct effects
and /n/ distinct effect implementations.

@eff@ is a reformulation of @mtl@ that avoids the “quadratic instance” problem. Like @mtl@, it uses
monad transformers to represent effect implementations, which @eff@ calls effect /handlers/, and it
uses typeclasses to represent effects. Unlike @mtl@, @eff@ uses a slightly different encoding that
allows explicit instances to be written /only/ for the effects handled by each transformer,
requiring a linear rather than quadratic number of instances. It achieves this without any use of
overlapping instances or Template Haskell by keeping track of a little extra information at the type
level that can be used to guide instance selection.

Generally speaking, this library provides two discrete (but related) chunks of functionality:

  1. First, @eff@ provides a library of common effects, such as 'Reader', 'Error', and 'State', as
     well as handlers for them. These can be used out of the box the same way @transformers@ and
     @mtl@ can be, and they use a similar interface.

  2. Second, @eff@ exposes the infrastructure necessary to define /your own/ effects and effect
     handlers, all of which automatically cooperate with the built-in effects and any effects
     defined in other libraries.

Compared to other Haskell effect system libraries, such as @freer@, @polysemy@, and @fused-effects@,
@eff@ distinguishes itself in the following respects:

  * @eff@ is, at the time of this writing, the fastest effect system available. Its performance is
    equivalent to that of @mtl@, which is slightly faster than @fused-effects@ and significantly
    faster than @freer@ or @polysemy@ on real workloads. It is designed specifically to take
    advantage of the GHC optimizer by cooperating with specialization as much as possible.

  * Unlike other effect systems, @eff@ interoperates with the rest of the @transformers@ ecosystem
    by design. Its core effect handlers /are/ the monad transformers provided by @transformers@, and
    it uses the standard 'MonadTransControl' class from @monad-control@ to implement the lifting of
    higher-order effects. It is easy to reuse functionality from the @transformers@ and @mtl@
    ecosystems with @eff@.

  * Despite its use of monad transformers and its focus on performance, defining effects and effect
    handlers in @eff@ requires relatively little boilerplate, though @freer-simple@ and @polysemy@
    provide some Template Haskell code that can generate most of the boilerplate automatically.
    Providing similar Template Haskell functionality is a future goal of this library, but it as not
    yet been implemented.

  * Unlike @freer@, but like @polysemy@ and @fused-effects@, @eff@ supports higher-order (or scoped)
    effects, in addition to the more traditional algebraic effects.

-}
module Control.Effect (
  -- * Using effects
  -- $using_effects
    Can

  -- * Defining new effects #defining_effects#
  -- $defining_effects
  , EffectK
  , Send(..)
  , controlT

  -- * Implementing new effect handlers
  -- $handling_effects
  , HandlerK

  -- ** The @EffT@ transformer
  , EffT(..)
  , EffsT

  -- ** The @Handles@ type family
  , Handles
  , type (==)
  , Elem

  -- ** The @HandlerT@ transformer
  , HandlerT(..)
  ) where

import Control.Effect.Internal
import Data.Type.Equality (type (==))

#ifdef __HADDOCK_VERSION__
import Control.Effect.Reader
import Control.Effect.State
import Control.Effect.Error
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
#endif

{-$using_effects

Effects in @eff@ are little more than ordinary typeclasses on monads. To show an example, the
definition of the standard 'Reader' effect, which provides access to a global environment, is
written roughly as follows:

@
class 'Monad' m => 'Reader' r m where
  'ask' :: m r
  'local' :: (r -> r) -> m a -> m a
@

If you’re already familiar with @mtl@, this class may look familiar to you, and indeed, 'Reader' is
effectively identical to the @MonadReader@ class from @mtl@, but without the functional dependency
from @m@ to @r@.

To write a function that uses a particular effect, simply add the effect as a constraint in the
function’s type signature. For example, the following function uses 'Reader' to get access to a
'String', combines it with its argument, then prints the result to the console:

@
printSuffixed :: ('Reader' 'String' m, 'MonadIO' m) => 'String' -> m ()
printSuffixed suffix = do
  message <- 'ask' @'String'
  'liftIO' '$' 'putStrLn' (message '<>' suffix)
@

To /run/ an effectful computation, use an /effect handler/. A single effect may have many different
effect handlers—for example, an effect that provides access to the filesystem might have both a real
implementation and one that uses an in-memory, virtual file system for testing—so the choice of what
an effect actually does is chosen when an effect is handled, not where it’s used. In the case of
'Reader', we’ll use the built-in handler, 'runReader', which just supplies the value that will be
returned by 'ask':

@
>>> 'runReader' \"Hello\" '$' printSuffixed \", world!\"
Hello, world!
@

How does this work? Take a look at the type of the above expression:

@
>>> :t 'runReader' \"Hello\" '$' printSuffixed \", world!\"
'MonadIO' m => m ()
@

Notice that by using the 'runReader' handler, the @'Reader' 'String'@ effect was “discharged” from
the constraints, leaving only 'MonadIO'. This is how effects and effect handlers, work: a
computation may use many different effects, and they are handled one at a time by handlers until
none are left.

This library provides a handful of general-purpose, built-in effects. Most of them are a little more
complicated than 'Reader', but they all work the same basic way: add constraints to use effects,
then use handlers to discharge them. In many applications, it may make sense to build up a giant
list of effect constraints, then discharge them all at the top-level of your program, in the @main@
function. In other situations, it may make sense to discharge effects incrementally, sprinkling
handlers throughout the code. Both of these approaches are supported, so the decision of how to take
advantage of effects is up to you. -}

{-$defining_effects

When using only the built-in effects and handlers, the interface of @eff@ is not substantially
different from the interface of @mtl@. However, the benefits of @eff@ appear when defining new
effects and effect handlers, not just using the built-in ones.

The first step to defining a new effect is easy: just write a typeclass that defines the operations
your effect should support. For example, to define an effect that supports interacting with the file
system, you might write the following:

@
class 'Monad' m => FileSystem m where
  readFile :: 'FilePath' -> m 'String'
  writeFile :: 'FilePath' -> 'String' -> m ()
@

The next step is to teach @eff@ about your brand new effect. To do that, you need to make the
special 'EffT' monad transformer an instance of your new @FileSystem@ effect. This part is mostly
just boilerplate, so it may be able to be generated automatically in a future version of this
library, but for now, it must be written by hand. Here is what the instance looks like for
@FileSystem@:

@
instance ('Monad' (t m), 'Send' FileSystem t m) => FileSystem ('EffT' t m) where
  readFile path = 'send' \@FileSystem (readFile path)
  writeFile path contents = 'send' \@FileSystem (writeFile path contents)
@

As you can see, this is an extremely boring instance, but it’s necessary to teach @eff@ how to lift
actions though monad transformers. In this case, the solution is trivial, but it isn’t always so
simple. To see why, consider a third method you might want as part of the @FileSystem@ effect:

@
class 'Monad' m => FileSystem m where
  readFile :: 'FilePath' -> m 'String'
  writeFile :: 'FilePath' -> 'String' -> m ()
  __withFile :: 'FilePath' -> 'System.IO.IOMode' -> ('System.IO.Handle' -> m a) -> m a__
@

If you try to lift @withFile@ the same way you will find it does not work. Why not? The answer stems
from the @('System.IO.Handle' -> m r)@ argument. Because there are uses of @m@ in the arguments to
the function, not just in the result (or more precisely, uses of @m@ in negative positions), lifting
@withFile@ also requires “lowering” the action produced by the callback. This kind of effect is
called a /higher-order/, or /scoped/, effect.

The 'MonadTransControl' class from the @monad-control@ package is designed to lift higher-order
effects. While 'MonadTrans' provides the power to 'lift' actions, 'MonadTransControl' provides the
additional power to lower certain actions in the process.

To update the @FileSystem@ instance for 'EffT', it is necessary to use the more powerful 'sendWith'
operation to implement @withFile@. 'sendWith' accepts two arguments instead of one: the first
argument specifies how to run the action in the current monad, if it supports handling the effect,
while the second argument specifies how to lift the action into the underlying monad, doing any
lowering that may be necessary along the way. In this particular case, the method implementation
looks like this:

@
  withFile path mode f = 'sendWith' \@FileSystem
    (writeFile path mode ('runEffT' '.' f))
    ('controlT' '$' \\lower -> writeFile path mode (lower '.' 'runEffT' '.' f))
@

A full explanation of 'MonadTransControl' is outside the scope of this documentation; see the
documentation for "Control.Monad.Trans.Control" for more details. -}

{-$handling_effects

In @eff@, effect handlers are encoded as monad transformers. The core, primitive effects of @eff@
are therefore implemented as unique monad transformers that provide implementations of different
effects. However, in practice, most custom handlers do not need to define their own monad
transformers, as they can be defined in terms of the existing effect handlers already provided by
@eff@.

To provide a concrete example, consider the hypothetical @FileSystem@ effect defined in the previous
section on defining new effects. To keep things simple, we will not handle the higher-order
@withFile@ operation, as the complexity it adds is not any different from the complexity already
covered. That leaves us with the following effect:

@
class 'Monad' m => FileSystem m where
  readFile :: 'FilePath' -> m 'String'
  writeFile :: 'FilePath' -> 'String' -> m ()
@

== Defining impure effect handlers

To implement an effectful version of this handler that actually interacts with the real filesystem,
the implementation can trivially defer to "System.IO".'readFile' and "System.IO".'writeFile', which
do all the actual work. All that is necessary is to write a small bit of glue code to connect the
two together.

To do that, start by defining a new, unique “tag” type that will provide a name for the new handler.
The actual name of the type is irrelevant, and it does not need to be inhabited; its only purpose is
as a unique tag at the type level:

@
data FileSystemIO
@

Next, define @FileSystemIOT@ as an alias for 'HandlerT' applied to the unique tag:

@
type FileSystemIOT = 'HandlerT' FileSystemIO '[]
@

The empty list provided as the second argument to 'HandlerT' is explained in the second below, but
it is not relevant just yet. For now, just define an ordinary instance of @FileSystem@ for
@FileSystemIOT@:

@
instance 'MonadIO' m => FileSystem (FileSystemIOT m) where
  readFile path = 'liftIO' '$' "System.IO".'readFile' path
  writeFile path contents = 'liftIO' '$' "System.IO".'writeFile' path contents
@

The next step is to teach @eff@ that @FileSystemIOT@ is a handler for the @FileSystem@ effect, as
there is no way for @eff@ to automatically detect the presence of the new @FileSystem@ instance. To
do this, define a new instance of the 'Handles' type family:

@
type instance 'Handles' FileSystemIOT eff = eff 'Data.Type.Equality.==' FileSystem
@

This instance can be read as saying “@FileSystemIOT@ is a handler for some effect @eff@ /if and only
if/ @eff@ is @FileSystem@.” The precision is important, as @eff@ needs to know for certain that it
does not handle any /other/ effects so that it can lift them properly. (A handler can, if it wants,
handle multiple different effects.)

With both the @FileSystem@ and 'Handles' instances in place, all that’s left to do is to define a
@runFileSystemIO@ function that can be used to actually handle the effect:

@
runFileSystemIO :: 'EffT' FileSystemIOT m a -> m a
runFileSystemIO = 'runHandlerT' '.' 'runEffT'
@

You may note that this function does not really do any “running” at all; both 'runEffT' and
'runHandlerT' do nothing more than unwrap the 'EffT' and 'HandlerT' newtypes, respectively. The real
purpose of the @runFileSystemIO@ is to guide the type system to select the @FileSystem@ instance for
@FileSystemIOT@, nothing more.

There is nothing left to do: this effect handler is now fully-functional! To use it, write a
function that uses the @FileSystem@ effect and run it as you would any other effect:

@
copyFile :: FileSystem m => 'FilePath' -> 'FilePath' -> m ()
copyFile inPath outPath = do
  contents <- readFile inPath
  writeFile outPath contents

copyFileIO :: 'MonadIO' m => 'FilePath' -> 'FilePath' -> m ()
copyFileIO inPath outPath = runFileSystemIO '$' copyFile inPath outPath
@

== Defining pure effect handlers

The @runFileSystemIO@ handler might feel like cheating, since it didn’t actually do anything—it just
deferred to the existing implementations. To provide a more complicated example, we’ll implement a
pure handler for @FileSystem@ that uses a fake, in-memory filesystem instead of the real one. (This
could be useful for unit testing, for example.)

The process for defining this new handler is largely the same, so once again, start by defining a
new type-level tag for the effect:

@
data FileSystemPure
@

The next step is to define a @FileSystem@ instance, but this time, the instance won’t use 'MonadIO'.
Instead, it will delegate to two different effets: a 'State' effect to store the virtual filesystem
and a 'Error' effect to handle errors. In this case, the @FileSystemPureT@ handler should keep the
'State' effect “private”—it should be an implementation detail of the handler that does not leak out
into calling code—but the 'Error' effect should defer the choice of handler to the caller. This is
where the second argument to 'HandlerT' comes in. Any “private” effect handlers should go in that
list, so @FileSystemPureT@ can be defined as follows:

@
-- | A mapping from file paths to file contents.
type VirtualFileSystem = [('FilePath', 'String')]

type FileSystemPureT = 'HandlerT' FileSystemPure '['StateT' VirtualFileSystem]
type instance 'Handles' FileSystemPureT eff = eff 'Data.Type.Equality.==' FileSystem
@

The “public” effects are not specified on the handler type itself, as they are attached to the
handler instances themselves (like 'MonadIO' was attached to the @FileSystem@ instance for
@FileSystemIOT@). Here is the instance for @FileSystemPureT@:

@
instance 'Error' 'String' m => FileSystem (FileSystemPureT m) where
  readFile path = 'HandlerT' '$' do
    fileSystem <- 'get'
    case 'lookup' path fileSystem of
      'Just' contents -> 'pure' contents
      'Nothing'       -> 'throw' ("readFile: no such file " '<>' path)

  writeFile path contents = 'HandlerT' '$' do
    fileSystem <- 'get'
    -- add the new file and remove an old file with the same name, if it exists
    'put' ((path, contents) : 'filter' (('/=' path) '.' 'fst') fileSystem)
@

Finally, we define the handler function. This handler function will be a little more interesting
than @runFileSystemIO@ because it will discharge the @('State' VirtualFileSystem)@ effect /locally/,
keeping the implementation details of the @FileSystemPure@ handler hidden:

@
runFileSystemPure :: 'EffT' ('HandlerT' FileSystemPure) m a -> m a
runFileSystemPure = 'evalState' [] '.' 'runHandlerT' '.' 'runEffT'
@

This demonstrates an important capability of effect handlers: not only are they modular, they don’t
all have to be run together at once. This allows @runFileSystemPure@ to handle the 'State' effect
locally but pass the 'Error' effect on to its caller. The capability allows handlers to be reused to
define other effects without leaking their implementation details. -}
