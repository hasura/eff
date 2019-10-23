# `eff` — screaming fast extensible effects for less [![Build Status](https://travis-ci.org/lexi-lambda/eff.svg?branch=master)](https://travis-ci.org/lexi-lambda/eff)

**🚧 This library is currently under construction. 🚧**

`eff` is a work-in-progress implementation of an *extensible effect system* for Haskell, a general-purpose solution for tracking effects at the type level and handling them in flexible ways. Compared to other effect systems currently available, `eff` differentiates itself in the following respects:

  - `eff` is **really fast**. It is designed specifically to cooperate with the GHC specializer to allow effect handlers to be aggressively optimized, even in highly polymorphic code. Performance should be indistinguishable from `mtl`, slightly faster than `fused-effects`, and significantly faster than `freer-simple`, `polysemy`, and other library based on free or free-like constructions.

    Traditional effect system microbenchmarks fail to capture the performance of real code, as they are so small that GHC often ends up inlining everything. In real programs, GHC compiles most effect-polymorphic via dictionary passing, not specialization, causing the performance of other effect systems to degrade beyond what microbenchmarks would imply. `eff` takes care to allow GHC to generate efficient code without the need for whole-program specialization.

  - `eff` is **low-boilerplate** and **easy to use**, even without Template Haskell or any generic programming. Effects in `eff` are just ordinary typeclasses on monads, just like in `mtl`, and a small bit of extra information is maintained in the type system to guide instance selection to eliminate the need for any overlapping instances. Defining effect handlers in terms of existing handlers does not require defining any new monad transformers.

  - `eff` is **expressive**, providing support for both first-order/algebraic effects and higher-order/scoped effects, like `fused-effects` and `polysemy` (but unlike `freer-simple`).

  - `eff` **integrates well** with the existing `transformers` ecosystem. Effect handlers in `eff` are ordinary monad transformers, and many built-in effects are handled by the ordinary transformers from the `transformers` package. As in `fused-effects`, existing transformers can be easily adapted into effect handlers, but `eff` goes a step further by allowing existing `mtl`-style typeclasses to be used as effects, just by defining a couple small instances.

If you are already familiar with `mtl` and the “`mtl`-style” approach to handling effects, `eff` may be approximately described as “`mtl` but without the quadratic instances problem.”

## `eff` in action

To illustrate just how easy it is to define and handle effects in `eff`, the following code example includes 100% of the code necessary to define a custom `FileSystem` effect and two handlers, one that runs in `IO` and another that uses an in-memory virtual file system:

```haskell
import Prelude hiding (readFile, writeFile)

import qualified System.IO as IO

import Control.Effect
import Control.Effect.Error
import Control.Effect.State
import Control.Monad.IO.Class
import Data.Functor.Identity

-- ------------------------------------------------------------------
-- the FileSystem effect

class Monad m => FileSystem m where
  readFile :: FilePath -> m String
  writeFile :: FilePath -> String -> m ()

instance (Monad (t m), Send FileSystem t m) => FileSystem (EffT t m) where
  readFile path = send @FileSystem (readFile path)
  writeFile path contents = send @FileSystem (writeFile path contents)

-- ------------------------------------------------------------------
-- the FileSystemIOT handler

data FileSystemIO
type FileSystemIOT = HandlerT FileSystemIO '[]
type instance Handles FileSystemIOT eff = eff == FileSystem

instance MonadIO m => FileSystem (FileSystemIOT m) where
  readFile path = liftIO $ IO.readFile path
  writeFile path contents = liftIO $ IO.writeFile path contents

runFileSystemIO :: EffT FileSystemIOT m a -> m a
runFileSystemIO = runHandlerT . runEffT

-- ------------------------------------------------------------------
-- the FileSystemPureT handler

-- | A mapping from file paths to file contents.
type VirtualFileSystem = [(FilePath, String)]

data FileSystemPure
type FileSystemPureT = HandlerT FileSystemPure '[StateT VirtualFileSystem]
type instance Handles FileSystemPureT eff = eff == FileSystem

instance Error String m => FileSystem (FileSystemPureT m) where
  readFile path = HandlerT $ do
    fileSystem <- get
    case lookup path fileSystem of
      Just contents -> pure contents
      Nothing       -> throw ("readFile: no such file " <> path)

  writeFile path contents = HandlerT $ do
    fileSystem <- get
    -- add the new file and remove an old file with the same name, if it exists
    put ((path, contents) : filter ((/= path) . fst) fileSystem)

runFileSystemPure :: Monad m => EffT FileSystemPureT m a -> m a
runFileSystemPure = evalState [] . runHandlerT . runEffT
```

That’s it. No Template Haskell, no need to define any new monad transformers, and no need to define any lifting instances for each handler. For a thorough explanation of how the above example works, see the `eff` documentation.

## Implementation status

`eff` is a work in progress, and many things are not yet implemented. The set of built-in effects currently provided is very small, and some key bits of functionality needed to implement a safe `Resource` effect are still missing. However, all the existing functionality works, and it has been designed to support those extensions, so I do not anticipate any difficulty supporting them.

This library is also missing a benchmark suite. I have a small set of microbenchmarks I have been using to test out various scenarios and edge cases of different effect libraries, but they need to be cleaned up and added to this repository, and a set of less synthetic benchmarks are also important to assess real-world performance. **If you have a small but non-trivial program where differences in effect system performance are significant, I would be much obliged if you could share it to build a more realistic set of effect system benchmarks.**

## Acknowledgements, citations, and related work

All code in `eff` is original in the sense that it was not taken directly from other libraries, but the vast majority of it is directly inspired by the existing work of many others. The following is a non-exhaustive list of people and works that have had a significant impact, directly or indirectly, on `eff`’s design and implementation:

  - Oleg Kiselyov, Amr Sabry, and Cameron Swords — [Extensible Effects: An alternative to monad transfomers][oleg:exteff]
  - Oleg Kiselyov and Hiromi Ishii — [Freer Monads, More Extensible Effects][oleg:more]
  - Nicolas Wu, Tom Schrijvers, and Ralf Hinze — [Effect Handlers in Scope][wu:scope]
  - Nicolas Wu and Tom Schrijvers — [Fusion for Free: Efficient Algebraic Effect Handlers][schrijvers:fusion]
  - Andy Gill and other contributors — [`mtl`][hackage:mtl]
  - Rob Rix, Patrick Thomson, and other contributors — [`fused-effects`][gh:fused-effects]
  - Sandy Maguire and other contributors — [`polysemy`][gh:polysemy]

[gh:fused-effects]: https://github.com/fused-effects/fused-effects
[gh:polysemy]: https://github.com/polysemy-research/polysemy
[hackage:mtl]: https://hackage.haskell.org/package/mtl
[oleg:exteff]: http://okmij.org/ftp/Haskell/extensible/exteff.pdf
[oleg:more]: http://okmij.org/ftp/Haskell/extensible/more.pdf
[schrijvers:fusion]: https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/mpc2015.pdf
[wu:scope]: https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
