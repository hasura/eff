# `eff` — screaming fast extensible effects for less [![Build Status](https://travis-ci.org/hasura/eff.svg?branch=master)](https://travis-ci.org/hasura/eff) [![Documentation](https://img.shields.io/static/v1?label=docs&message=0.0.0.0&color=informational)][docs]

**🚧 This library is currently under construction. 🚧**

`eff` is a work-in-progress implementation of an *extensible effect system* for Haskell, a general-purpose solution for tracking effects at the type level and handling them in flexible ways. Compared to other effect systems currently available, `eff` differentiates itself in the following respects:

  - `eff` is **really fast**. Built on top of low-level primitives added to the GHC RTS to support capturing slices of the call stack, `eff` is performant by design. Using a direct implementation of delimited control allows it to be fast without relying on fickle compiler optimizations to eliminate indirection.

    Traditional effect system microbenchmarks fail to capture the performance of real code, as they are so small that GHC often ends up inlining everything. In real programs, GHC compiles most effect-polymorphic code via dictionary passing, not specialization, causing the performance of other effect systems to degrade beyond what microbenchmarks would imply. `eff` takes care to allow GHC to generate efficient code without the need for whole-program specialization.

  - `eff` is **low-boilerplate** and **easy to use**, even without Template Haskell or any generic programming. `eff`’s interface is comparable to `freer-simple` and `polysemy`, but writing new effect handlers is made even simpler thanks to a small set of highly expressive core operations.

  - `eff` is **expressive**, providing support for both first-order/algebraic effects and higher-order/scoped effects, like `fused-effects` and `polysemy` (but unlike `freer-simple`).

  - `eff`’s semantics is **precise** and **easy to reason about**, based on models of delimited control. Other approaches to scoped operations (including those taken in `mtl`, `fused-effects`, and `polysemy`) have behavior that changes depending on handler order, and some combinations can lead to nonsensical results. `eff`’s semantics is consistent regardless of handler order, and scoped operations compose in predictable ways.

## `eff` in action

To illustrate just how easy it is to define and handle effects in `eff`, the following code example includes 100% of the code necessary to define a custom `FileSystem` effect and two handlers, one that runs in `IO` and another that uses an in-memory virtual file system:

```haskell
import qualified System.IO as IO
import Prelude hiding (readFile, writeFile)
import Control.Effect

-- -----------------------------------------------------------------------------
-- effect definition

data FileSystem :: Effect where
  ReadFile :: FilePath -> FileSystem m String
  WriteFile :: FilePath -> String -> FileSystem m ()

readFile :: FileSystem :< effs => FilePath -> Eff effs String
readFile = send . ReadFile

writeFile :: FileSystem :< effs => FilePath -> String -> Eff effs ()
writeFile a b = send $ WriteFile a b

-- -----------------------------------------------------------------------------
-- IO handler

runFileSystemIO :: IOE :< effs => Eff (FileSystem ': effs) a -> Eff effs a
runFileSystemIO = handle \case
  ReadFile path -> liftH $ liftIO $ IO.readFile path
  WriteFile path contents -> liftH $ liftIO $ IO.writeFile path contents

-- -----------------------------------------------------------------------------
-- pure handler

runFileSystemPure :: Error String :< effs => Eff (FileSystem ': effs) a -> Eff effs a
runFileSystemPure = swizzle
  >>> handle \case
        ReadFile path -> liftH do
          fileSystem <- get
          case lookup path fileSystem of
            Just contents -> pure contents
            Nothing       -> throw ("readFile: no such file " <> path)
        WriteFile path contents -> liftH do
          fileSystem <- get
          -- add the new file and remove an old file with the same name, if it exists
          put ((path, contents) : filter ((/= path) . fst) fileSystem)
  >>> evalState @[(FilePath, String)] []
```

That’s it. For a thorough explanation of how the above example works, [see the `eff` documentation][docs].

## Implementation status

`eff` is a work in progress, and since it requires changes to the GHC RTS, you cannot use it yet on any released version of GHC. If there is interest, I can try to provide builds of GHC with the necessary changes to use `eff`, but otherwise you will need to wait for them to be merged into GHC proper before using `eff` yourself.

Looking beyond that, many things are still not yet implemented. More work needs to be done to properly interoperate with `IO` exceptions, and the set of built-in effects currently provided is very small. However, all the existing functionality works, and it has been designed to support extensions, so I do not anticipate any difficulty supporting them.

This library is also sorely lacking a benchmark suite. I have a small set of microbenchmarks I have been using to test out various scenarios and edge cases of different effect libraries, but they need to be cleaned up and added to this repository, and a set of less synthetic benchmarks are also important to assess real-world performance. **If you have a small but non-trivial program where differences in effect system performance are significant, I would be much obliged if you could share it to build a more realistic set of effect system benchmarks.**

## Acknowledgements, citations, and related work

All code in `eff` is original in the sense that it was not taken directly from other libraries, but much of it is directly inspired by the existing work of many others. The following is a non-exhaustive list of people and works that have had a significant impact, directly or indirectly, on `eff`’s design and implementation:

  - Oleg Kiselyov, Amr Sabry, and Cameron Swords — [Extensible Effects: An alternative to monad transfomers][oleg:exteff]
  - Oleg Kiselyov and Hiromi Ishii — [Freer Monads, More Extensible Effects][oleg:more]
  - Rob Rix, Patrick Thomson, and other contributors — [`fused-effects`][gh:fused-effects]
  - Sandy Maguire and other contributors — [`polysemy`][gh:polysemy]

[docs]: https://hasura.github.io/eff/Control-Effect.html
[gh:fused-effects]: https://github.com/fused-effects/fused-effects
[gh:polysemy]: https://github.com/polysemy-research/polysemy
[oleg:exteff]: http://okmij.org/ftp/Haskell/extensible/exteff.pdf
[oleg:more]: http://okmij.org/ftp/Haskell/extensible/more.pdf
