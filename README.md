# Implementation of Absence-Aware Lenses

## Prerequisites

Ensure you have the following installed:

* GHC (tested 9.6.5)
* cabal (version 3.0 or later)

These can be installed using [ghcup](https://www.haskell.org/ghcup/) or your distribution's package manager. 

## Running the Code

To test the provided functions, use `cabal repl` to load the relevant files. For example:

```console
$ cabal repl
... 
ghci> :load src/MALens.hs
...
ghci> get fstL ("a", Some "b")
"a"
ghci> put fstL ("a", Some "b") "c"
Ok ("c",NoneWith [])
```

More examples are available in `src/MALens/Examples`. For example, `src/MALens/Examples/MapKeyT.hs` contains the key-based mapping example mentioned in Section 5.3 of the paper.

```console
$ cabal repl 
...
ghci> :load src/MALens/Examples/MapKeyT.hs 
...
ghci> let s = [("Brown", "CS", 90), ("Smith", "Math", 88), ("Johnson", "CS", 65)]
ghci> put nameScoresKey s (Some [("Smith", 88), ("Brown", 90)])
...
Ok [("Smith","Math",88),("Brown","CS",90)]
```

### File Overview

The project files are structured as follows:

* `src/Domain.hs` Type classes for poset structures. 
* `src/Err.hs` A monad for error reporting. 
* `src/MALens.hs` The main definition of absence-aware lenses and their combinators.
* `src/MALensTH.hs` Template Haskell to simply pair manipulation.
* `src/SymmetricLens.hs` (WIP, not in the paper) Symmetric lenses expressed in the framework.
* `src/MALens/Examples/Dup.hs` Examples regarding duplications
* `src/MALens/Examples/List.hs` List-related examples, including those from Sections 5.1 and 5.2 of the paper.
* `src/MALens/Examples/MapKeyT.hs` Examples of `mapKey` (Section 5.3)
* `src/MALens/Examples/Snapshotting.hs` Unstructured examples of `snapshot`, which contains the preliminary versions of `mapKey`.
