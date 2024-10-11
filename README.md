# Implementation of Absence-Aware Lenses

## How to Run

Prerequisite: Install `GHC` (tested 9.6.5) and `cabal` (>= 3.0) via [ghcup](https://www.haskell.org/ghcup/) or a package management system.

One can test functions provided by loading files via `cabal repl`. For example:

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

The files under `src/MALens/Examples` contains more interesting examples. For example, `src/MALens/Examples/MapKeyT.hs` contains the key-based mapping example mentioned in the paper.

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

### Files under `src`

- `Domain.hs` Definitions of type classes that represent structures of posets.
- `Err.hs` Definition of a monad used for error-reporting. 
- `MALens.hs` Main definition of absence-aware lenses and combinators. 
- `MALensTH.hs` Template Haskell to avoid tedious manipulation of pairs. 
- `SymmetricLens.hs` (WIP, not in the paper) Symmetric lenses expressed in the framework.
- `MALens/Examples/Dup.hs` Examples regarding duplications
- `MALens/Examples/List.hs` Examples regarding lists (including examples in Section 5.1 and 5.2)
- `MALens/Examples/MapKeyT.hs` Examples of `mapKey` (Section 5.3)
- `MALens/Examples/Snapshotting.hs` Unstructured examples of `snapshot`, which contains the preliminary versions of `mapKey`.
