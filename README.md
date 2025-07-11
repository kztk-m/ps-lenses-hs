# Implementation of Partial-State Lenses

This code accompanies the paper "Lenses for Partially-Specified States".

## Prerequisites

Ensure you have the following installed:

* GHC (tested 9.6.5)
* cabal (version 3.0 or later)

These can be installed using [ghcup](https://www.haskell.org/ghcup/) or your distribution's package manager.

## Running the Code

To test the provided functions, use `cabal repl` to start `ghci`

```console
$ cabal repl 
...
ghci> 
```

Then, load the relevant files. No explicit build is required for this command. For example:

```haskell
ghci> :load PSLens
...
ghci> get (constL 42) (Some 3) :: Err Int 
Ok 42 
ghci> put (constL 42) (Some 3) 42 
Ok (NoneWith [])
ghci> put (constL 42) (Some 3) 41 
Err ["constL: non identical update on a constant."]
```

More examples are available in `src/PSLens/Examples`. For example, `src/PSLens/Examples/Tasks.hs` contains the task list example discussed Sections 2 and 4 in the paper.

```haskell
ghci> :load PSLens.Examples.Tasks
...
ghci> originalTasks -- defined in PSLens.Examples.Tasks
Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0))]}
ghci> get lTasks originalTasks -- lTasks is defined in PSLens.Examples.Tasks
Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Jog",0))]}),ProperTasks (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(False,"Jog",0))]}))
ghci> dOG -- defined in PSLens.Examples.Tasks
PartialTasks (PTasks {addReq = Tasks {getTasks = fromList [(4,(False,"Buy egg",0))]}, delReq = [], completeReq = [], postponeReq = fromList []})
ghci> put lTasks originalTasks (dOG , least)
Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]})
```

### File Overview

The project files are structured as follows:

* `src/Domain.hs` Type classes for poset structures.
* `src/Err.hs` A monad for error reporting.
* `src/PSLens.hs` The main definition of absence-aware lenses and their combinators.
* `src/PSLensTH.hs` Template Haskell to simply pair manipulation.
* `src/SymmetricLens.hs` (WIP, not in the paper) Symmetric lenses expressed in the framework.
* `src/PSLens/Examples/Tasks.hs` Tasks list examples (Section 2 and 4)
