# Prototype Implementation of Partial-State Lenses

This code accompanies our ESOP 2026 paper "Lenses for Partially-Specified States".

## Prerequisites

Ensure you have the following installed:

* GHC (tested 9.6.5, 9.6.6, 9.6.7, and 9.14.1; thus 9.8, 9.10 and 9.12 would also work)
* cabal (version 3.0 or later)

These can be installed using [ghcup](https://www.haskell.org/ghcup/) or your distribution's package manager.

## Running the Code

To test the provided functions, use `cabal repl` to start `ghci`. (This implementation does not provide executables, and thus `cabal run` does not work.)

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

More examples are available in `src/PSLens/Examples/Tasks.hs`, which implements the task list example discussed in Sections 2 and 4 of the paper. The following demonstrates how to reproduce the execution results discussed in Section 2.

```haskell
ghci> :load PSLens.Examples.Tasks
...
ghci> import Err
...
ghci> originalTasks -- defined in PSLens.Examples.Tasks
Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0))]}
ghci> printTasks originalTasks
1  False  Buy milk  +1
2  True   Walk dog  +0
3  False  Jog       +0
ghci> get lTasks originalTasks -- lTasks is defined in PSLens.Examples.Tasks
Ok (ProperTasks (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(3,(False,"Jog",0))]}),ProperTasks (Tasks {getTasks = fromList [(2,(True,"Walk dog",0)),(3,(False,"Jog",0))]}))
ghci> printDTPair =<< execErr (get lTasks originalTasks)
1  False  Buy milk  +1
3  False  Jog       +0

2  True   Walk dog  +0
3  False  Jog       +0
ghci> -- Example in Section 2.3
ghci> dOG -- defined in PSLens.Examples.Tasks
PartialTasks (PTasks {addReq = Tasks {getTasks = fromList [(4,(False,"Buy egg",0))]}, delReq = [], compReq = COnGoing (Tasks {getTasks = fromList []}), postReq = POnGoing})
ghci> printDT dOG -- w_og in the paper 
4  False  Buy egg  +0  (+)
ghci> put lTasks originalTasks (dOG , least)
Ok (Tasks {getTasks = fromList [(1,(False,"Buy milk",1)),(2,(True,"Walk dog",0)),(3,(False,"Jog",0)),(4,(False,"Buy egg",0))]})
ghci> printTasks =<< execErr (put lTasks originalTasks (dOG , least))
1  False  Buy milk  +1
2  True   Walk dog  +0
3  False  Jog       +0
4  False  Buy egg   +0
ghci> printDT dDT -- w_dt in the paper 
2                      (-)
3  False  Stretch  +0  (+)
ghci> printTasks =<< execErr (put lTasks originalTasks (dOG , dDT)) -- s''_tl in the paper
1  False  Buy milk  +1
3  False  Stretch   +0
4  False  Buy egg   +0
ghci> printDTPair =<< execErr (get lTasks =<< put lTasks originalTasks (dOG , dDT)) -- v''_og and v''_dt in the paper
1  False  Buy milk  +1
3  False  Stretch   +0
4  False  Buy egg   +0

3  False  Stretch  +0
4  False  Buy egg  +0
ghci> -- Example in Section 2.4
ghci> printDT dOGc -- Fig. 3 in the paper 
1                 (-)
3  True  Jog  +0  (C)
ghci> printTasks =<< execErr (put lTasks originalTasks (dOGc, least))
2  True  Walk dog  +0
3  True  Jog       +0
```

## File Overview

The project files are structured as follows:

* `src/Domain.hs` Type classes for i-poset structures. No ordering definitions, as they are only relevant in laws.
* `src/Err.hs` A monad for error reporting.
* `src/PSLens.hs` The main definition of partial-state lenses and their combinators, including those not mentioned in our paper.
* `src/PSLensTH.hs` Template Haskell to simplify pair manipulation (not mentioned in the paper).
* `src/PSLens/Examples/Tasks.hs` Task list examples (Sections 2 and 4)

## Notable Differences from the Paper

The code `src/PSLens/Examples/Tasks.hs` only implements the elaborated version discussed in Section 4.5. One can mimic the behavior of the non-elaborated version by setting completion/postponing requests to empty. For simplicity, we use `Int` for due dates.
