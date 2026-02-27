# GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq

> System programming demands strong correctness guarantees, yet verification
> remains challenging due to low-level memory manipulation and the gap between
> source-level reasoning and compiled code. We present GallinaC, a framework
> that unifies verification and certified compilation of system
> programs. GallinaC is a shallow, monadic embedding of a C-like language into
> Gallina, the specification language of the Rocq Prover. This enables programs
> to be written and verified directly in a single setting, without introducing a
> separate syntactic representation. We equip GallinaC with a separation logic
> expressed in Gallina, supporting modular reasoning about memory and stateful
> computations. To connect reasoning with execution, we define both denotational
> and operational semantics and prove their agreement. We build a certified
> compilation pipeline on top of CompCert, ensuring that verified properties are
> preserved down to executable code. By integrating programming, verification,
> and compilation, GallinaC reduces the gap between code and proofs and enables
> source-level optimizations, including a more exhaustive tail-call optimization
> than CompCert's.

## State of the project

This repository contains the Rocq development of GallinaC. Files are added
regularly, as they are cleaned-up for publication.

## Usage

### Programming

To create an environment adapted for writing GallinaC programs, simply run

```Rocq
From GallinaC Require Import Programming
```

This will require all subpackages as needed and import them. Moreover, syntax
scopes are also opened.

## Where to find what

Here is an overview of the different modules:

- `theories/gallinac/` Entry module
  - `Programming.v`: Export modules required for programming
- `theories/corec/`: Utilities to define partial (co)recursive functions, from [Formal Definitions and Proofs for Partial (Co)Recursive Functions](https://www.sciencedirect.com/science/article/abs/pii/S2352220824000531)
- `theories/utils/`: Various utilities
  - `Algebra.v`: Separation algebras as defined in [Local Action and Abstract Separation Logic](https://ieeexplore.ieee.org/abstract/document/4276580/)
  - `GenId.v`: Identifier generation following a separation algebra
  - `*Ext.v`: Various additions to existing Rocq modules
- `theories/imp/`: Building blocks for shallowly embedded imperative programming
  - `Monad.v`: Our `program` monad with state, failure and non-termination effects
  - `While.v`: Definition of the `while` loop using the `corec` library
  - `Primitives.v`: All GallinaC primitives
  - `PrimitivesProp.v`: Properties of GallinaC primitives
  - `Pointer.v`: Pointer library with provenance tracking
  - `Memval.v`: Values which may be stored in memory
  - `Heap.v`: Heap memory
  - `Store.v`: Store memory
  - `Intops.v`: Building-blocks to extend any type with bounded integer semantics
  - `Uint32.v`: Rocq `nat` type with C-style `uint32_t` semantics
  - `Uintptr.v`: Rocq `N` type with C-style `uintptr_t` semantics
