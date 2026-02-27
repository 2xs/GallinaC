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

## Where to find what

Here is an overview of the available different modules:

- `corec/`: Utilities to define partial (co)recursive functions, from [Formal Definitions and Proofs for Partial (Co)Recursive Functions](https://www.sciencedirect.com/science/article/abs/pii/S2352220824000531)
