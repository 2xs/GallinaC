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

## Installation

You will need Rocq, CompCert and MetaRocq installed on your machine. Due to our
depencencies, Rocq version must be 9.0 or 9.1. As of time of writing, the newest
CompCert is 3.17. Pins help make sure that updates don't break the installation.

The commands below should create a fresh switch without issues. Just note that
in particular MetaRocq takes quite a while to compile.

```Bash
opam switch create gallinac 4.12
opam install rocq-prover rocq-core=9.1.1
opam pin add rocq-core 9.1.1
opam pin add coq-compcert 3.17
opam install rocq-metarocq-utils rocq-metarocq-quotation rocq-metarocq-template
```

Afterwards, you can compile the project using `make` and evalutate the compiler

```Bash
make # Builds the project itself -j might speed things up
make examples # Run the examples
make extraction # Extract the example reverse program
make reversec # Build the binary that compiles the extracted program into assembly
make reverse # Build the final assembly
./reverse # Execute the reverse example
```

## Usage

### Programming

To create an environment adapted for writing GallinaC programs, simply run:

```Rocq
From GallinaC Require Import Programming.
```

This will require all subpackages as needed and import them. Moreover, syntax
scopes are also opened. See file `theories/examples/Reverse/Reverse.v` for an
example.

### Compilation

Once your desired program is ready for compilation, you can similarly import all
necessary modules using a single import:

```Rocq
From GallinaC Require Import Compiler.
```

Compilation tooling isn't quite refined yet (there is no single command to
compile your program), but the `Reverse` example shows all necessary steps. They
are summarized below.

1. Reify your program with `MetaRocq Run (reify_program "My.Module.Path" "main" "my_reified_program).`. A GallinaC program is a module containing all relevant declarations. Functions called outside this module are **not** reified. Instead, they are will be declared as `extern`.
2. Extract a code generator, see the complete list of necessary commands in `ReverseExtraction.v`
3. Compile and run the code generator to obtain the assembly
4. Compile and link the assembly with your program

## Where to find what

Here is an overview of the different modules:

- `theories/Programming.v`: Export modules required for programming
- `theories/Compiler.v`: Export modules required for compiling
- `examples/Reverse` Example with in-place linked-list reversal
  - `Reverse.v`: Definition of the `reverse` program
  - `ReverseExecution.v`: Illustrates evaluations of GallinaC programs
  - `ReverseReify.v`: Reifies the `reverse` into a deep embedding of GallinaC
  - `ReverseOpSem.v`: Executes reified `reverse` program using an operational semantics using the CompCert framework
  - `ReverseExtraction.v`: Extracts a code generator for the `reverse` program
- `theories/Corec/`: Utilities to define partial (co)recursive functions, from [Formal Definitions and Proofs for Partial (Co)Recursive Functions](https://www.sciencedirect.com/science/article/abs/pii/S2352220824000531)
- `theories/Utils/`: Various utilities
  - `Algebra.v`: Separation algebras as defined in [Local Action and Abstract Separation Logic](https://ieeexplore.ieee.org/abstract/document/4276580/)
  - `GenId.v`: Identifier generation following a separation algebra
  - `*Ext.v`: Various additions to existing Rocq modules
- `theories/Imp/`: Building blocks for shallowly embedded imperative programming
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
  - `Model.v`: Canonical model of heap and store memories
- `theories/Compiler/`: Compilation of GallinaC using CompCert
  - `Common`: Shared definitions throughout the compiler
  - `Reify`: Reification of (shallow) GallinaC into a deep embedding
  - `Deep`: Deep embedding of GallinaC
  - `IR`: An intermediate language between (deep) GallinaC and Cminor (CompCert's backend entry language)
  - `Passes`: Compilation passes and their proofs
