# Working on GallinaC

This file contains a collection of tips and guidance when working on the
GallinaC code base. More detailed docs may be available in `docs/`.

# Base assumptions

This file assumes that an opam switch named `gallinac` is installed, see
`README.md` for details.

# Project Layout

In `theories/` you will find the main development. All modules within reside
within the `GallinaC` prefix. At its root, you will find
`theories/Programming.v`, `theories/Compiler.v` and
`theories/Proving.v`. Consumers of GallinaC can simply `Require Import` these
modules to pull everything in scope as appropriate.

In `examples/` you will find examples. These reside in the `GallinaC.Examples`
prefix.

# Project Architecture

## Corecursion dependency

Module `theories/Corec` contains facilities to define (co-)recursive functions
without having to rely on Rocq's termination checker. In particular, we
construct a fuel-free `while` loop using it.

This module is imported from another project. Do not modify it, unless you
receive explicit permission (and even then, you probably shouldn't).

## Diverse utilities

Module `theories/Utils` provides various utilities.

### Separation algebras `theories/Utils/Algebra.v`

Separation algebras describe things which may be "separated", the definition
builds up from a "join" operation. Two elements being disjoint means simply that
their join succeeds.

From this simple definition, the behaviour of numerous different objects can be
defined, most notably heaps, stores and resource access.

A quite simple example of separation algebra is provided in
`theories/Utils/Excl.v`.

All details are available in [Local Action and Abstract Separation
Logic](https://ieeexplore.ieee.org/abstract/document/4276580/)

### Extension modules

The various `theories/Utils/*Ext.v` files contain extensions to types defined in
the standard library or other dependencies.

## Imperative building blocks

Module `theories/Imp` contains all building blocks for imperative
programming. The monad definition is in `theories/Imp/Monad.v`. Primitive
operations are defined in `theories/Imp/Primitives.v` with some properties
defined in `theories/Imp/PrimitivesProp.v`. The `while` loop is defined in
`theories/Imp/While.v`.

Bounded integers are defined in `theories/Imp/Intops.v` with canonical instances
defined in `theories/Imp/Uint32.v` and `theories/Imp/Uintptr.v`.

Imperative memory is defined in `theories/Imp/Memory.v`,
`theories/Imp/RWMemory.v`, `theories/Imp/Heap.v`, `theories/Imp/Store.v`,
`theories/Imp/State.v` and `theories/Imp/Value.v` with canonical instances in
`theories/Models/`.

## Separation logic

A module for separation logic is available in `theories/Seplog`.

## Compilation

Compilation of the shallow GallinaC is defined in module
`theories/Compiler`. Compilation is multi-staged and relies on MetaRocq and
CompCert.

### Reification

To be able to compile a GallinaC program, it first needs to be *reified* into a
deep embedding, i.e. an inductive. This is achieved via MetaRocq. Using
MetaRocq's template monad, it is possible to recurse directly on the terms,
allowing the "pattern match" on e.g. `bind` to construct `c_bind`.

The reification pass is defined in `theories/Compiler/Reify`.

The resulting deep GallinaC is defined in `theories/Compiler/Deep`.

### Compilation to IR

Deep GallinaC is designed to be very close to shallow GallinaC. Doing a
single-pass compilation to GallinaC would be (proof-wise) too complex. Hence, a
compilation pass first lowers the Deep GallinaC to an Intermediate
Representation (IR). This language is very close to Deep GallinaC, however it
contains "pre-computed" values (e.g. offsets of stack variables) which make it
closer to Cminor.

Note: An `IR` rewrite is scheduled. Some definitions may be removed.

The compilation pass is defined in `theories/Compiler/Passes/IRgen.v`.

The resulting IR is defined in `theories/Compiler/IR`.

### Optimization passes

IR is well-adapted to perform type-directed optimization passes. Currently, a
tail-call optimization is performed before Cminor generation.

### Compilation to Cminor

The final stage of the GallinaC compiler frontend is the generation of the
Cminor code. Cminor is the entrance of the CompCert backend. It is very
low-level, but there still exists a couple things which are handled "for free",
most notably function prologues and epilogues.

The compilation pass is defined in `theories/Compiler/Passes/Cminorgen.v`.

### Compilation safety

To recap, compilation happens in three stages: Reification, IR translation,
Cminor translation.

Defining compilation passes doesn't immediately mean that these passes are
correct. CompCert provides a framework to prove that compilation passes are
correct. However, it only works on "deep" embeddings.

To prove the correctness of the reification, we must prove a semantic
equivalence between the shallow and deep GallinaC. To do this, we first equip
deep GallinaC with an operational semantics (necessary anyway for CompCert). In
addition, we define a *denotation* of deep GallinaC back into the shallow
GallinaC. Then, we prove that one evaluation step in the operational semantics
does not change the result of denotation, i.e. `forall s s', WT s -> step s s'
-> WT s' /\ denote s = denote s'`.  See `docs/SemanticEquivalence.md` for
details.

The compilation safety of the deep passes follows a similar pattern. Here
however, as there is no denotation, matching relations guide the preservation of
equivalence across evaluation steps, i.e. `forall s s' t, step s s' -> matching
s t -> exists t', steps t t' /\ matching s' t'`. The target language may perform
multiple evaluation steps, hence the `steps`.

# Building files

A `Makefile` handles the build process, under the hood `coq_makefile` generates
sub-Makefiles which take care of the dependencies.

As dependency-tracking is slightly brittle, it is recommended to run this
sequentially, e.g. `make && make examples && make extraction && make reversec &&
make reverse && ./reverse` for a full build.

Dependency-tracking seems slightly brittle with the Rocq-generated Makefile. If
it seems that `make` terminates abnormally early (some files were not
regenerated), or some files still reuse an earlier version of a file (through
its `.vo`), simply run `make deepclean` before rerunning `make`. This should
trigger a full rebuild from scratch.

## CI

There is some basic CI infrastructure. File `Containerfile` builds an image able
to build the project and `.gitlab-ci.yml` contains CI instructions to use that
image to perform a full build. See `docs/CI.md` for details.

## Building the project

`make`

## Building a single file

To build `path/to/myfile.v` (and all its dependencies) run

`make path/to/myfile.vo`

## Building the examples

`make examples`

## Extract OCaml code generator from the Reverse example

`make extraction`

Files which trigger extraction are not built unless you run `make extraction`.
See for instance `_RocqExamples` where `ReverseExtraction.v` is excluded from
the file.

## Compile the OCaml code generator that generates the assembly

`make reversec`

## Build the final binary

`make reverse`

## Execute the compiled reverse example

`./reverse`

## Clean the project

`make clean`

## Clean the project and remove all intermediate files

`make deepclean`

# Code style

## Implicit arguments

Prefer non-maximal inserted arguments (`[A]`) over maximally inserted arguments
(`{A}`). Obviously, use maximally inserted implicit arguments when the tail
argument would be implicit, e.g. the `get` primitive of the State monad.

# Proof style

## Axioms

This development imports some axioms which should not introduce inconsistencies.
However, they should only be used transitively. Only specific files are allowed
to use them explicitly. See `docs/Axioms.md` for details.

## Hypotheses names

Prefer `ALLCAPS` names for hypotheses, e.g. `forall n (LT: 0 < n), ...`. When
appropriate, a small number of lower case letters may be appropriate,
e.g. `forall x y z (LExy: x <= y) (LEyz: y <= z), x <= z`.

See `docs/Style.md` for more specific instructions on how to name things.

# Finding dependencies

If you want to find a file defining a Rocq module of a dependency, you can use
`opam show`:

```
opam show --list-files <dependency> | grep <regexp>
```

A concrete example, finding the `Maps` module of CompCert:

```
opam show --list-files coq-compcert | grep Maps
```
