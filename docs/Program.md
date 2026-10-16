# Program model

## The `program` Monad (`theories/Imp/Monad.v`)

This monad incorporates state, failure and non-termination effects. Its definition is `program S A = S -> option (outcome (A * S))` where `S` is the type of the state and `A` is the return type of the monadic computation, assuming it doesn't fail.

The core termination values are:
- `None`: Execution diverged (looped forever)
- `Some Failure`: Execution terminated abnormally with an error
- `Some (Success (a, s'))`: Execution terminated normally with value `a` and new state `s'`

However, one MUST NOT use these values directly. Instead, one should use the provided primitives. The core primitives are:
- `ret a`: Successfully returns pure value `a` and does not change state
- `do x <- m; f`: Perform monadic computation `m`, then if it
  - Diverges, diverge
  - Fails, fail
  - Succeeds with value `a` and new state `s'`, bind `a` to `x` and continue execution with `f` in new state `s'` and where `x` can be used
- `m1;; m2`: Same as `do`, but the result of `m1` is discarded, state changes remain

Additional primitives tailored for system-programming are defined in `theories/Imp/Primitives.v`.

## Memory Model

Memory is split into two parts, a *heap* and a *store*, both implemented as separation algebras. *Memory values* are stored at *locations* which are accessed via *references*.

### Heap

Heaps (`theories/Imp/Heap.v`) provide dynamical memory management, with familiar `alloc` and `free` primitives. Memory is divided in blocks which hold values at various offsets.

### Store

Stores (`theories/Imp/Store.v`) provide static memory management by introducing variables.
