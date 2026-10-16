# Deep GallinaC

Deep GallinaC is a *reification* of the shallow GallinaC used for
programming. Hence, both languages are close in many regards. This file
discusses certain more tricky aspects.

## Scopes

In a monadic language, scopes are very dynamic. The code below is totally
valid. However, it poses an issue when reifying. Indeed, it could be tempting to
just "leave" the garbage data in the reified environment. However, this breaks
subject reduction (evaluation from a well-typed state yields a well-typed
state), making proofs in `Agree` impossible. To remedy this, deep GallinaC
introduces a special `Kscope` continuation that removes old values when it is
encountered. A similar issue arises with store variables introduced by
`with_var` and is also handled by `Kscope`.

```
do x <-
  do y <- f;
  g y;
do y <-
  do y <- h x;
  do x <- i y;
  j x;
k y
```

## Lack of tail calls

Deep does not feature tail calls. The reifier explicitly replaces them with a
binding `do x <- tail_call_fun; ret x`. This helps the proofs in `Agree` as it
makes it explicit when `Kscope` pops happen. IR re-introduces them later.

In addition, due to how Deep GallinaC's semantics is defined, commands `c_if`
and `c_with_var` are also problematic: both propagate tail position into their
sub-commands (`step_ifthenelse` keeps the continuation, and `step_with_var`
only pushes a `Kscope` continuation), so a call there may be in tail position
too.

The reifier therefore tracks tail position with a `tail` flag threaded through
`translate_cmd`. At the function body root, it starts as `true`. The `c_if`
branches, `c_with_var` body and `c_bind` continuation (right argument) pass it
through. The left `c_bind` command and `while`'s cond/body set it to false. Upon
reaching a `c_app`, the reifier wraps the call in a bind using `wrap_tail_call`
iff `tail` is `true`. Hence, only true tail-calls are wrapped.

Note that the issue with `c_with_var` isn't that the function call gets
stuck. It's about when the function returns, as popping the `Kscope` works, but
then reaches `Kcall`/`Kstop`.
