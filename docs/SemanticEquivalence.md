# Semantic Equivalence (`theories/Compiler/Deep/Agree.v`)

Denotation by itself (even if it can be verified by a straight-forward
`reflexivity`) does not suffice to validate the correctness of the reification
process. In addition, *semantic equivalence* between the shallow and deep
embeddings needs to be proven.

## Well-behaved reduction

Core to the semantic equivalence theorems is that they operate on reducible
definitions. If the definitions don't reduce, then numerous things break, most
notably reification validity using `reflexivity`. For this reason, most
properties must have computational counterparts that can decide whether they
hold or not.

Taking the example of denotation of expressions, while arbitrary shallow terms
are always well-typed (otherwise the Rocq type checker would refuse them), the
same is not true for arbitrary deep terms. For instance, `e_add e_tt e_tt` is
trivially not well-typed. However, recursion on `Prop`-inhabiting types is quite
tedious and there is always the possibility that somewhere down the line
something breaks reduction.

To never accidentally introduce this issue, all `Prop`-inhabiting types used
during denotation have computational counterparts which are proven to *reflect*
these `Prop`s. Hence, `denote_expr` has signature
`forall [ctx : Maps.PTree.t (type * bool)] [e : expr] [t : type], type_expr ctx e = Some t -> denote_tree denote_binding ctx -> denote_type t`
with structural induction on `e`.

In essence, it recurses directly on the expression term. However, to not have to
define a denotation for not well-typed terms, a typing witness `type_expr ctx e
= Some t` has to be provided. Since `type_expr` fully reduces, this always
reduces to a trivial `eq_refl`. Consistent use of such a discipline then
guarantees that denotation never remains on proof-terms. For instance, use
`reflect_eq_of_true` to construct an equality proof rather than a custom opaque
lemma.

During the proofs of `Agree`, this property is also used. While the proofs
themselves don't need to be transparent or to reduce, they still exploit the
fact that a denoted term (or anything related to denotation) is always
computable. When switching between the computational and `Prop` world is
required, it is always possible to reconstruct them using completeness and
correctness theorems. For instance, `type_expr_complete` produces a `wt_expr`
from a `type_expr` equality, while `type_expr_correct` produces a `type_expr`
equality from a `wt_expr`.

## Correctness of the step relation

First, it must be validated that the `step` relation performs evaluations in a
way compatible with the implicit evaluation performed by the shallow embedding.
Its exact statement is

```
Lemma step_correct {Sm: State.type} (exfs: exf_env)
  [p events s s' t t']
  (WTp: type_program p = true)
  (WTs: wt_state p s)
  (Ts: @Typing.type_state Sm p s = Some t)
  (Ts': Typing.type_state p s' = Some t')
  (STEP: step (Globalenvs.Genv.globalenv p) s events s') :
  denote_state exfs WTp Ts (state_of_state s) = denote_state exfs WTp Ts' (state_of_state s').
```

In simpler terms, it states that:
- For any GallinaC state implementation ([Sm])
- For any extern environment ([exfs])
- For any well-typed program [p] ([WTp])
- For any well-typed state [s] ([WTs] and [Ts])
- If one [step] of evaluation according to the operational semantics is
  performed ([STEP])
- And it yields a well-typed state ([Ts'])

Then the denotations of these states are equal.

This essentially means that the step relation is a reification of the evaluation
semantics of shallow GallinaC.

This can then be generalized to an arbitrary amount of evaluation steps using
`step_star_correct`. Note however that while `step_correct` assumes that `s'` is
well-typed, `step_star_correct` infers it directly from
`OpSem.Typing.step_preservation`.

## Correctness of initial states

Another issue: Is the initial continuation "the right" one? This is
validated by `denote_state_entry`.

```
Lemma denote_state_entry {Sm: State.type} (exfs: exf_env) (p: Prog.program) (f: fundef)
  (args: list Vl) (mem: Sm) (sig_args: list type)
  (WTp: type_program p = true)
  (Ts: OpSem.Typing.type_state p (OpSem.Callstate f args OpSem.Kstop mem) = Some t_nat)
  (WTFD: type_fundef (mk_glob_ctxt p) f = true)
  (SIG: type_funsig f = Some (mk_signature sig_args t_nat)) :
  denote_state exfs WTp Ts
  = denote_fundef_call exfs WTFD SIG (denote_glob_ctxt_of_program exfs p WTp) args.
```

It states that the denotation of an initial state (i.e. calling a function from
the `Kstop` continuation) is equal to directly denoting this function call.

## Correctness of final states

Evaluation in `OpSem` should terminate (provided no divergence or failure) at
`Returnstate (v_nat n) Kstop mem`.  This essentially means that the main
function has returned with some integer.  Lemma `denote_state_final` enforces that
this execution state is equal to a pure `ret n`, i.e. an immediate exit from the
monad.

```
Lemma denote_state_final {Sm: State.type} (exfs: exf_env) (p: Prog.program) (n: nat)
  (mem: Sm) (t: type)
  (WTp: type_program p = true)
  (Ts: OpSem.Typing.type_state p
         (OpSem.Returnstate (v_nat n) OpSem.Kstop mem) = Some t) :
  denote_state exfs WTp Ts = ret n.
```

## End-to-end correctness

With the three lemmas above we know:
- `OpSem.step` is a reification of the monad evaluation
- Initial states correspond to a function call of the "main" function
- Final states correspond to a direct `ret` of the final produced value

However, the first lemma alone is not enough, as it only states that "when
something executes, the denotation remains equal/it reduces towards the same
value". These "executing states" are opaque.

Theorem `denote_initial_final` combines these lemmas together to obtain a proof
of semantic correctness over full program executions. A terminating evaluation of a
deep state is semantically equivalent to calling the `main` function in the
shallow GallinaC: The output value and memory state are equal.

```
Theorem denote_initial_final {Sm: State.type} (exfs: exf_env) (p: Prog.program)
  (s0 s': @OpSem.state Sm) (tr: Events.trace) (r: Integers.int)
  (INIT: OpSem.initial_state p s0)
  (STAR: OpSem.step_star (Globalenvs.Genv.globalenv p) s0 tr s')
  (FINAL: OpSem.final_state s' r) :
  exists (n: nat) (f: fundef)
         (WTp: type_program p = true)
         (WTFD: type_fundef (mk_glob_ctxt p) f = true)
         (SIG: type_funsig f = Some (mk_signature [] t_nat)),
    r = Integers.Int.repr (Z.of_nat n)
    /\ get_global p.(prog_main) (mk_glob_ctxt p) = Some (AST.Gfun f)
    /\ denote_fundef_call exfs WTFD SIG (denote_glob_ctxt_of_program exfs p WTp) []
         (emp_state)
       = Some (Monad.Success (n, OpSem.state_of_state s')).
```

As external calls are not modelled by the deep semantics, the lemma is only
applicable to programs (more specifically their runs) that never call them. In
turn, it also means that it holds for every `exfs`.

This is also the first step to show that proofs using `Seplog` not only are
valid for shallow GallinaC, but also for deep GallinaC. In combination with the
end-to-end compilation correctness theorem `transf_gc_program_correct`, this can
be lifted all the way down to the assembly.
