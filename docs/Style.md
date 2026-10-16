# Import order

`Require`/`Import`/`Export` should be done at the top of the file, in the
following order. The sole exception are plain imports (i.e. without `Require`)
which should be limited to a module. Obviously, some entries might be
unnecessary for a file.

1. ssreflect and hierarchy builder imports
2. Corelib imports
3. Stdlib imports
4. CompCert imports
5. GallinaC imports

When mixing plain `Require`, `Import` and `Export`, perform first the plain
`Require`s, then the `Import`s and finally the `Export`s. When `Import`ing or
`Export`ing a module found within a file, import it on a line below the one
`Require`ing the file.

For instance

```
From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.

From Corelib Require Import Classes.RelationClasses.

From Stdlib Require Import Arith.
From Stdlib Require Export List.
Import ListNotations.

From compcert Require Archi.

From GallinaC.Utils Require Import Algebra.
From GallinaC.Imp Require Intops.
From GallinaC.Imp Require Import Memory.
```

## ssreflect and Hierarchy Builder imports

When a file uses ssreflect or HB, perform exactly these imports first.

```
From Corelib Require Import ssreflect ssrfun ssrbool.
From HB Require Import structures.
```

# Decidable propositions

Use the reflection pattern to show that it is indeed decidable.

Define a boolean function which returns true iff for the values where the
proposition holds. Then, prove that that function *reflects* the proposition.
It then becomes possible to `destruct` that lemma. To perform case analysis on
the function.

An example

```
Inductive P: nat -> Prop := ...

Definition f (n: nat): bool := ...

Lemma f_spec: forall n, Bool.reflect (P n) (f n).
Proof.
...
Qed.
```

# Naming style

To preserve a cohesive naming style, follow the style recorded here.

## Hypotheses names

The prefered style is `ALLCAPs`, i.e. upper case letters with some optional
trailing numbers or lower case letters to indicate intent.

Don't prefix `H` on hypotheses unless there is no alternative.

Some examples

```
Lemma add_lt_r (n m: nat) (LT: 0 < m):
  n < n + m.
Proof.
...
Qed.

Lemma lt_trans (x y z: nat)
  (LTxy: x < y) (LTyz: y < z)
  :  x < z.
Proof.
...
Qed.

Lemma modus_ponens [P Q: Prop]
  (HP: P) (PQ: P -> Q)
  (* Can't name the hypothesis [P] as it would shadow *)
  : Q.
Proof.
  apply PQ, HP.
Qed.
```

## Naming patterns

Common naming patterns are recorded here.

### Disjointness

- In a hypothesis: `(DSJ: X $/= Y)`
- In a lemma name: suffix `_dsj`

### Function-likeness

- In a lemma name: suffix `_fun`

### Soundness / Correctness

- In a lemma name: suffix `_correct`

### Completeness

- In a lemma name: suffix `_complete`

### Well-typedness

- In a hypothesis: `(WT: …)`, or `WT` plus a short lower-case suffix naming
  the subject when the context leaves it unclear, e.g. `(WTp: wt_program p)`
