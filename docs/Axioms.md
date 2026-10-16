# Axioms in GallinaC

In part due to dependencies (Corec and CompCert), GallinaC introduces certain
axioms. These axioms are not known to introduce inconsistencies. However, they
may only be explicitly imported and used at the specified files. Axiom usage
should only be transitively through these files' definitions.

Never import any other axioms such as UIP. You can test that a
definition/lemma/theorem does not rely on any other lemmas using

`Print Assumptions mylemma.`

## Corec library

The corecursion library in `theories/Corec` relies on the following axioms:
- Functional extensionality `functional_extensionality_dep`
- Propositional extensionality `propositional_extensionality`
- Classical excluded middle `classic`
- Constructive indefinite descriptions `constructive_indefinite_description`

Note: As propositional extensionality is strong enough to imply proof
irrelevance, Corec does not (and should not) import the dedicated
`ProofIrrelevance` module from `Stdlib`.

## Monad definition

The monad definition in `theories/Imp/Monad.v` relies on the following axiom:
- Functional extensionality `functional_extensionality_dep`

## Turing-complete while loop

The definition of the `while` loop relies on the `Corec` library. Hence, it transitively relies on the same axioms.
In addition, the module imports and uses the following axiom explicitly:
- Functional extensionality `functional_extensionality_dep`

## Semantic equivalence between deep and shallow GallinaC

The proof of semantic equivalence relies on the `Corec` library. Hence, it transitively relies on the same axioms.
In addition, the module imports and uses the following axiom explicitly:
- Functional extensionality `functional_extensionality_dep`

## CompCert floats

CompCert relies on the following axioms for the treatment of floating point
values and operations. These axioms only appear transitively, e.g. when
interacting with Cminor.
- Weak excluded middle in type `sig_not_dec`
- Least Principle of Omniscience (LPO) `sig_forall_dec`

## CompCert core axioms

CompCert relies throughout its development on further axioms. Of importance for GallinaC are the following.
- Custom proof irrelevance `proof_irr`
- Semantic correctness of external code `external_functions_sem`, `external_functions_properties`, `inline_assembly_sem`, `inline_assembly_properties`
- Classical excluded middle `classic`
- Functional extensionality `functional_extensionality_dep`
- Numerous constants defined outside Rocq which the extracted code links against

### CompCert extraction constants

To bridge the gap with the "real world", CompCert defines constants as `Parameter`.
These are then implemented outside Rocq and the extracted code links against them.
See `examples/Reverse/ReverseExtraction.v` for how they are bound at extraction.
They are divided as follows:

- Compiler options (`Compopts`)
- Pretty-printers (`Compiler.print_*`)
- Target descriptions (`Archi.win64` and `symbol_is_relocatable`)
- Algorithms implemented in OCaml and checked back inside the "Rocq world"
- Unchecked heuristics which don't affect the proofs

## Axioms reference

```
Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep :
  forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
Stdlib.Logic.PropExtensionality.propositional_extensionality :
  forall P Q : Prop, P <-> Q -> P = Q
Stdlib.Logic.Classical_Prop.classic :
  forall P : Prop, P \/ ~ P
Stdlib.Logic.IndefiniteDescription.constructive_indefinite_description :
  forall [A : Type] (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
Stdlib.Reals.ClassicalDedekindReals.sig_not_dec :
  forall P : Prop, {~ ~ P} + {~ P}
Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec :
  forall P : nat -> Prop, (forall n : nat, {P n} + {~ P n}) -> {n : nat | ~ P n} + {forall n : nat, P n}
compcert.lib.Axioms.proof_irr :
  forall [A : Prop] (a1 a2 : A), a1 = a2
compcert.common.Events.external_functions_sem :
  String.string -> AST.signature -> Events.extcall_sem
compcert.common.Events.external_functions_properties :
  forall (id : String.string) (sg : AST.signature), Events.extcall_properties (Events.external_functions_sem id sg) sg
compcert.common.Events.inline_assembly_sem :
  String.string -> AST.signature -> Events.extcall_sem
compcert.common.Events.inline_assembly_properties :
  forall (id : String.string) (sg : AST.signature), Events.extcall_properties (Events.inline_assembly_sem id sg) sg
```
