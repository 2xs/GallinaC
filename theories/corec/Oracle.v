From Coq Require Import Classical IndefiniteDescription.


Lemma cases{A B:Prop}: A \/ B ->  {A} + {B}.
Proof.
intro Hor.
assert (Hex :
          let AB := fun (b : bool) => 
           match b with true => A | false => B end in
          exists b,  AB b);
[destruct Hor as [HP | HnP]; [   now exists true |   now exists false]|] .
apply constructive_indefinite_description in Hex.
destruct Hex as (x & Hex).
destruct x ; [ now left | now right].
Qed.



Lemma oracle : forall (p:Prop), {p} + {~p}.
Proof.
intro p.
assert(Hor := classic p).
now apply cases.
Qed.
