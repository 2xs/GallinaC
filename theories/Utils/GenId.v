From GallinaC.Utils Require Import Algebra.

Local Open Scope separation_scope.

Create HintDb genid.

(** Identifier generation

    An identifier generator follows a separation algebra, with certain additional axioms
 *)
Record GenId: Type :=
  {
    carrier :> Separation;
    get: carrier -> option nat;
    next: carrier -> carrier;
    get_next_fw_none: forall (g: carrier) (EQ: get g = None), get (next g) = None;
    get_next_bw_some: forall (g: carrier) (id1: nat) (EQ: get (next g) = Some id1),
    exists id0, get g = Some id0;
    get_next_lt: forall (g: carrier) (id0 id1: nat)
                        (EQ0: get g = Some id0) (EQ1: get (next g) = Some id1),
      id0 < id1;
    get_sep: forall g1 g2, g1 $/= g2 -> get g1 <> get g2 \/ (get g1 = None /\ get g2 = None);
    next_sep: forall g1 g2, g1 $/= g2 -> next g1 $/= g2;
  }.

Arguments carrier GId: rename, simpl never.
Arguments get [GId] g: rename, simpl never.
Arguments next [GId] g: rename, simpl never.
Arguments get_next_fw_none [GId] g EQ: rename, simpl never.
Arguments get_next_bw_some [GId] g id1 EQ: rename, simpl never.
Arguments get_next_lt [GId] g id0 id1 EQ0 EQ1: rename, simpl never.
Arguments get_sep [GId] g1 g2 DSJ: rename, simpl never.
Arguments next_sep [GId] g1 g2 DGJ: rename, simpl never.

Hint Resolve get_next_fw_none get_next_bw_some get_next_lt get_sep next_sep: genid.
