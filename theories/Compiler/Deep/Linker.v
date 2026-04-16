From Stdlib Require Import Arith BinPos.

From compcert.common Require Export Linking.
From compcert.cfrontend Require Ctypes.

From GallinaC.Compiler.Common Require Import Types.

From GallinaC.Compiler.Deep Require Import Prog.

Local Obligation Tactic := cbn.

Global Program Instance Linker_type : Linker type := {
  link := fun t1 t2 => if type_eqb t1 t2 then Some t1 else None;
  linkorder := eq
}.
Next Obligation.
  reflexivity.
Defined.

Next Obligation.
  congruence.
Defined.

Next Obligation.
  intros x y z.
  destruct (type_eqb_spec x y); [ subst | discriminate ].
  intros Heq. split; congruence.
Defined.

Lemma link_type_eq: forall (t1 t2 t: type), link t1 t2 = Some t -> t1 = t /\ t2 = t.
Proof.
  unfold link; cbn.
  intros t1 t2 t Heq.
  destruct (type_eqb_spec t1 t2); [ | discriminate ].
  split; congruence.
Qed.

Lemma linkorder_type_eq: forall (t1 t2: type), linkorder t1 t2 -> t1 = t2.
Proof.
  auto.
Qed.
Global Opaque Linker_type.

(* Definition link_name {St: Store} (nm1 nm2: @name St): option (name) := *)
(*   match name_eq_dec nm1 nm2 with *)
(*   | left _ => Some nm1 *)
(*   | right _ => None *)
(*   end. *)

(* Global Program Instance Linker_name {St: Store}: Linker (@name St) := { *)
(*     link := link_name; *)
(*     linkorder := eq; *)
(*   }. *)
(* Next Obligation. *)
(*   auto. *)
(* Defined. *)

(* Next Obligation. *)
(*   intros; congruence. *)
(* Defined. *)

(* Next Obligation. *)
(*   unfold link_name. *)
(*   intros St x y z Heq. *)
(*   destruct (name_eq_dec x y); try discriminate. *)
(*   split; congruence. *)
(* Defined. *)

(* Lemma link_name_eq: forall {St: Store} (nm1 nm2 nm: @name St), link nm1 nm2 = Some nm -> nm1 = nm /\ nm2 = nm. *)
(* Proof. *)
(*   unfold link; cbn; unfold link_name. *)
(*   intros St nm1 nm2 nm Heq. *)
(*   destruct (name_eq_dec nm1 nm2); [ split; congruence | discriminate ]. *)
(* Qed. *)

(* Lemma linkorder_name_eq: forall {St: Store} (nm1 nm2: @name St), linkorder nm1 nm2 -> nm1 = nm2. *)
(* Proof. *)
(*   intros; auto. *)
(* Qed. *)

(* Global Opaque Linker_name. *)

Definition link_fundef (fd1 fd2: fundef) :=
  match fd1, fd2 with
  | AST.Internal _, AST.Internal _ => None
  | AST.External ef1, AST.External ef2 =>
      if AST.external_function_eq ef1 ef2 then Some (AST.External ef1) else None
  | AST.Internal f, AST.External ef =>
      match ef with AST.EF_external id sg => Some (AST.Internal f) | _ => None end
  | AST.External ef, AST.Internal f =>
      match ef with AST.EF_external id sg => Some (AST.Internal f) | _ => None end
  end.

Inductive linkorder_fundef: fundef -> fundef -> Prop :=
| linkorder_fundef_refl: forall fd, linkorder_fundef fd fd
| linkorder_fundef_ext_int: forall id sg f,
  linkorder_fundef (AST.External (AST.EF_external id sg)) (AST.Internal f)
.

Global Program Instance Linker_fundef: Linker fundef := {
    link := link_fundef;
    linkorder := linkorder_fundef;
  }.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  intros.
  inversion H; subst; inversion H0; subst; constructor.
Qed.
Next Obligation.
  intros.
  destruct x, y; cbn in H.
  discriminate.
  destruct e; inversion H; subst; now repeat constructor.
  destruct e; inversion H; subst; now repeat constructor.
  destruct (AST.external_function_eq e e0); [ inversion H; subst; split; constructor | discriminate ].
Qed.

Lemma link_fundef_either: forall (fd1 fd2 fd: fundef), link fd1 fd2 = Some fd -> fd = fd1 \/ fd = fd2.
Proof.
  cbn; unfold link, link_fundef; intros.
  destruct fd1, fd2.
  discriminate.
  destruct e; inversion H; subst; auto.
  destruct e; inversion H; subst; auto.
  destruct (AST.external_function_eq e e0); subst; inversion H; auto.
Qed.

Global Opaque Linker_fundef.

Definition link_vardef (v1 v2: vardef) :=
  match link v1.(var_type) v2.(var_type) with
  | Some vtype => Some (mkvardef vtype)
  | None => None
  end.

Global Program Instance Linker_vardef: Linker vardef :=
  {
    link := link_vardef;
    linkorder := eq;
  }.
Next Obligation.
  auto.
Defined.

Next Obligation.
  intros; congruence.
Defined.

Next Obligation.
  unfold link_vardef.
  intros x y z Heq.
  destruct (link (var_type _) _) eqn:Evtype; [ | discriminate ].
  apply link_linkorder in Evtype.
  destruct Evtype as [ Hlo_type_x Hlo_type_y ].
  apply linkorder_type_eq in Hlo_type_x;
    apply linkorder_type_eq in Hlo_type_y.
  destruct x, y, z; cbn in *; split; congruence.
Defined.

Lemma link_vardef_eq (v1 v2 v: vardef): link v1 v2 = Some v -> v1 = v /\ v2 = v.
Proof.
  unfold link; cbn; unfold link_vardef.
  intros Heq.
  destruct (link _ _) eqn:Evtype; [ | discriminate ].
  apply link_type_eq in Evtype.
  destruct Evtype as [ Hv1t Hv2t ].
  destruct v1, v2; split; cbn in *; congruence.
Qed.

Lemma linkorder_vardef_eq (v1 v2: vardef): linkorder v1 v2 -> v1 = v2.
Proof.
  auto.
Qed.

Global Opaque Linker_vardef.

Definition link_program (p1 p2: program): option program :=
  match link (program_of_program p1) (program_of_program p2) with
  | None => None
  | Some p =>
      let extra :=
        if (p1.(prog_extra).(prog_next_id) =? p2.(prog_extra).(prog_next_id))%positive then
          Some {| prog_next_id := p1.(prog_extra).(prog_next_id) |}
        else
          None
      in
      match extra with
      | Some extra =>
          Some
            {|
              prog_defs := p.(AST.prog_defs);
              prog_public := p.(AST.prog_public);
              prog_main := p.(AST.prog_main);
              prog_extra := extra
            |}
      | _ => None
      end
  end.

Definition linkorder_program (p1 p2: program) : Prop :=
     linkorder (program_of_program p1) (program_of_program p2)
  /\ (p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id)).

Global Program Instance Linker_program: Linker program := {
  link := link_program;
  linkorder := linkorder_program
}.
Next Obligation.
  split. apply linkorder_refl. auto.
Defined.

Next Obligation.
  unfold linkorder_program.
  intros x y z [ Hlo_xy H_x_y ] [ Hlo_yz H_y_z ].
  split; [ | congruence ].
  eapply linkorder_trans; eauto.
Defined.

Next Obligation.
  unfold link_program, linkorder_program.
  intros x y z Heq.
  destruct (link _ _) eqn:Elink; [ | discriminate ].
  destruct (Pos.eqb_spec (prog_next_id (prog_extra x)) (prog_next_id (prog_extra y))) as [EQ | ]; [ subst | discriminate ].
  inversion Heq; subst; clear Heq.
  (* destruct (match prog_malloc (prog_extra x) with Some _ => _ | None => _ end) as [ mallocx' | ] eqn:Emallocx; [ | discriminate ]. *)
  (* destruct (match prog_free (prog_extra x) with Some _ => _ | None => _ end) as [ freex' | ] eqn:Efreex; [ | discriminate ]. *)
  apply link_linkorder in Elink as [ LOxp LOyp ].
  destruct p as [ defsp publicp mainp]; cbn in *.

  destruct x as [defsx publicx mainx [next_idx]], y as [defsy publicy mainy [next_idy]]; cbn in *;
    subst.
  auto.
Defined.

Lemma linkorder_program_next_id (p1 p2: program) (Hlinkorder: linkorder p1 p2)
  : p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id).
Proof.
  now inversion Hlinkorder.
Qed.

Lemma linkorder_program_free (p1 p2: program) (Hlinkorder: linkorder p1 p2)
  : p1.(prog_extra).(prog_next_id) = p2.(prog_extra).(prog_next_id).
Proof.
  now inversion Hlinkorder.
Qed.


Global Opaque Linker_program.
