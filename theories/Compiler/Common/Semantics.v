(*
GallinaC: Unifying Verification and Certified Compilation of System Programs in Rocq
Copyright (C) 2023-2026 GallinaC contributors (see CONTRIBUTORS.md)

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program. If not, see <https://www.gnu.org/licenses/>.
*)

From Corelib Require Import ssreflect ssrfun ssrbool.

From Stdlib Require Import NArith Psatz.

From GallinaC.Utils Require Import ListExt.
From GallinaC.Imp Require Import Store.

Local Open Scope separation_scope.
Local Open Scope mem_scope.

Section StackBlockAlloc.

  Context [Ad: Addr.type] [Nm: Ref.type Ad] [Vl: Type] [St: Store.type Ad Nm Vl].

  Definition stack_block_alloc (v: Vl) (n: N) (st0: St) (sg0: excl (@store_cnt Ad Nm Vl St))
    : option (St * excl (@store_cnt Ad Nm Vl St) * list Nm) :=
    N.iter n
        (fun acc => match acc with
                    | Some (st, sg, locals) =>
                        match push st sg v with
                        | Some (st', sg', l) => Some (st', sg', locals ++ [l])
                        | None => None
                        end
                    | None => None
                    end)
        (Some (st0, sg0, @nil Nm)).

  Lemma stack_block_alloc_0 (v: Vl) (st0: St) sg0:
    stack_block_alloc v 0 st0 sg0 = Some (st0, sg0, []).
  Proof using Type. by []. Qed.

  Lemma stack_block_alloc_succ (v: Vl) (n: N) (st0: St) sg0:
    stack_block_alloc v (N.succ n) st0 sg0
    = match stack_block_alloc v n st0 sg0 with
      | Some (st, sg, locals) =>
          match push st sg v with
          | Some (st', sg', l) => Some (st', sg', locals ++ [l])
          | None => None
          end
      | None => None
      end.
  Proof using Type. by rewrite /stack_block_alloc N.iter_succ. Qed.

  Lemma stack_block_alloc_inv [st0: St] [sg0: excl (@store_cnt Ad Nm Vl St)]
    (DOM0: dominates st0 sg0) (v: Vl):
    forall (n: N) (st: St) sg locals
           (ALLOC: stack_block_alloc v n st0 sg0 = Some (st, sg, locals)),
      List.length locals = N.to_nat n
      /\ dominates st sg
      /\ layered st0 locals st
      /\ (forall a v', (a |-> v') $<= st ->
            (a |-> v') $<= st0
            \/ (exists i nm, List.nth_error locals i = Some nm
                             /\ References nm a
                             /\ v' = v)).
  Proof using Type.
    elim/N.peano_ind => [ | n IH ] st sg locals ALLOC.
    - rewrite stack_block_alloc_0 in ALLOC; case: ALLOC => <- <- <-.
      split; first by [].
      split; first exact: DOM0.
      split; first exact: layered_nil.
      by move=> a v' SUB; left.
    - move: ALLOC; rewrite stack_block_alloc_succ.
      case ALLOC1: (stack_block_alloc v n st0 sg0) => [[[st1 sg1] locals1]|] //.
      case PUSH: (push st1 sg1 v) => [[[st' sg'] l]|] //.
      case=> <- <- <-.
      case: (IH st1 sg1 locals1 ALLOC1) => [LEN1 [DOM1 [LAYERED1 DEC1]]].
      case: (proj2 (push_some st1 sg1 v)
               (ex_intro _ st' (ex_intro _ sg' (ex_intro _ l PUSH))))
        => [k [CGET _]].
      case: (push_mem st1 sg1 v st' sg' l k PUSH CGET) => [REFl [WRTl SUMl]].
      split; first by rewrite length_app LEN1 N2Nat.inj_succ /=; lia.
      split; first exact: (dominates_push st1 st' sg1 sg' v l PUSH DOM1).
      split.
      + exact: (layered_snoc st0 locals1 st1 l (mkAddr k 0%N) v st' LAYERED1 REFl WRTl
                 (dominates_block_lt CGET DOM1 (mkAddr_block k 0%N)) SUMl).
      + move=> a v' SUB.
        case: (one_discriminate SUMl a v' SUB) => [[EA EW] | [_ SUB1]].
        * right; exists (List.length locals1), l.
          split; first exact: ListExt.nth_error_last.
          split; last exact: EW.
          rewrite EA; exact: REFl.
        * case: (DEC1 a v' SUB1) => [SUB0 | [i [nm [NTH [REF EW]]]]]; first by left.
          right; exists i, nm.
          split; first exact: (ListExt.nth_error_snoc_mono NTH).
          by split.
  Qed.

  Lemma stack_block_alloc_layered [st0: St] [sg0: excl (@store_cnt Ad Nm Vl St)]
    (DOM0: dominates st0 sg0) (v: Vl) [n st sg locals]
    (ALLOC: stack_block_alloc v n st0 sg0 = Some (st, sg, locals)):
    layered st0 locals st.
  Proof using Type.
    by case: (stack_block_alloc_inv DOM0 v n st sg locals ALLOC) => [_ [_ [LAYERED _]]].
  Qed.

  Lemma stack_block_alloc_cnt (v: Vl):
    forall (n: N) [st0: St] [k0 st sg locals]
           (ALLOC: stack_block_alloc v n st0 (Owned (mk_cnt k0 None)) = Some (st, sg, locals)),
    exists k, sg = Owned (mk_cnt k None).
  Proof using Type.
    elim/N.peano_ind => [ | n IH ] st0 k0 st sg locals ALLOC.
    - rewrite stack_block_alloc_0 in ALLOC; case: ALLOC => _ <- _.
      by exists k0.
    - move: ALLOC; rewrite stack_block_alloc_succ.
      case ALLOC1: (stack_block_alloc v n st0 (Owned (mk_cnt k0 None)))
        => [[[st1 sg1] locals1]|] //.
      case PUSH: (push st1 sg1 v) => [[[st' sg'] l]|] //.
      case=> _ <- _.
      case: (IH st0 k0 st1 sg1 locals1 ALLOC1) => [k Esg].
      exists (S k).
      by rewrite (push_cnt st1 sg1 v st' sg' l PUSH) Esg cnext_owned cnext_mk_cnt.
  Qed.

  Lemma stack_block_alloc_some [st0: St] [k0: nat]
    (DOM0: dominates st0 (Owned (mk_cnt k0 None): excl (@store_cnt Ad Nm Vl St)))
    (v: Vl):
    forall n: N,
    exists st sg locals,
      stack_block_alloc v n st0 (Owned (mk_cnt k0 None)) = Some (st, sg, locals).
  Proof using Type.
    elim/N.peano_ind => [ | n [st [sg [locals ALLOC]]]].
    - exists st0, (Owned (mk_cnt k0 None): excl (@store_cnt Ad Nm Vl St)), (@nil Nm).
      exact: stack_block_alloc_0.
    - case: (stack_block_alloc_cnt v n ALLOC) => [k Esg].
      case: (stack_block_alloc_inv DOM0 v n st sg locals ALLOC) => [_ [DOM _]].
      have CGETS: cget sg = Some k by rewrite Esg cget_owned; exact: cget_mk_cnt_none.
      case: (push_of_dominates v CGETS DOM) => [st' [sg' [l EPUSH]]].
      exists st', sg', (locals ++ [l]).
      by rewrite stack_block_alloc_succ ALLOC EPUSH.
  Qed.

  Lemma stack_block_alloc_sub (v: Vl):
    forall (n: N) [st_s st_t: St] [c: excl (@store_cnt Ad Nm Vl St)] [st_s' c' nms]
           (SUB: st_t $<= st_s)
           (ALLOC: stack_block_alloc v n st_s c = Some (st_s', c', nms)),
    exists st_t',
      stack_block_alloc v n st_t c = Some (st_t', c', nms) /\ st_t' $<= st_s'.
  Proof using Type.
    elim/N.peano_ind => [ | n IH ] st_s st_t c st_s' c' nms SUB ALLOC.
    - rewrite stack_block_alloc_0 in ALLOC; case: ALLOC => <- <- <-.
      by exists st_t; rewrite stack_block_alloc_0.
    - move: ALLOC; rewrite stack_block_alloc_succ.
      case ALLOC1: (stack_block_alloc v n st_s c) => [[[st1 c1] nms1]|] //.
      case PUSH: (push st1 c1 v) => [[[st2 c2] nm]|] //.
      case=> <- <- <-.
      case: (IH st_s st_t c st1 c1 nms1 SUB ALLOC1) => [st_t1 [ALLOCT1 SUB1]].
      case: (push_sub SUB1 PUSH) => [st_t2 [PUSHT SUB2]].
      by exists st_t2; rewrite stack_block_alloc_succ ALLOCT1 PUSHT.
  Qed.

End StackBlockAlloc.
