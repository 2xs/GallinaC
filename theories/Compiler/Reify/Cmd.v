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

From Stdlib Require Import PArith Arith.

From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Deep Require Export Cmd.
From GallinaC.Compiler.Reify Require Export Common Types Env Expr.

Import MonadNotation.
Local Open Scope bs_scope.

Polymorphic Fixpoint translate_args (renv: reify_funbody_env) (tms: list term): TemplateMonad (list expr) :=
  match tms with
  | [] => tmReturn []
  | tm::tms =>
      arg <- translate_expr renv tm;;
      args <- translate_args renv tms;;
      tmEval cbv (arg::args)
  end.

(* Deep GallinaC doesn't have tail calls because shallow GallinaC doesn't either.
 * In [do x <- f; g x] the tail call [g x] executes in a sub-environment of the calling function.
 * To materialize this difference, the reification process wraps a tail-position
 * call as [do tmp <- app f args; ret tmp] with a fresh temp.  The [c_bind]
 * supplies the [Kbind] resolution target at the return: [step_return_call_seq]'s
 * [resolve_seq_cont] cannot resolve a marker chain bottoming out at
 * [Kcall]/[Kstop] (no rule), so a bare tail [c_app] would leave the machine
 * stuck.
 *)
Polymorphic Definition wrap_tail_call (renv: reify_funbody_env) (f: Prog.fundef) (f_id: AST.ident) (args: list expr): TemplateMonad (cmd * reify_funbody_env) :=
  match Prog.type_funsig f with
  | Some sig =>
      t_ret <- tmEval cbv sig.(Prog.sig_res);;
      '(renv, tmp) <- tmEval cbv (push_temp renv nAnon t_ret);;
      renv <- tmEval cbv (drop_temp renv tmp);;
      tmReturn (c_bind tmp t_ret (c_app f_id args) (c_ret (e_var tmp)), renv)
  | None => tmPrint (c_app f_id args);; tmFail "wrap_tail_call: cannot determine the callee's return type"
  end.

(* [tail] tracks whether [tm] sits in tail position of the function body,
   i.e. its result lands directly on a call cont ([Kcall]/[Kstop]) and any
   tail [c_app] must be wrapped by [wrap_tail_call].  Tail position
   propagates through bind continuations, [c_if] branches
   ([step_ifthenelse] keeps the continuation) and [c_with_var] bodies
   ([step_with_var] only pushes a [Kscope scope_store] marker, see
   [examples/WithVarTail]).  It is cleared under bind's first arm and
   while's cond/body, whose returning calls resolve at the enclosing seq
   cont ([Kbind]/[Kloop1]/[Kloop2]). *)
Polymorphic Fixpoint translate_cmd (tail: bool) (renv: reify_funbody_env) (tm: term): TemplateMonad (cmd * reify_funbody_env) :=
  match tm with
  | tApp f args =>
      (* Application *)
      match f with
      | tConst ((path, f) as kname) _ =>
          match resolve_modpath_ext renv path with
          | ImpMonad =>
              match resolve_monad_primitive f with
              | Some Bind =>
                  match args with
                  | [_; tmA; _; tmm; tmf] =>
                      t <- translate_type tmA;;
                      '(cb, renv) <- translate_cmd false renv tmm;;
                      cb <- tmEval cbv cb;;
                      renv <- tmEval cbv renv;;
                      match tmf with
                      | tLambda {| binder_name := binder |} tm4 tm3 =>
                          '(renv, b_id) <- tmEval cbv (push_temp renv binder t);;
                          '(cc, renv) <- translate_cmd tail renv tm3;;
                          cc <- tmEval cbv cc;;
                          renv <- tmEval cbv renv;;
                          renv <- tmEval cbv (drop_temp renv b_id);;
                          tmReturn (c_bind b_id t cb cc, renv)
                      | _ => tmFail "translate_cmd: bind: malformed continuation"
                      end
                  | _ => tmFail "translate_cmd: bind: malformed arguments"
                  end
              | Some Ret  =>
                  match args with
                  | [_; _; tm] =>
                      e <- translate_expr renv tm ;;
                      tmReturn (c_ret e, renv)
                  | _ =>
                      tmFail "translate_cmd: ret: malformed arguments"
                  end
              | None =>
                  tmFail ("translate_cmd: unknown monad primitive " ++ f)
              end
          | ImpPrimitives =>
              match resolve_gallinac_primitive f with
              | Some WithVar =>
                  match args with
                  | [_; A; MS; tm_var; tm_cont] =>
                      t <- translate_storable MS;;
                      e_var <- translate_expr renv tm_var;;
                      e_var <- tmEval cbv e_var;;
                      match tm_cont with
                      | tLambda {| binder_name := binder |} tm4 tm3 =>
                          renv <- tmEval cbv (push_local renv t);;
                          '(c_cont, renv) <- translate_cmd tail renv tm3 ;;
                          c_cont <- tmEval cbv c_cont;;
                          renv <- tmEval cbv (drop_local renv);;
                          tmReturn (c_with_var t e_var c_cont, renv)
                      | _ => tmFail "translate_cmd: with_var: not a continuation"
                      end
                  | _ => tmFail "translate_cmd: with_var: malformed arguments"
                  end
              | Some ReadVar =>
                  match args with
                  | [_; MS; tRel i] =>
                      t <- translate_storable MS;;
                      match resolve_rel_local renv i with
                      | Some ofst => tmReturn (c_read_var ofst t, renv)
                      | None => tmFail ("Error in translate_cmd: unbound local variable" ++ string_of_nat i)
                      end
                  | _ => tmFail "translate_cmd: read_var: malformed arguments"
                  end
              | Some WriteVar =>
                  match args with
                  | [_; MS; tRel i; tm_val] =>
                      t <- translate_storable MS;;
                      e_val <- translate_expr renv tm_val;;
                      match resolve_rel_local renv i with
                      | Some ofst => tmReturn (c_write_var ofst t e_val, renv)
                      | None => tmFail ("Error in translate_cmd: unbound local variable" ++ string_of_nat i)
                      end
                  | _ => tmFail "translate_cmd: write_var: malformed arguments"
                  end
              | Some AllocPtr =>
                  match args with
                  | [_; MS; tm_sz; tm_init] =>
                      e_sz <- translate_expr renv tm_sz;;
                      t <- translate_storable MS;;
                      e_init <- translate_expr renv tm_init ;;
                      tmReturn (c_alloc_ptr e_sz t e_init, renv)
                  | _ => tmFail "translate_cmd: alloc_ptr: malformed arguments"
                  end
              | Some ReadPtr =>
                  match args with
                    | [_; MS; tm_p] =>
                        e_p <- translate_expr renv tm_p;;
                        t <- translate_storable MS;;
                        tmReturn (c_read_ptr e_p t, renv)
                  | _ => tmFail "translate_cmd: read_ptr: malformed arguments"
                  end
              | Some WritePtr =>
                  match args with
                  | [_; MS; tm_p; tm_val] =>
                      e_p <- translate_expr renv tm_p;;
                      t <- translate_storable MS;;
                      e_val <- translate_expr renv tm_val;;
                      tmReturn (c_write_ptr e_p t e_val, renv)
                  | _ => tmFail "translate_cmd: write_ptr: malformed arguments"
                  end
              | Some FreePtr =>
                  match args with
                  | [_; tm_ptr] =>
                      e_ptr <- translate_expr renv tm_ptr;;
                      tmReturn (c_free_ptr e_ptr, renv)
                  | _ => tmFail "translate_cmd: free_ptr: malformed arguments"
                  end
              | Some EqPtr =>
                  match args with
                  | [_; tm_l; tm_r] =>
                      e_l <- translate_expr renv tm_l;;
                      e_r <- translate_expr renv tm_r;;
                      tmReturn (c_ptr_eq e_l e_r, renv)
                  | _ => tmFail "translate_cmd: eq_ptr: malformed arguments"
                  end
              | Some ShiftFWPtr =>
                  match args with
                  | [_; tm1; tm2] =>
                      e1 <- translate_expr renv tm1;;
                      e2 <- translate_expr renv tm2;;
                      tmReturn (c_shift_fw_ptr e1 e2, renv)
                  | _ => tmFail "translate_cmd: shift_fw_ptr: malformed arguments"
                  end
              | Some ShiftBWPtr =>
                  match args with
                  | [_; tm1; tm2] =>
                      e1 <- translate_expr renv tm1;;
                      e2 <- translate_expr renv tm2;;
                      tmReturn (c_shift_bw_ptr e1 e2, renv)
                  | _ => tmFail "translate_cmd: shift_bw_ptr: malformed arguments"
                  end
              | Some While =>
                  match args with
                  | [_; tm_cond; tm_body] =>
                      '(c_cond, renv') <- translate_cmd false renv tm_cond ;;
                      renv <- tmEval cbv
                                     {|
                                       prog_renv := renv'.(prog_renv);
                                       stack := renv.(stack);
                                       stack_depth := renv.(stack_depth);
                                       temps := renv'.(temps);
                                       model := renv.(model);
                                     |};;
                      c_cond <- tmEval cbv c_cond;;
                      renv <- tmEval cbv renv;;
                      '(c_body, renv) <- translate_cmd false renv tm_body ;;
                      c_body <- tmEval cbv c_body ;;
                      renv <- tmEval cbv renv ;;
                      tmReturn (c_while c_cond c_body, renv)
                  | _ => tmFail "translate_cmd: while: malformed arguments"
                  end
              | None => tmFail ("translate_cmd: unknown GallinaC primitive " ++ f)
              end
          | ImpWhile =>
              match args with
              | [_; tm_cond; tm_body] =>
                  '(c_cond, renv') <- translate_cmd false renv tm_cond ;;
                  renv <- tmEval cbv
                                 {|
                                   prog_renv := renv'.(prog_renv);
                                   stack := renv.(stack);
                                   stack_depth := renv.(stack_depth);
                                   temps := renv'.(temps);
                                   model := renv.(model);
                                 |};;
                  c_cond <- tmEval cbv c_cond;;
                  renv <- tmEval cbv renv;;
                  '(c_body, renv) <- translate_cmd false renv tm_body ;;
                  c_body <- tmEval cbv c_body ;;
                  renv <- tmEval cbv renv ;;
                  tmReturn (c_while c_cond c_body, renv)
              | _ => tmFail "translate_cmd: while: malformed arguments"
              end
          | ImpIntopsUnsigned =>
              match resolve_numeric_primitive f with
              | Some Mdl =>
                  match args with
                  | [_; UInt; tm_l; tm_r] =>
                      e1 <- translate_expr renv tm_l;;
                      e2 <- translate_expr renv tm_r;;
                      tmReturn (c_mod e1 e2, renv)
                  | _ => tmPrint tm;; tmFail "translate_cmd: mdl: malformed arguments"
                  end
              | Some Div =>
                  match args with
                  | [_; UInt; tm_l; tm_r] =>
                      e1 <- translate_expr renv tm_l;;
                      e2 <- translate_expr renv tm_r;;
                      tmReturn (c_div e1 e2, renv)
                  | _ => tmPrint tm;; tmFail "translate_cmd: div: malformed arguments"
                  end
              | None => tmPrint tm;; tmFail "translate_cmd: unknown numeric primitive"
              end
          | CurrentModule =>
              args <- translate_args renv (drop_model_arg renv args) ;;
              match resolve_named_internal renv kname with
              | Some (i, f) =>
                  if tail
                  then wrap_tail_call renv (AST.Internal f) i args
                  else tmEval cbv (c_app i args, renv)
              | None => tmFail "Error in translate_cmd: invalid function"
              end
          | Other =>
              args <- translate_args renv (drop_model_arg renv args) ;;
              '(i, ef, renv) <-
                match resolve_named_external renv kname with
                | Some (i, ef) => tmReturn (i, ef, renv)
                | None => introduce_new_external renv kname
                end;;
              if tail
              then wrap_tail_call renv (AST.External ef) i args
              else tmEval cbv (c_app i args, renv)
          | CoreInitDatatypes | CoreInitPrelude | CoreNumbersBinNums
          | StdNArithBinNatDef
          | ImpHeap | ImpHeapPtr | ImpStateState | ImpStorableStorable | ImpValue
          | ImpIntopsIntCarrier | ImpUint32
          | ModelsPointerPointer =>
              tmPrint tm;;
              tmFail "Invalid command"
          end
      | _ => tmFail "TODO3"
      end
  | tConst ((modpath, _) as kname) _ =>
      match resolve_modpath_ext renv modpath with
      | CurrentModule =>
          match resolve_named_internal renv kname with
          | Some (i, f) =>
              if tail
              then wrap_tail_call renv (AST.Internal f) i []
              else tmEval cbv (c_app i [], renv)
          | None => tmFail "Error in translate_cmd: invalid function"
          end
      | _ => tmPrint tm;; tmFail "translate_cmd: unknown function called"
      end
  (* A [match] term (or [if] which is only syntactic sugar for [match])
     - [ci] tracks the inductive used for matching
     - [tm_scrutinee] is the matched term
     - [branches] are the matching branches, in the order of constructors (not the source text order)
     - the ignored argument (typed [AST.predicate term]) is only relevant if you use [as]/[in]/[return] which is currently forbidden in GallinaC
   *)
  | tCase ci _ tm_scrutinee branches =>
      (* Resolve the inductive used for matching *)
      match resolve_prim_inductive ci.(ci_ind) with
      | Some t_bool =>
          (* It is a boolean, we expect a [then] followed by an [else] branch
           * Generate a [c_if]
           *)
          match branches with
          | [ {| bcontext := []; bbody := tm_t |};
              {| bcontext := []; bbody := tm_e |} ] =>
              e_i <- translate_expr renv tm_scrutinee;;
              '(c_t, renv) <- translate_cmd tail renv tm_t;;
              c_t <- tmEval cbv c_t;;
              renv <- tmEval cbv renv;;
              '(c_e, renv) <- translate_cmd tail renv tm_e;;
              c_e <- tmEval cbv c_e;;
              renv <- tmEval cbv renv;;
              tmReturn (c_if e_i c_t c_e, renv)
          | _ => tmPrint tm;; tmFail "translate_cmd: if: malformed branches"
          end
      | _ => tmPrint tm;; tmFail "translate_cmd: match is only supported on bool"
      end
  | _ => tmPrint tm;; tmFail "translate_cmd: Not a command"
  end.
