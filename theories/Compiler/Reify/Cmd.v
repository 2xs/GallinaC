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

Polymorphic Fixpoint translate_cmd (renv: reify_funbody_env) (tm: term): TemplateMonad (cmd * reify_funbody_env) :=
  match tm with
  | tApp f args =>
      (* Application *)
      match f with
      | tConst ((path, f) as kname) _ =>
          match resolve_modpath renv path with
          | ImpMonad =>
              match resolve_monad_primitive f with
              | Some Bind =>
                  match args with
                  | [_; tmA; _; tmm; tmf] =>
                      t <- translate_type tmA;;
                      '(cb, renv) <- translate_cmd renv tmm;;
                      cb <- tmEval cbv cb;;
                      renv <- tmEval cbv renv;;
                      match tmf with
                      | tLambda {| binder_name := binder |} tm4 tm3 =>
                          '(renv, b_id) <- tmEval cbv (push_temp renv binder t);;
                          '(cc, renv) <- translate_cmd renv tm3;;
                          cc <- tmEval cbv cc;;
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
                  | [A; St; Hp; MS; tm_var; tm_cont] =>
                      t <- translate_storable MS;;
                      e_var <- translate_expr renv tm_var;;
                      e_var <- tmEval cbv e_var;;
                      match tm_cont with
                      | tLambda {| binder_name := binder |} tm4 tm3 =>
                          renv <- tmEval cbv (push_local renv t);;
                          '(c_cont, renv) <- translate_cmd renv tm3 ;;
                          c_cont <- tmEval cbv c_cont;;
                          renv <- tmEval cbv renv;;
                          tmReturn (c_with_var t e_var c_cont, renv)
                      | _ => tmFail "translate_cmd: with_var: not a continuation"
                      end
                  | _ => tmFail "translate_cmd: with_var: malformed arguments"
                  end
              | Some ReadVar =>
                  match args with
                  | [St; Hp; MS; tRel i] =>
                      t <- translate_storable MS;;
                      match resolve_rel_local renv i with
                      | Some ofst => tmReturn (c_read_var ofst t, renv)
                      | None => tmFail ("Error in translate_cmd: unbound local variable" ++ string_of_nat i)
                      end
                  | _ => tmFail "translate_cmd: read_var: malformed arguments"
                  end
              | Some WriteVar =>
                  match args with
                  | [St; Hp; MS; tRel i; tm_val] =>
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
                  | [_; _; MS; tm_sz; tm_init] =>
                      e_sz <- translate_expr renv tm_sz;;
                      t <- translate_storable MS;;
                      e_init <- translate_expr renv tm_init ;;
                      tmReturn (c_alloc_ptr e_sz t e_init, renv)
                  | _ => tmFail "translate_cmd: alloc_ptr: malformed arguments"
                  end
              | Some ReadPtr =>
                  match args with
                    | [St; Hp; MS; tm_p] =>
                        e_p <- translate_expr renv tm_p;;
                        t <- translate_storable MS;;
                        tmReturn (c_read_ptr e_p t, renv)
                  | _ => tmFail "translate_cmd: read_ptr: malformed arguments"
                  end
              | Some WritePtr =>
                  match args with
                  | [St; Hp; MS; tm_p; tm_val] =>
                      e_p <- translate_expr renv tm_p;;
                      t <- translate_storable MS;;
                      e_val <- translate_expr renv tm_val;;
                      tmReturn (c_write_ptr e_p t e_val, renv)
                  | _ => tmFail "translate_cmd: write_ptr: malformed arguments"
                  end
              | Some FreePtr =>
                  match args with
                  | [St; Hp; tm_ptr] =>
                      e_ptr <- translate_expr renv tm_ptr;;
                      tmReturn (c_free_ptr e_ptr, renv)
                  | _ => tmFail "translate_cmd: free_ptr: malformed arguments"
                  end
              | Some EqPtr =>
                  match args with
                  | [St; Hp; tm_l; tm_r] =>
                      e_l <- translate_expr renv tm_l;;
                      e_r <- translate_expr renv tm_r;;
                      tmReturn (c_ptr_eq e_l e_r, renv)
                  | _ => tmFail "translate_cmd: eq_ptr: malformed arguments"
                  end
              | Some ShiftFWPtr =>
                  match args with
                  | [St; Hp; tm1; tm2] =>
                      e1 <- translate_expr renv tm1;;
                      e2 <- translate_expr renv tm2;;
                      tmReturn (c_shift_fw_ptr e1 e2, renv)
                  | _ => tmFail "translate_cmd: shift_fw_ptr: malformed arguments"
                  end
              | Some ShiftBWPtr =>
                  match args with
                  | [St; Hp; tm1; tm2] =>
                      e1 <- translate_expr renv tm1;;
                      e2 <- translate_expr renv tm2;;
                      tmReturn (c_shift_bw_ptr e1 e2, renv)
                  | _ => tmFail "translate_cmd: shift_bw_ptr: malformed arguments"
                  end
              | Some While =>
                  match args with
                  | [_; tm_cond; tm_body] =>
                      '(c_cond, renv') <- translate_cmd renv tm_cond ;;
                      renv <- tmEval cbv
                                     {|
                                       prog_renv := renv'.(prog_renv);
                                       stack := renv.(stack);
                                       stack_depth := renv.(stack_depth);
                                       temps := renv'.(temps);
                                     |};;
                      c_cond <- tmEval cbv c_cond;;
                      renv <- tmEval cbv renv;;
                      '(c_body, renv) <- translate_cmd renv tm_body ;;
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
                  '(c_cond, renv') <- translate_cmd renv tm_cond ;;
                  renv <- tmEval cbv
                                 {|
                                   prog_renv := renv'.(prog_renv);
                                   stack := renv.(stack);
                                   stack_depth := renv.(stack_depth);
                                   temps := renv'.(temps);
                                 |};;
                  c_cond <- tmEval cbv c_cond;;
                  renv <- tmEval cbv renv;;
                  '(c_body, renv) <- translate_cmd renv tm_body ;;
                  c_body <- tmEval cbv c_body ;;
                  renv <- tmEval cbv renv ;;
                  tmReturn (c_while c_cond c_body, renv)
              | _ => tmFail "translate_cmd: while: malformed arguments"
              end
          | CurrentModule =>
              args <- translate_args renv args ;;
              c <- match resolve_named_internal renv kname with
                   | Some (i, _) => tmReturn (c_app i args, renv)
                   | None => tmFail "Error in translate_cmd: invalid function"
                   end
              ;;
              tmEval cbv c
          | Other =>
              args <- translate_args renv args ;;
              '(i, ef, renv) <- resolve_named_external renv kname;;
              tmEval cbv (c_app i args, renv)
          | ImpPointerPointer | CoreInitDatatypes =>
              tmPrint tm;;
              tmFail "Invalid command"
          end
      | _ => tmFail "TODO3"
      end
  | tConst ((modpath, _) as kname) _ =>
      match resolve_modpath renv modpath with
      | CurrentModule =>
          c <-
            match resolve_named_internal renv kname with
            | Some (i, _) => tmReturn (c_app i [], renv)
            | None => tmFail "Error in translate_cmd: invalid function"
            end
          ;;
          tmEval cbv c
      | _ => tmPrint tm;; tmFail "translate_cmd: unknown function called"
      end
  | _ => tmPrint tm;; tmFail "translate_cmd: Not a command"
  end.

(* Fixpoint translate_cmd (renv: reify_funbody_env) (tm : term) : TemplateMonad (cmd * reify_funbody_env) := *)
(*   match tm with *)
(*   | tApp (tConst (MPfile [], "ret") []) [_; _; tm] => *)
(*       e <- translate_expr renv tm ;; *)
(*       tmReturn (c_ret e, renv) *)
(*   | tApp (tConst (_, "bind") []) [_; tmA; _; tmm; tmf] => *)
(*       t  <- translate_type tmA ;; *)
(*       '(cb, renv) <- translate_cmd renv tmm ;; *)
(*       cb <- tmEval cbv cb;; *)
(*       renv <- tmEval cbv renv;; *)
(*       match tmf with *)
(*       | tLambda {| binder_name := binder |} tm4 tm3 => *)
(*           '(renv, b_id) <- tmEval cbv (push_temp renv binder t);; *)
(*           '(cc, renv) <- translate_cmd renv tm3 ;; *)
(*           cc <- tmEval cbv cc;; *)
(*           renv <- tmEval cbv (drop_temp renv b_id);; *)
(*           tmReturn (c_bind b_id t cb cc, renv) *)
(*       | _ => tmFail "Error in translate_cmd: not a continuation" *)
(*       end *)
(*   | tApp (tConst (_, "while") []) [_; tm_cond; tm_body] => *)
(*       '(c_cond, renv') <- translate_cmd renv tm_cond ;; *)
(*       renv <- tmEval cbv *)
(*                      {| *)
(*                        prog_renv := renv'.(prog_renv); *)
(*                        stack := renv.(stack); *)
(*                        stack_depth := renv.(stack_depth); *)
(*                      |};; *)
(*       c_cond <- tmEval cbv c_cond;; *)
(*       renv <- tmEval cbv renv;; *)
(*       '(c_body, renv) <- translate_cmd renv tm_body ;; *)
(*       c_body <- tmEval cbv c_body ;; *)
(*       renv <- tmEval cbv renv ;; *)
(*       tmReturn (c_while c_cond c_body, renv) *)
(*   | tCase _ _ tm0 [{| bbody := tm1 |} ; {| bbody := tm2 |}] => *)
(*       e <- translate_expr renv tm0 ;; *)
(*       '(c1, renv) <- translate_cmd renv tm1 ;; *)
(*       renv <- tmEval cbv renv ;; *)
(*       '(c2, renv) <- translate_cmd renv tm2 ;; *)
(*       renv <- tmEval cbv renv ;; *)
(*       tmReturn (c_if e c1 c2, renv) *)
(*   | tRel i => *)
(*       c <- *)
(*         match resolve_rel_fun renv i with *)
(*         | Some (_, (i, _)) => tmReturn (c_app i [], renv) *)
(*         | None => tmFail "Error in translate_cmd: invalid function" *)
(*         end *)
(*       ;; *)
(*       tmEval cbv c *)
(*   | tApp (tRel i) [tm] => *)
(*       e <- translate_expr renv tm ;; *)
(*       c <- match resolve_rel_fun renv i with *)
(*            | Some (_, (i, _)) => tmReturn (c_app i [ e ], renv) *)
(*            | None => tmFail "Error in translate_cmd: invalid function" *)
(*            end *)
(*       ;; *)
(*       tmEval cbv c *)
(*   | tApp (tConst (_, "with_var") []) [A; St; Hp; MS; tm_var; tm_cont] => *)
(*        t <- translate_storable MS;; *)
(*        '(c_var, renv) <- translate_cmd renv tm_var;; *)
(*        c_var <- tmEval cbv c_var;; *)
(*        renv <- tmEval cbv renv;; *)
(*        match tm_cont with *)
(*       | tLambda {| binder_name := binder |} tm4 tm3 => *)
(*           renv <- tmEval cbv (push_local renv t);; *)
(*           '(c_cont, renv) <- translate_cmd renv tm3 ;; *)
(*           c_cont <- tmEval cbv c_cont;; *)
(*           renv <- tmEval cbv renv;; *)
(*           tmReturn (c_with_var t c_var c_cont, renv) *)
(*       | _ => tmFail "Error in translate_cmd: not a continuation" *)
(*        end *)
(*   | tApp (tConst (_, "read_var") []) [St; Hp; MS; tRel i] => *)
(*       t <- translate_storable MS;; *)
(*       match resolve_rel_local renv i with *)
(*       | Some ofst => tmReturn (c_read_var ofst t, renv) *)
(*       | None => tmFail ("Error in translate_cmd: unbound local variable" ++ string_of_nat i) *)
(*       end *)
(*   | tApp (tConst (_, "write_var") []) [St; Hp; MS; tRel i; tm_val] => *)
(*       t <- translate_storable MS;; *)
(*       e_val <- translate_expr renv tm_val;; *)
(*       match resolve_rel_local renv i with *)
(*       | Some ofst => tmReturn (c_write_var ofst t e_val, renv) *)
(*       | None => tmFail ("Error in translate_cmd: unbound local variable" ++ string_of_nat i) *)
(*       end *)
(*   | tApp (tConst (_, "eq_ptr") []) [St; Hp; tm_l; tm_r] => *)
(*       e_l <- translate_expr renv tm_l;; *)
(*       e_r <- translate_expr renv tm_r;; *)
(*       tmReturn (c_ptr_eq e_l e_r, renv) *)
(*   | (tApp (tConst (_, "shift_fw_ptr") []) [St; Hp; tm1; tm2]) => *)
(*       e1 <- translate_expr renv tm1;; *)
(*       e2 <- translate_expr renv tm2;; *)
(*       tmReturn (c_shift_fw_ptr e1 e2, renv) *)
(*   | (tApp (tConst (_, "shift_bw_ptr") []) [St; Hp; tm1; tm2]) => *)
(*       e1 <- translate_expr renv tm1;; *)
(*       e2 <- translate_expr renv tm2;; *)
(*       tmReturn (c_shift_fw_ptr e1 e2, renv) *)
(*   | (tApp (tConst (_, "read_ptr") []) [St; Hp; MS; tm_p]) => *)
(*       e_p <- translate_expr renv tm_p;; *)
(*       t <- translate_storable MS;; *)
(*       tmReturn (c_read_ptr e_p t, renv) *)
(*   | (tApp (tConst (_, "write_ptr") []) [St; Hp; MS; tm_p; tm_val]) => *)
(*       e_p <- translate_expr renv tm_p;; *)
(*       t <- translate_storable MS;; *)
(*       e_val <- translate_expr renv tm_val;; *)
(*       tmReturn (c_write_ptr e_p t e_val, renv) *)
(*   | (tApp (tConst (_, "alloc_ptr") []) [St; Hp; MS; tm_sz; tm_init]) => *)
(*       e_sz <- translate_expr renv tm_sz;; *)
(*       t <- translate_storable MS;; *)
(*       e_init <- translate_expr renv tm_init ;; *)
(*       tmReturn (c_alloc_ptr e_sz t e_init, renv) *)
(*   | tConst (_, f) [] => *)
(*       c <- *)
(*         match resolve_named_fun renv f with *)
(*         | Some (f, _) => tmReturn (c_app f [], renv) *)
(*         | None => tmFail "Error in translate_cmd: invalid function" *)
(*         end *)
(*       ;; *)
(*       tmEval cbv c *)
(*   | _ => *)
(*       tmPrint tm;; *)
(*       tmPrint (reify_funbody_env_to_string renv);; *)
(*       tmFail "Error in translate_cmd: not a command" *)
(*   end. *)

(* Fixpoint translate_cmd' renv (tm : term) : TemplateMonad (cmd * reify_funbody_env) := *)
(*   match tm with *)
(*   | tLambda _ _ tm' => translate_cmd' renv tm' *)
(*   | _ => translate_cmd renv tm *)
(*   end. *)
