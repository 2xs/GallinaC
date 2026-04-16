From Stdlib Require Import PArith Arith.

From MetaRocq.Template Require Import All.

From GallinaC.Utils Require Import ListExt.

From GallinaC.Compiler.Deep Require Import Prog.
From GallinaC.Compiler.Reify Require Export Common Types Env Expr Cmd.

Import MRMonadNotation.
Local Open Scope bs_scope.

Polymorphic Fixpoint allocate_args_id renv (args: list (string * type)): TemplateMonad (list (string * (AST.ident * type)) * reify_program_env) :=
  match args with
  | [] => tmReturn ([], renv)
  | (mr_id, t_arg)::args =>
      cc_id <- tmEval cbv renv.(next_id);;
      renv <- tmEval cbv {| next_id := Pos.succ renv.(next_id); funs := renv.(funs); current_module := renv.(current_module); |};;
      '(args, renv) <- allocate_args_id renv args;;
      tmEval cbv ((mr_id, (cc_id, t_arg))::args, renv)
  end.

Polymorphic Definition mk_reify_funbody_stack (args: list (string * (AST.ident * type))): list binding :=
  List.map (fun '(mr_id, (cc_id, t_arg)) => Param mr_id cc_id t_arg) (List.rev args).

Polymorphic Definition mk_reify_funbody_env (renv: reify_program_env) (args: list (string * (AST.ident * type))) : TemplateMonad (reify_funbody_env) :=
  tmEval cbv {| prog_renv := renv; stack := mk_reify_funbody_stack args; stack_depth := 0; temps := []; |}.

Polymorphic Fixpoint translate_funbody (renv: reify_funbody_env) (body : term) : TemplateMonad (cmd * reify_funbody_env) :=
  match body with
  | tLam _ _ body =>
      translate_funbody renv body
  | body =>
      translate_cmd renv body
  end.

Polymorphic Definition translate_function (renv: reify_program_env) (mr_id: ident) (args: list (string * type)) (t_out: type) (body : term) : TemplateMonad reify_program_env :=
  '(params, renv) <- allocate_args_id renv args;;
  params <- tmEval cbv params;;
  renv <- mk_reify_funbody_env renv params;;
  '(body, renv) <- translate_funbody renv body;;
  tfunction <- tmEval cbv
                      {|
                        fn_return := t_out;
                        fn_params := List.map snd params;
                        fn_temps := renv.(temps);
                        fn_body := body;
                        fn_extra := tt;
      |};;
  tmEval cbv (push_fun renv mr_id tfunction).

Polymorphic Fixpoint translate_module (renv: reify_program_env) (module: list global_reference): TemplateMonad reify_program_env :=
  match module with
  | ConstRef ((_, f_name) as kname)::module =>
      tm <- tmUnquote (tConst kname []);;
      f_sig <- tmEval cbn tm.(my_projT1);;
      f_sig <- tmQuote f_sig;;
      '(args, t_out) <- translate_signature f_sig;;
      body <- tmEval cbn tm.(my_projT2);;
      body <- tmEval (unfold kname) body;;
      body <- tmQuote body;;
      renv <- translate_function renv f_name args t_out body;;
      translate_module renv module
  | [] => tmReturn renv
  | gref::_ => tmMsg "translate_module: Unsupported global reference";; tmPrint gref;; tmFail ""
  end.

Polymorphic Definition reify_program (module main boundname: qualid): TemplateMonad program :=
  path <- tmLocateModule1 module;;
  M <- tmQuoteModule module;;
  renv <- translate_module (init_reify_env path) M;;
  match List.find (fun '(mr_id, _) => String.eqb mr_id main) renv.(funs) with
  | Some (_, (id_main, _)) =>
      prog <-
        tmEval cbv
               {|
                 prog_defs := List.rev (List.map (fun '(_, (gc_id, f)) => (gc_id, AST.Gfun (AST.Internal f))) renv.(funs));
                 prog_public := [id_main];
                 prog_main := id_main;
                 prog_extra := {| prog_next_id := renv.(next_id); |};
               |};;
      tmDefinition boundname prog
  | None => tmFail "Unable to find main function"
  end.
