From GallinaC.Compiler.Common Require Import Types Ctxt Value Expr.
From GallinaC.Compiler.Deep Require Import Cmd Prog Typing.
From GallinaC.Compiler.Deep Require Export OpSem Denotation.
Import OpSem.Typing(wt_state).

(* Semantic agreement between operational and denotational semantics *)
(* [step] evaluation (between well-typed states) preserves denotation *)
Lemma step_correct {St Hp}
  {p: Prog.program} {events} {s s': @state St Hp}
  (WTp: Typing.wt_program p)
  (WTs: wt_state p s)
  (WTs': wt_state p s')
  (STEP: step (Globalenvs.Genv.globalenv p) s events s') :
  denote_state WTp WTs = denote_state WTp WTs'.
Proof.
Admitted.
