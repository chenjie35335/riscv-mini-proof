Require Import CoreSocModel ComparisonNodes FormalPCIncrementNodes FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma pc_normal_add_concrete old pc :
 VM.find 7768 old = Some (Gval (Fuint 33) pc) ->
 exists word, eval_hfexpr_with_memory flat_memories pc_normal_expr_7769 old old = Some (Gval (Fuint 34) word).
Proof. intro Value. cbn [pc_normal_expr_7769 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Value. eexists. reflexivity. Qed.
Lemma pc_normal_tail_concrete old word :
 VM.find 7769 old = Some (Gval (Fuint 34) word) ->
 exists reset_word, eval_hfexpr_with_memory flat_memories pc_normal_expr_7770 old old = Some (Gval (Fuint 33) reset_word).
Proof.
 intro Value. cbn [pc_normal_expr_7770 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. eexists. reflexivity.
Qed.
Theorem pc_increment_after_two invalid s0 s1 s2 pc :
 VM.find 7768 s0 = Some (Gval (Fuint 33) pc) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 exists word, VM.find 7770 s2 = Some (Gval (Fuint 33) word).
Proof.
 intros PC First Second.
 destruct (pc_normal_add_concrete s0 pc PC) as [word Eval].
 assert (Middle : VM.find 7769 s1 = Some (Gval (Fuint 34) word)).
 { eapply pc_normal_node_7769; [exact Eval|reflexivity|exact First]. }
 destruct (pc_normal_tail_concrete s1 word Middle) as [reset_word Tail].
 exists reset_word. eapply pc_normal_node_7770; [exact Tail|reflexivity|exact Second].
Qed.
Print Assumptions pc_increment_after_two.
