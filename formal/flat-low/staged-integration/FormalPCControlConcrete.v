Require Import CoreSocModel ComparisonNodes FormalPCControlNodes FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma pc_control_eval_7771 old width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 exists bit, eval_hfexpr_with_memory flat_memories pc_control_expr_7771 old old = Some (Gval (Fuint 1) [::bit]).
Proof.
 intro Value. cbn [pc_control_expr_7771 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. destruct width as [|[|width]]; eexists; reflexivity.
Qed.
Theorem pc_control_concrete_7771 invalid old current result width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bit, VM.find 7771 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Value Step. destruct (pc_control_eval_7771 old width word Value) as [bit Eval].
 exists bit. eapply pc_control_node_7771; [exact Eval|reflexivity|exact Step].
Qed.
Lemma pc_control_eval_7772 old width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 exists bit, eval_hfexpr_with_memory flat_memories pc_control_expr_7772 old old = Some (Gval (Fuint 1) [::bit]).
Proof.
 intro Value. cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. destruct width as [|[|width]]; eexists; reflexivity.
Qed.
Theorem pc_control_concrete_7772 invalid old current result width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bit, VM.find 7772 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Value Step. destruct (pc_control_eval_7772 old width word Value) as [bit Eval].
 exists bit. eapply pc_control_node_7772; [exact Eval|reflexivity|exact Step].
Qed.
Lemma pc_control_eval_7776 old width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 exists bit, eval_hfexpr_with_memory flat_memories pc_control_expr_7776 old old = Some (Gval (Fuint 1) [::bit]).
Proof.
 intro Value. cbn [pc_control_expr_7776 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. destruct width as [|[|width]]; eexists; reflexivity.
Qed.
Theorem pc_control_concrete_7776 invalid old current result width word :
 VM.find 84 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bit, VM.find 7776 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Value Step. destruct (pc_control_eval_7776 old width word Value) as [bit Eval].
 exists bit. eapply pc_control_node_7776; [exact Eval|reflexivity|exact Step].
Qed.
Theorem pc_control_concrete_7773 invalid old current result a b :
 VM.find 7772 old = Some (Gval (Fuint 1) [::a]) ->
 VM.find 1360 old = Some (Gval (Fuint 1) [::b]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bit, VM.find 7773 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Left Right Step.
 assert (Eval : exists bit, eval_hfexpr_with_memory flat_memories pc_control_expr_7773 old old = Some (Gval (Fuint 1) [::bit])).
 { cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Left Right. destruct a, b; eexists; reflexivity. }
 destruct Eval as [bit Eval]. exists bit.
 eapply pc_control_node_7773; [exact Eval|reflexivity|exact Step].
Qed.
Print Assumptions pc_control_concrete_7773.
