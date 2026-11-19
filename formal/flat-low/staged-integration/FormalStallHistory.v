Require Import CoreSocModel ComparisonNodes FormalStallNodes FormalStallConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma stall_eval_9215 old bit :
 VM.find 1 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_9215 old old = Some (Gval (Fuint 1) [::bit]).
Proof. intro Lookup. cbn [stall_expr_9215 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_9217 old bit :
 VM.find 1 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_9217 old old = Some (Gval (Fuint 1) [::bit]).
Proof. intro Lookup. cbn [stall_expr_9217 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_9216 old bit :
 VM.find 9215 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_9216 old old = Some (Gval (Fuint 1) [::negb bit]).
Proof. intro Lookup. cbn [stall_expr_9216 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_9218 old bit :
 VM.find 9217 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_9218 old old = Some (Gval (Fuint 1) [::negb bit]).
Proof. intro Lookup. cbn [stall_expr_9218 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_7763 old bit :
 VM.find 74 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_7763 old old = Some (Gval (Fuint 1) [::negb bit]).
Proof. intro Lookup. cbn [stall_expr_7763 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_7764 old bit :
 VM.find 81 old = Some (Gval (Fuint 1) [::bit]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_7764 old old = Some (Gval (Fuint 1) [::negb bit]).
Proof. intro Lookup. cbn [stall_expr_7764 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Lookup. destruct bit; reflexivity. Qed.
Lemma stall_eval_7765 old b1 b2 :
 VM.find 7763 old = Some (Gval (Fuint 1) [::b1]) ->
 VM.find 7764 old = Some (Gval (Fuint 1) [::b2]) ->
 eval_hfexpr_with_memory flat_memories stall_expr_7765 old old = Some (Gval (Fuint 1) [::b1 || b2]).
Proof. intros Left Right. cbn [stall_expr_7765 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Left Right. destruct b1,b2; reflexivity. Qed.
Theorem stall_after_six invalid s0 s1 s2 s3 s4 s5 s6 bit :
 VM.find 1 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 -> formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 -> formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 -> formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 7765 s6 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset S1 S2 S3 S4 S5 S6.
 pose proof (stall_node_9215 invalid s0 s0 s1 _ (stall_eval_9215 s0 bit Reset) (Logic.eq_refl _) S1) as I0.
 pose proof (stall_node_9217 invalid s0 s0 s1 _ (stall_eval_9217 s0 bit Reset) (Logic.eq_refl _) S1) as D0.
 pose proof (stall_node_9216 invalid s1 s1 s2 _ (stall_eval_9216 s1 bit I0) (Logic.eq_refl _) S2) as I1.
 pose proof (stall_node_9218 invalid s1 s1 s2 _ (stall_eval_9218 s1 bit D0) (Logic.eq_refl _) S2) as D1.
 pose proof (stall_connection_33_transfer invalid s2 s2 s3 _ I1 S3) as I2.
 pose proof (stall_connection_40_transfer invalid s2 s2 s3 _ D1 S3) as D2.
 pose proof (stall_connection_74_transfer invalid s3 s3 s4 _ I2 S4) as I3.
 pose proof (stall_connection_81_transfer invalid s3 s3 s4 _ D2 S4) as D3.
 pose proof (stall_node_7763 invalid s4 s4 s5 _ (stall_eval_7763 s4 _ I3) (Logic.eq_refl _) S5) as I4.
 pose proof (stall_node_7764 invalid s4 s4 s5 _ (stall_eval_7764 s4 _ D3) (Logic.eq_refl _) S5) as D4.
 pose proof (stall_node_7765 invalid s5 s5 s6 _ (stall_eval_7765 s5 _ _ I4 D4) (Logic.eq_refl _) S6) as Last.
 destruct bit; exact Last.
Qed.
Print Assumptions stall_after_six.
