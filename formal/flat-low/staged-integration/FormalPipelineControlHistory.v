Require Import CoreSocModel ComparisonNodes FormalPipelineControlNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma pipeline_eval_7849 old b1 :
 VM.find 65 old = Some (Gval (Fuint 1) [::b1]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7849 old old = Some (Gval (Fuint 1) [::b1]).
Proof. intros Hb1. cbn [pipeline_expr_7849 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1. destruct b1; reflexivity. Qed.
Lemma pipeline_eval_7850 old b1 :
 VM.find 7765 old = Some (Gval (Fuint 1) [::b1]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7850 old old = Some (Gval (Fuint 1) [::negb b1]).
Proof. intros Hb1. cbn [pipeline_expr_7850 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1. destruct b1; reflexivity. Qed.
Lemma pipeline_eval_7851 old b1 b2 :
 VM.find 7850 old = Some (Gval (Fuint 1) [::b1]) ->
 VM.find 128 old = Some (Gval (Fuint 1) [::b2]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7851 old old = Some (Gval (Fuint 1) [::b1 && b2]).
Proof. intros Hb1 Hb2. cbn [pipeline_expr_7851 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1 Hb2. destruct b1,b2; reflexivity. Qed.
Lemma pipeline_eval_7852 old b1 b2 :
 VM.find 7849 old = Some (Gval (Fuint 1) [::b1]) ->
 VM.find 7851 old = Some (Gval (Fuint 1) [::b2]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7852 old old = Some (Gval (Fuint 1) [::b1 || b2]).
Proof. intros Hb1 Hb2. cbn [pipeline_expr_7852 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1 Hb2. destruct b1,b2; reflexivity. Qed.
Lemma pipeline_eval_7853 old b1 :
 VM.find 7765 old = Some (Gval (Fuint 1) [::b1]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7853 old old = Some (Gval (Fuint 1) [::negb b1]).
Proof. intros Hb1. cbn [pipeline_expr_7853 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1. destruct b1; reflexivity. Qed.
Lemma pipeline_eval_7854 old b1 :
 VM.find 128 old = Some (Gval (Fuint 1) [::b1]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7854 old old = Some (Gval (Fuint 1) [::negb b1]).
Proof. intros Hb1. cbn [pipeline_expr_7854 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1. destruct b1; reflexivity. Qed.
Lemma pipeline_eval_7855 old b1 b2 :
 VM.find 7853 old = Some (Gval (Fuint 1) [::b1]) ->
 VM.find 7854 old = Some (Gval (Fuint 1) [::b2]) ->
 eval_hfexpr_with_memory flat_memories pipeline_expr_7855 old old = Some (Gval (Fuint 1) [::b1 && b2]).
Proof. intros Hb1 Hb2. cbn [pipeline_expr_7855 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Hb1 Hb2. destruct b1,b2; reflexivity. Qed.
Theorem pipeline_advance_after_two invalid s0 s1 s2 stall exception :
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 128 s0 = Some (Gval (Fuint 1) [::exception]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 -> formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7855 s2 = Some (Gval (Fuint 1) [::negb stall && negb exception]).
Proof.
 intros Stall Exception S1 S2.
 pose proof (pipeline_node_7853 invalid s0 s0 s1 _ (pipeline_eval_7853 s0 stall Stall) (Logic.eq_refl _) S1) as A.
 pose proof (pipeline_node_7854 invalid s0 s0 s1 _ (pipeline_eval_7854 s0 exception Exception) (Logic.eq_refl _) S1) as B.
 exact (pipeline_node_7855 invalid s1 s1 s2 _ (pipeline_eval_7855 s1 _ _ A B) (Logic.eq_refl _) S2).
Qed.
Theorem pipeline_flush_after_three invalid s0 s1 s2 s3 stall exception reset :
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 128 s1 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 65 s1 = Some (Gval (Fuint 1) [::reset]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 -> formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 -> formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 7852 s3 = Some (Gval (Fuint 1) [::reset || (negb stall && exception)]).
Proof.
 intros Stall Exception Reset S1 S2 S3.
 pose proof (pipeline_node_7850 invalid s0 s0 s1 _ (pipeline_eval_7850 s0 stall Stall) (Logic.eq_refl _) S1) as A.
 pose proof (pipeline_node_7851 invalid s1 s1 s2 _ (pipeline_eval_7851 s1 _ exception A Exception) (Logic.eq_refl _) S2) as B.
 pose proof (pipeline_node_7849 invalid s1 s1 s2 _ (pipeline_eval_7849 s1 reset Reset) (Logic.eq_refl _) S2) as C.
 exact (pipeline_node_7852 invalid s2 s2 s3 _ (pipeline_eval_7852 s2 _ _ C B) (Logic.eq_refl _) S3).
Qed.
Print Assumptions pipeline_flush_after_three.
