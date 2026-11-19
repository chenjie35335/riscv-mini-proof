Require Import ComparisonNodes FormalNodeEquation.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_memory.
From Coq Require Import ZArith.
From simplssrlib Require Import Var.
Local Open Scope N_scope.
Lemma formal_comparison_0_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7565 result = eval_hfexpr_with_memory flat_memories comparison_0 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_0 suffix_0 nonregister_0 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_1_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7570 result = eval_hfexpr_with_memory flat_memories comparison_1 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_1 suffix_1 nonregister_1 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_2_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7574 result = eval_hfexpr_with_memory flat_memories comparison_2 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_2 suffix_2 nonregister_2 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_3_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7578 result = eval_hfexpr_with_memory flat_memories comparison_3 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_3 suffix_3 nonregister_3 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_4_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7583 result = eval_hfexpr_with_memory flat_memories comparison_4 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_4 suffix_4 nonregister_4 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_5_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7587 result = eval_hfexpr_with_memory flat_memories comparison_5 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_5 suffix_5 nonregister_5 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_6_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7591 result = eval_hfexpr_with_memory flat_memories comparison_6 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_6 suffix_6 nonregister_6 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_7_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7595 result = eval_hfexpr_with_memory flat_memories comparison_7 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_7 suffix_7 nonregister_7 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_8_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7599 result = eval_hfexpr_with_memory flat_memories comparison_8 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_8 suffix_8 nonregister_8 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_9_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7603 result = eval_hfexpr_with_memory flat_memories comparison_9 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_9 suffix_9 nonregister_9 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_10_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7607 result = eval_hfexpr_with_memory flat_memories comparison_10 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_10 suffix_10 nonregister_10 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_11_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7611 result = eval_hfexpr_with_memory flat_memories comparison_11 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_11 suffix_11 nonregister_11 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_12_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7615 result = eval_hfexpr_with_memory flat_memories comparison_12 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_12 suffix_12 nonregister_12 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_13_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7619 result = eval_hfexpr_with_memory flat_memories comparison_13 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_13 suffix_13 nonregister_13 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_14_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7623 result = eval_hfexpr_with_memory flat_memories comparison_14 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_14 suffix_14 nonregister_14 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_15_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7627 result = eval_hfexpr_with_memory flat_memories comparison_15 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_15 suffix_15 nonregister_15 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_16_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7631 result = eval_hfexpr_with_memory flat_memories comparison_16 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_16 suffix_16 nonregister_16 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_17_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7635 result = eval_hfexpr_with_memory flat_memories comparison_17 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_17 suffix_17 nonregister_17 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_18_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7639 result = eval_hfexpr_with_memory flat_memories comparison_18 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_18 suffix_18 nonregister_18 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_19_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7643 result = eval_hfexpr_with_memory flat_memories comparison_19 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_19 suffix_19 nonregister_19 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_20_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7647 result = eval_hfexpr_with_memory flat_memories comparison_20 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_20 suffix_20 nonregister_20 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_21_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7651 result = eval_hfexpr_with_memory flat_memories comparison_21 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_21 suffix_21 nonregister_21 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_22_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7655 result = eval_hfexpr_with_memory flat_memories comparison_22 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_22 suffix_22 nonregister_22 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_23_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7659 result = eval_hfexpr_with_memory flat_memories comparison_23 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_23 suffix_23 nonregister_23 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_24_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7663 result = eval_hfexpr_with_memory flat_memories comparison_24 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_24 suffix_24 nonregister_24 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_25_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7667 result = eval_hfexpr_with_memory flat_memories comparison_25 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_25 suffix_25 nonregister_25 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_26_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7671 result = eval_hfexpr_with_memory flat_memories comparison_26 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_26 suffix_26 nonregister_26 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_27_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7675 result = eval_hfexpr_with_memory flat_memories comparison_27 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_27 suffix_27 nonregister_27 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_28_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7679 result = eval_hfexpr_with_memory flat_memories comparison_28 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_28 suffix_28 nonregister_28 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_29_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7683 result = eval_hfexpr_with_memory flat_memories comparison_29 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_29 suffix_29 nonregister_29 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_30_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7687 result = eval_hfexpr_with_memory flat_memories comparison_30 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_30 suffix_30 nonregister_30 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_31_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7691 result = eval_hfexpr_with_memory flat_memories comparison_31 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_31 suffix_31 nonregister_31 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_32_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7695 result = eval_hfexpr_with_memory flat_memories comparison_32 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_32 suffix_32 nonregister_32 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_33_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7699 result = eval_hfexpr_with_memory flat_memories comparison_33 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_33 suffix_33 nonregister_33 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_34_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7703 result = eval_hfexpr_with_memory flat_memories comparison_34 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_34 suffix_34 nonregister_34 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_35_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7707 result = eval_hfexpr_with_memory flat_memories comparison_35 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_35 suffix_35 nonregister_35 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_36_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7711 result = eval_hfexpr_with_memory flat_memories comparison_36 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_36 suffix_36 nonregister_36 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_37_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7715 result = eval_hfexpr_with_memory flat_memories comparison_37 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_37 suffix_37 nonregister_37 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_38_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7719 result = eval_hfexpr_with_memory flat_memories comparison_38 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_38 suffix_38 nonregister_38 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_39_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7723 result = eval_hfexpr_with_memory flat_memories comparison_39 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_39 suffix_39 nonregister_39 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_40_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7728 result = eval_hfexpr_with_memory flat_memories comparison_40 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_40 suffix_40 nonregister_40 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_41_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7732 result = eval_hfexpr_with_memory flat_memories comparison_41 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_41 suffix_41 nonregister_41 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_42_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7736 result = eval_hfexpr_with_memory flat_memories comparison_42 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_42 suffix_42 nonregister_42 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_43_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7740 result = eval_hfexpr_with_memory flat_memories comparison_43 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_43 suffix_43 nonregister_43 Step) as Equation.
 exact Equation.
Qed.
Lemma formal_comparison_44_iteration invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7744 result = eval_hfexpr_with_memory flat_memories comparison_44 old old.
Proof.
 intro Step.
 pose proof (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
   position_44 suffix_44 nonregister_44 Step) as Equation.
 exact Equation.
Qed.
