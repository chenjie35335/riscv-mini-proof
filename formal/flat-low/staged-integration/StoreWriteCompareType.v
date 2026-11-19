Require Import StoreWriteCompareNode NopBranchShapes FormalTypedNodeEquation FormalSuccessfulNodeEvaluation SelectedNodeSafety NormalizedBit CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_gt_zero_normalized value result :
 eval_binop (Bcomp Bgt) value (Gval (Fuint 1) [::false]) = Some result ->
 normalized_bit result.
Proof.
 destruct value as [ground bits|element array|bundle|t|t|t];
 unfold eval_binop, absorbing_bit, refine_boolean_result, eval_binop_basic;
 try (intro H; discriminate H).
 all: try destruct ground; try destruct t.
 all: try match goal with x : fgtyp |- _ => destruct x end.
 all: cbn; intro H.
 all: repeat match type of H with context [if ?b then _ else _] => destruct b end.
 all: cbn in H; try discriminate H; inversion H; subst; constructor.
Qed.

Lemma store_write_compare_type_step invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists value,VM.find 8027 result=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intro Step.
 assert(Member:List.In(8027,store_write_compare_expr_8027)store_write_compare_nodes)by(left;reflexivity).
 destruct(selected_node_safe_position flat_memories flat_statements store_write_compare_offsets flat_statements store_write_compare_nodes 8027 store_write_compare_expr_8027
 store_write_compare_positions store_write_compare_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail 8027 store_write_compare_expr_8027 invalid flat_memories old false current result Position Step)as[value Eval].
 rewrite add0n in Eval.
 assert(Typed:type_of_val value=Gtyp(Fuint 1)).
 { apply nop_branch_normalized_type. cbn[store_write_compare_expr_8027 eval_hfexpr_validif_policy eval_href_validif_policy]in Eval.
   destruct(VM.find 8002 old)as[source|];[|discriminate]. exact(store_write_gt_zero_normalized source value Eval). }
 exists value. split;[|exact Typed].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem store_write_compare_observed_type memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 exists value,VM.find 8027(top_environment observed)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Observe Legal.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite <-Last. exact(store_write_compare_type_step _ (history 9258%nat)(history 9258%nat)(history 9259%nat)(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
