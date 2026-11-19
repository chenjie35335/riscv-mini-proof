Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_checker_data_expr_8087 := (@Eref VarOrder.T (@Eid VarOrder.T 8039)).
Definition store_checker_data_expr_8088 := (@Eref VarOrder.T (@Eid VarOrder.T 8087)).
Definition store_checker_data_expr_8205 := (@Eref VarOrder.T (@Eid VarOrder.T 8088)).
Definition store_checker_data_nodes := [::(8087,store_checker_data_expr_8087);(8088,store_checker_data_expr_8088);(8205,store_checker_data_expr_8205)].
Definition store_checker_data_offsets := [::8593%nat;0%nat;116%nat].
Lemma store_checker_data_positions : select_node_offsets store_checker_data_offsets flat_statements=Some store_checker_data_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_checker_data_safety : selected_node_safety flat_memories flat_statements store_checker_data_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_checker_data_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_checker_data_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_checker_data_offsets store_checker_data_nodes node expr);
 [exact store_checker_data_positions|exact store_checker_data_safety|exact Member|exact Eval|exact Step].
Qed.
