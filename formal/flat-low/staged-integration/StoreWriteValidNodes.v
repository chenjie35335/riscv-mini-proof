Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_write_valid_expr_8030 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 8028)) (@Eref VarOrder.T (@Eid VarOrder.T 8029))).
Definition store_write_valid_expr_8081 := (@Eref VarOrder.T (@Eid VarOrder.T 8030)).
Definition store_write_valid_expr_8082 := (@Eref VarOrder.T (@Eid VarOrder.T 8081)).
Definition store_write_valid_expr_8202 := (@Eref VarOrder.T (@Eid VarOrder.T 8082)).
Definition store_write_valid_nodes := [::(8030,store_write_valid_expr_8030);(8081,store_write_valid_expr_8081);(8082,store_write_valid_expr_8082);(8202,store_write_valid_expr_8202)].
Definition store_write_valid_offsets := [::8536%nat;50%nat;0%nat;119%nat].
Lemma store_write_valid_positions : select_node_offsets store_write_valid_offsets flat_statements=Some store_write_valid_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_write_valid_safety : selected_node_safety flat_memories flat_statements store_write_valid_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_write_valid_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_write_valid_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_write_valid_offsets store_write_valid_nodes node expr);
 [exact store_write_valid_positions|exact store_write_valid_safety|exact Member|exact Eval|exact Step].
Qed.
