Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_output_expr_8038 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7925)) (@Eref VarOrder.T (@Eid VarOrder.T 8018))).
Definition store_output_expr_8039 := (@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 8038)) (@Eref VarOrder.T (@Eid VarOrder.T 8037))).
Definition store_output_nodes := [::(8038,store_output_expr_8038);(8039,store_output_expr_8039)].
Definition store_output_offsets := [::8544%nat;0%nat].
Lemma store_output_positions : select_node_offsets store_output_offsets flat_statements=Some store_output_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_output_safety : selected_node_safety flat_memories flat_statements store_output_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_output_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_output_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_output_offsets store_output_nodes node expr);
 [exact store_output_positions|exact store_output_safety|exact Member|exact Eval|exact Step].
Qed.
