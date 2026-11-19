Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_address_select_expr_8003 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Eref VarOrder.T (@Eid VarOrder.T 7752)) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Definition store_address_select_nodes := [::(8003,store_address_select_expr_8003)].
Definition store_address_select_offsets := [::8509%nat].
Lemma store_address_select_positions : select_node_offsets store_address_select_offsets flat_statements=Some store_address_select_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_address_select_safety : selected_node_safety flat_memories flat_statements store_address_select_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_address_select_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_address_select_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_address_select_offsets store_address_select_nodes node expr);
 [exact store_address_select_positions|exact store_address_select_safety|exact Member|exact Eval|exact Step].
Qed.
