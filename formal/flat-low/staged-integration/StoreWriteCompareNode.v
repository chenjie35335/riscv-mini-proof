Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_write_compare_expr_8027 := (@Eprim_binop VarOrder.T (Bcomp Bgt) (@Eref VarOrder.T (@Eid VarOrder.T 8002)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition store_write_compare_nodes := [::(8027,store_write_compare_expr_8027)].
Definition store_write_compare_offsets := [::8533%nat].
Lemma store_write_compare_positions : select_node_offsets store_write_compare_offsets flat_statements=Some store_write_compare_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_write_compare_safety : selected_node_safety flat_memories flat_statements store_write_compare_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_write_compare_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_write_compare_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_write_compare_offsets store_write_compare_nodes node expr);
 [exact store_write_compare_positions|exact store_write_compare_safety|exact Member|exact Eval|exact Step].
Qed.
