Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_shift_expression := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7819)) (@Eref VarOrder.T (@Eid VarOrder.T 7831))).
Definition store_shift_nodes := [::(7837,store_shift_expression)].
Definition store_shift_offsets := [::8343%nat].
Lemma store_shift_positions : select_node_offsets store_shift_offsets flat_statements=Some store_shift_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_shift_safety : selected_node_safety flat_memories flat_statements store_shift_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_shift_node_step invalid old current result ground bits :
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories store_shift_expression old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7837 result=Some(Gval ground bits).
Proof.
 intros Eval Step. eapply(reference_redirect_ground_step store_shift_offsets store_shift_nodes 7837 store_shift_expression);
 [exact store_shift_positions|exact store_shift_safety|left;reflexivity|exact Eval|exact Step].
Qed.
