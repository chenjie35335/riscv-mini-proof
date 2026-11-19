Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_offset_expr_7827 := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Definition store_offset_expr_7828 := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7827)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Definition store_offset_expr_7829 := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Definition store_offset_expr_7830 := (@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 7829)) (@Econst VarOrder.T (Fuint 2) [::true; true])).
Definition store_offset_expr_7831 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7828)) (@Eref VarOrder.T (@Eid VarOrder.T 7830))).
Definition store_offset_nodes := [::(7827,store_offset_expr_7827);(7828,store_offset_expr_7828);(7829,store_offset_expr_7829);(7830,store_offset_expr_7830);(7831,store_offset_expr_7831)].
Definition store_offset_offsets := [::8333%nat;0%nat;0%nat;0%nat;0%nat].
Lemma store_offset_positions : select_node_offsets store_offset_offsets flat_statements=Some store_offset_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_offset_safety : selected_node_safety flat_memories flat_statements store_offset_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_offset_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_offset_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_offset_offsets store_offset_nodes node expr);
 [exact store_offset_positions|exact store_offset_safety|exact Member|exact Eval|exact Step].
Qed.
