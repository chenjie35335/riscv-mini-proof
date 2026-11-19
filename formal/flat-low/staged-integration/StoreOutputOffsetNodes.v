Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_output_offset_expr_8031 := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 8004))).
Definition store_output_offset_expr_8032 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 8031))).
Definition store_output_offset_expr_8033 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8032)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Econst VarOrder.T (Fuint 4) [::false; false; false; false])).
Definition store_output_offset_expr_8034 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8031))).
Definition store_output_offset_expr_8035 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8034)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8033))).
Definition store_output_offset_expr_8036 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8031))).
Definition store_output_offset_expr_8037 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8036)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 8035))).
Definition store_output_offset_nodes := [::(8031,store_output_offset_expr_8031);(8032,store_output_offset_expr_8032);(8033,store_output_offset_expr_8033);(8034,store_output_offset_expr_8034);(8035,store_output_offset_expr_8035);(8036,store_output_offset_expr_8036);(8037,store_output_offset_expr_8037)].
Definition store_output_offset_offsets := [::8537%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma store_output_offset_positions : select_node_offsets store_output_offset_offsets flat_statements=Some store_output_offset_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_output_offset_safety : selected_node_safety flat_memories flat_statements store_output_offset_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_output_offset_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_output_offset_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_output_offset_offsets store_output_offset_nodes node expr);
 [exact store_output_offset_positions|exact store_output_offset_safety|exact Member|exact Eval|exact Step].
Qed.
