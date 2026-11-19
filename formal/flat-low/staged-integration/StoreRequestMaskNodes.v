Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_request_mask_expr_7838 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Eref VarOrder.T (@Eid VarOrder.T 7754)) (@Eref VarOrder.T (@Eid VarOrder.T 91))).
Definition store_request_mask_expr_7839 := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Definition store_request_mask_expr_7840 := (@Eprim_binop VarOrder.T Bdshl (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7839))).
Definition store_request_mask_expr_7841 := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 1155))).
Definition store_request_mask_expr_7842 := (@Eprim_binop VarOrder.T Bdshl (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7841))).
Definition store_request_mask_expr_7843 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Definition store_request_mask_expr_7844 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7843)) (@Econst VarOrder.T (Fuint 4) [::true; true; true; true]) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition store_request_mask_expr_7845 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Definition store_request_mask_expr_7846 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7845)) (@Eref VarOrder.T (@Eid VarOrder.T 7840)) (@Eref VarOrder.T (@Eid VarOrder.T 7844))).
Definition store_request_mask_expr_7847 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 7838))).
Definition store_request_mask_expr_7848 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 7847)) (@Eref VarOrder.T (@Eid VarOrder.T 7842)) (@Eref VarOrder.T (@Eid VarOrder.T 7846))).
Definition store_request_mask_nodes := [::(7838,store_request_mask_expr_7838);(7839,store_request_mask_expr_7839);(7840,store_request_mask_expr_7840);(7841,store_request_mask_expr_7841);(7842,store_request_mask_expr_7842);(7843,store_request_mask_expr_7843);(7844,store_request_mask_expr_7844);(7845,store_request_mask_expr_7845);(7846,store_request_mask_expr_7846);(7847,store_request_mask_expr_7847);(7848,store_request_mask_expr_7848)].
Definition store_request_mask_offsets := [::8344%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma store_request_mask_positions : select_node_offsets store_request_mask_offsets flat_statements=Some store_request_mask_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_request_mask_safety : selected_node_safety flat_memories flat_statements store_request_mask_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_request_mask_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_request_mask_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_request_mask_offsets store_request_mask_nodes node expr);
 [exact store_request_mask_positions|exact store_request_mask_safety|exact Member|exact Eval|exact Step].
Qed.
