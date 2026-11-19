Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_mask_expr_8008 := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 7924))).
Definition store_mask_expr_8009 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8008)) (@Econst VarOrder.T (Fuint 8) [::true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 8) [::false; false; false; false; false; false; false; false])).
Definition store_mask_expr_8010 := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 7924))).
Definition store_mask_expr_8011 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8010)) (@Econst VarOrder.T (Fuint 8) [::true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 8) [::false; false; false; false; false; false; false; false])).
Definition store_mask_expr_8012 := (@Eprim_unop VarOrder.T (Uextr 2 2) (@Eref VarOrder.T (@Eid VarOrder.T 7924))).
Definition store_mask_expr_8013 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8012)) (@Econst VarOrder.T (Fuint 8) [::true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 8) [::false; false; false; false; false; false; false; false])).
Definition store_mask_expr_8014 := (@Eprim_unop VarOrder.T (Uextr 3 3) (@Eref VarOrder.T (@Eid VarOrder.T 7924))).
Definition store_mask_expr_8015 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 8014)) (@Econst VarOrder.T (Fuint 8) [::true; true; true; true; true; true; true; true]) (@Econst VarOrder.T (Fuint 8) [::false; false; false; false; false; false; false; false])).
Definition store_mask_expr_8016 := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 8011)) (@Eref VarOrder.T (@Eid VarOrder.T 8009))).
Definition store_mask_expr_8017 := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 8015)) (@Eref VarOrder.T (@Eid VarOrder.T 8013))).
Definition store_mask_expr_8018 := (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 8017)) (@Eref VarOrder.T (@Eid VarOrder.T 8016))).
Definition store_mask_nodes := [::(8008,store_mask_expr_8008);(8009,store_mask_expr_8009);(8010,store_mask_expr_8010);(8011,store_mask_expr_8011);(8012,store_mask_expr_8012);(8013,store_mask_expr_8013);(8014,store_mask_expr_8014);(8015,store_mask_expr_8015);(8016,store_mask_expr_8016);(8017,store_mask_expr_8017);(8018,store_mask_expr_8018)].
Definition store_mask_offsets := [::8514%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma store_mask_positions : select_node_offsets store_mask_offsets flat_statements=Some store_mask_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_mask_safety : selected_node_safety flat_memories flat_statements store_mask_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_mask_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_mask_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_mask_offsets store_mask_nodes node expr);
 [exact store_mask_positions|exact store_mask_safety|exact Member|exact Eval|exact Step].
Qed.
