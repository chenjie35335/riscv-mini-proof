Require Import FormalRFWritebackNodes.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_source_expr_953 := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 785))).
Definition rf_source_tail_953 := match straight_drop 963 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_953 : straight_drop 962 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 953 rf_source_expr_953) rf_source_tail_953).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_953 : formal_typed_suffix_safe flat_memories 953 rf_source_tail_953.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_953 : has_register 953 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_953 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_953 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 953 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_953|exact rf_source_suffix_953|exact rf_source_nonregister_953|exact Eval|exact Typed|exact Step]. Qed.

Theorem rf_address_nonzero_node invalid old current result address :
 VM.find 785 old = Some (Gval (Fuint 5) address) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 953 result = Some (Gval (Fuint 1) [::foldr orb false address]).
Proof.
 intros Address Step.
 apply (rf_source_node_953 invalid old current result (Gval (Fuint 1) [::foldr orb false address]));
 [|reflexivity|exact Step].
 unfold rf_source_expr_953. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Address. reflexivity.
Qed.
Theorem rf_write_enable_node invalid old current result enabled nonzero :
 VM.find 784 old = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 953 old = Some (Gval (Fuint 1) [::nonzero]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 954 result = Some (Gval (Fuint 1) [::enabled && nonzero]).
Proof.
 intros Enabled Nonzero Step.
 apply (rf_source_node_954 invalid old current result (Gval (Fuint 1) [::enabled && nonzero]));
 [|reflexivity|exact Step].
 unfold rf_source_expr_954. cbn [eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Enabled Nonzero. destruct enabled, nonzero; reflexivity.
Qed.
Print Assumptions rf_write_enable_node.
