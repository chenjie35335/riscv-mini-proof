Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Require Import FormalRFDataShape.
Definition rf_source_expr_988 := (@Eref VarOrder.T (@Eid VarOrder.T 786)).
Definition rf_source_tail_988 := match straight_drop 998 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_source_position_988 : straight_drop 997 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 988 rf_source_expr_988) rf_source_tail_988).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_source_suffix_988 : formal_typed_suffix_safe flat_memories 988 rf_source_tail_988.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_source_nonregister_988 : has_register 988 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_source_node_988 invalid old current result value :
 eval_hfexpr_with_memory flat_memories rf_source_expr_988 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 988 result = Some value.
Proof. intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact rf_source_position_988|exact rf_source_suffix_988|exact rf_source_nonregister_988|exact Eval|exact Typed|exact Step]. Qed.
Theorem x0_write_data_typed_after_two invalid old middle result :
 formal_value_iter invalid flat_memories old false old flat_statements = Some middle ->
 formal_value_iter invalid flat_memories middle false middle flat_statements = Some result ->
 exists value, VM.find 988 result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros First Second.
 destruct (rf_input_data_typed invalid old old middle First) as [value [Value Typed]].
 exists value. split; [|exact Typed].
 exact (rf_source_node_988 invalid middle middle result value Value Typed Second).
Qed.
Print Assumptions x0_write_data_typed_after_two.
