Require Import FormalDeclaredConnection FormalDeclaredInvalidWire ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition invalid_wire_decl_26 := match straight_drop 4 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition invalid_wire_tail_26 := match straight_drop 10096 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition invalid_wire_mid_26 := take_statements 10091 invalid_wire_decl_26.
Lemma invalid_wire_position_26 : straight_drop 3 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 26 (Gtyp (Fuint 32))) invalid_wire_decl_26).
Proof. vm_compute. reflexivity. Qed.
Lemma invalid_wire_split_26 : invalid_wire_decl_26 = statement_append invalid_wire_mid_26 (@Qcons VarOrder.T (@Sinvalid VarOrder.T (@Eid VarOrder.T 26)) invalid_wire_tail_26).
Proof. vm_compute. reflexivity. Qed.
Lemma invalid_wire_straight_26 : straight_statements invalid_wire_mid_26.
Proof. vm_compute. exact I. Qed.
Lemma invalid_wire_mid_safe_26 : formal_typed_suffix_safe flat_memories 26 invalid_wire_mid_26.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma invalid_wire_tail_safe_26 : formal_typed_suffix_safe flat_memories 26 invalid_wire_tail_26.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma invalid_wire_nonregister_26 : has_register 26 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem flat_invalid_wire_26_concrete inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 26 result = Some (Gval (Fuint 32) bits) /\ size bits = 32%nat.
Proof.
 intro Step.
 exact (declared_invalid_wire_value 3 flat_statements invalid_wire_decl_26 invalid_wire_mid_26 invalid_wire_tail_26
 26 32 inputs path flat_memories old current result
 invalid_wire_position_26 invalid_wire_split_26 invalid_wire_straight_26 invalid_wire_mid_safe_26 invalid_wire_tail_safe_26
 invalid_wire_nonregister_26 Step).
Qed.
Print Assumptions flat_invalid_wire_26_concrete.
