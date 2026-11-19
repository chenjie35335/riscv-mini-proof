Require Import RegisterInvariants CoreSocModel FormalConnectionTail FormalDeclaredConnection FormalStatementSegments ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reset_connection_24 := @Sfcnct VarOrder.T (@Eid VarOrder.T 24) (@Eref VarOrder.T (@Eid VarOrder.T 1)).
Definition reset_after_24 := match straight_drop 10094 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_declared_24 := match straight_drop 2 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_middle_24 := take_statements 10091 reset_declared_24.
Lemma reset_declaration_24 : straight_drop 1 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 24 (Gtyp (Fuint 1))) reset_declared_24).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_split_24 : reset_declared_24 = statement_append reset_middle_24 (@Qcons VarOrder.T reset_connection_24 reset_after_24).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_straight_24 : straight_statements reset_middle_24.
Proof. vm_compute. exact I. Qed.
Lemma reset_middle_safe_24 : formal_typed_suffix_safe flat_memories 24 reset_middle_24.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_after_safe_24 : formal_typed_suffix_safe flat_memories 24 reset_after_24.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_connection_nonregister_24 : has_register 24 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reset_connection_24_transfer invalid old current result bit :
 VM.find 1 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 24 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 1 flat_statements reset_declared_24 reset_middle_24 reset_after_24
 24 1 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact reset_declaration_24|exact reset_split_24|exact reset_straight_24|
 exact reset_middle_safe_24|exact reset_after_safe_24|exact reset_connection_nonregister_24|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Definition reset_connection_65 := @Sfcnct VarOrder.T (@Eid VarOrder.T 65) (@Eref VarOrder.T (@Eid VarOrder.T 24)).
Definition reset_after_65 := match straight_drop 9984 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_declared_65 := match straight_drop 43 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_middle_65 := take_statements 9940 reset_declared_65.
Lemma reset_declaration_65 : straight_drop 42 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 65 (Gtyp (Fuint 1))) reset_declared_65).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_split_65 : reset_declared_65 = statement_append reset_middle_65 (@Qcons VarOrder.T reset_connection_65 reset_after_65).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_straight_65 : straight_statements reset_middle_65.
Proof. vm_compute. exact I. Qed.
Lemma reset_middle_safe_65 : formal_typed_suffix_safe flat_memories 65 reset_middle_65.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_after_safe_65 : formal_typed_suffix_safe flat_memories 65 reset_after_65.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_connection_nonregister_65 : has_register 65 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reset_connection_65_transfer invalid old current result bit :
 VM.find 24 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 65 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 42 flat_statements reset_declared_65 reset_middle_65 reset_after_65
 65 24 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact reset_declaration_65|exact reset_split_65|exact reset_straight_65|
 exact reset_middle_safe_65|exact reset_after_safe_65|exact reset_connection_nonregister_65|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Definition reset_connection_1394 := @Sfcnct VarOrder.T (@Eid VarOrder.T 1394) (@Eref VarOrder.T (@Eid VarOrder.T 65)).
Definition reset_after_1394 := match straight_drop 8883 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_declared_1394 := match straight_drop 1474 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reset_middle_1394 := take_statements 7408 reset_declared_1394.
Lemma reset_declaration_1394 : straight_drop 1473 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1394 (Gtyp (Fuint 1))) reset_declared_1394).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_split_1394 : reset_declared_1394 = statement_append reset_middle_1394 (@Qcons VarOrder.T reset_connection_1394 reset_after_1394).
Proof. vm_compute. reflexivity. Qed.
Lemma reset_straight_1394 : straight_statements reset_middle_1394.
Proof. vm_compute. exact I. Qed.
Lemma reset_middle_safe_1394 : formal_typed_suffix_safe flat_memories 1394 reset_middle_1394.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_after_safe_1394 : formal_typed_suffix_safe flat_memories 1394 reset_after_1394.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reset_connection_nonregister_1394 : has_register 1394 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reset_connection_1394_transfer invalid old current result bit :
 VM.find 65 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 1394 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 1473 flat_statements reset_declared_1394 reset_middle_1394 reset_after_1394
 1394 65 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact reset_declaration_1394|exact reset_split_1394|exact reset_straight_1394|
 exact reset_middle_safe_1394|exact reset_after_safe_1394|exact reset_connection_nonregister_1394|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Print Assumptions reset_connection_1394_transfer.
