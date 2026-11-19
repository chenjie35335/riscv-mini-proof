Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition stall_connection_33 := @Sfcnct VarOrder.T (@Eid VarOrder.T 33) (@Eref VarOrder.T (@Eid VarOrder.T 9216)).
Definition stall_after_33 := match straight_drop 10097 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_declared_33 := match straight_drop 11 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_middle_33 := take_statements 10085 stall_declared_33.
Lemma stall_declaration_33 : straight_drop 10 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 33 (Gtyp (Fuint 1))) stall_declared_33).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_split_33 : stall_declared_33 = statement_append stall_middle_33 (@Qcons VarOrder.T stall_connection_33 stall_after_33).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_straight_33 : straight_statements stall_middle_33.
Proof. vm_compute. exact I. Qed.
Lemma stall_middle_safe_33 : formal_typed_suffix_safe flat_memories 33 stall_middle_33.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_after_safe_33 : formal_typed_suffix_safe flat_memories 33 stall_after_33.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_connection_nonregister_33 : has_register 33 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_connection_33_transfer invalid old current result bit :
 VM.find 9216 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 33 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 10 flat_statements stall_declared_33 stall_middle_33 stall_after_33
 33 9216 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact stall_declaration_33|exact stall_split_33|exact stall_straight_33|
 exact stall_middle_safe_33|exact stall_after_safe_33|exact stall_connection_nonregister_33|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Definition stall_connection_40 := @Sfcnct VarOrder.T (@Eid VarOrder.T 40) (@Eref VarOrder.T (@Eid VarOrder.T 9218)).
Definition stall_after_40 := match straight_drop 10099 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_declared_40 := match straight_drop 18 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_middle_40 := take_statements 10080 stall_declared_40.
Lemma stall_declaration_40 : straight_drop 17 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 40 (Gtyp (Fuint 1))) stall_declared_40).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_split_40 : stall_declared_40 = statement_append stall_middle_40 (@Qcons VarOrder.T stall_connection_40 stall_after_40).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_straight_40 : straight_statements stall_middle_40.
Proof. vm_compute. exact I. Qed.
Lemma stall_middle_safe_40 : formal_typed_suffix_safe flat_memories 40 stall_middle_40.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_after_safe_40 : formal_typed_suffix_safe flat_memories 40 stall_after_40.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_connection_nonregister_40 : has_register 40 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_connection_40_transfer invalid old current result bit :
 VM.find 9218 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 40 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 17 flat_statements stall_declared_40 stall_middle_40 stall_after_40
 40 9218 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact stall_declaration_40|exact stall_split_40|exact stall_straight_40|
 exact stall_middle_safe_40|exact stall_after_safe_40|exact stall_connection_nonregister_40|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Definition stall_connection_74 := @Sfcnct VarOrder.T (@Eid VarOrder.T 74) (@Eref VarOrder.T (@Eid VarOrder.T 33)).
Definition stall_after_74 := match straight_drop 9987 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_declared_74 := match straight_drop 52 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_middle_74 := take_statements 9934 stall_declared_74.
Lemma stall_declaration_74 : straight_drop 51 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 74 (Gtyp (Fuint 1))) stall_declared_74).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_split_74 : stall_declared_74 = statement_append stall_middle_74 (@Qcons VarOrder.T stall_connection_74 stall_after_74).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_straight_74 : straight_statements stall_middle_74.
Proof. vm_compute. exact I. Qed.
Lemma stall_middle_safe_74 : formal_typed_suffix_safe flat_memories 74 stall_middle_74.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_after_safe_74 : formal_typed_suffix_safe flat_memories 74 stall_after_74.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_connection_nonregister_74 : has_register 74 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_connection_74_transfer invalid old current result bit :
 VM.find 33 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 74 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 51 flat_statements stall_declared_74 stall_middle_74 stall_after_74
 74 33 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact stall_declaration_74|exact stall_split_74|exact stall_straight_74|
 exact stall_middle_safe_74|exact stall_after_safe_74|exact stall_connection_nonregister_74|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Definition stall_connection_81 := @Sfcnct VarOrder.T (@Eid VarOrder.T 81) (@Eref VarOrder.T (@Eid VarOrder.T 40)).
Definition stall_after_81 := match straight_drop 9989 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_declared_81 := match straight_drop 59 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition stall_middle_81 := take_statements 9929 stall_declared_81.
Lemma stall_declaration_81 : straight_drop 58 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 81 (Gtyp (Fuint 1))) stall_declared_81).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_split_81 : stall_declared_81 = statement_append stall_middle_81 (@Qcons VarOrder.T stall_connection_81 stall_after_81).
Proof. vm_compute. reflexivity. Qed.
Lemma stall_straight_81 : straight_statements stall_middle_81.
Proof. vm_compute. exact I. Qed.
Lemma stall_middle_safe_81 : formal_typed_suffix_safe flat_memories 81 stall_middle_81.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_after_safe_81 : formal_typed_suffix_safe flat_memories 81 stall_after_81.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma stall_connection_nonregister_81 : has_register 81 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem stall_connection_81_transfer invalid old current result bit :
 VM.find 40 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 81 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step.
 eapply (declared_connection_value 58 flat_statements stall_declared_81 stall_middle_81 stall_after_81
 81 40 1 (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]) invalid flat_memories old current result);
 [exact stall_declaration_81|exact stall_split_81|exact stall_straight_81|
 exact stall_middle_safe_81|exact stall_after_safe_81|exact stall_connection_nonregister_81|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Print Assumptions stall_connection_81_transfer.
