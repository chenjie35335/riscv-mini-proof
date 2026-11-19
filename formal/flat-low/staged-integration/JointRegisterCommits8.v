Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_7759_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7759)))).
Definition joint_register_7759_decl := match straight_drop 8266 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7759_tail := match straight_drop 8862 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7759_mid := take_statements 595 joint_register_7759_decl.
Lemma joint_register_7759_position : straight_drop 8265 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7759 joint_register_7759_reg) joint_register_7759_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7759_split : joint_register_7759_decl = statement_append joint_register_7759_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7759) joint_register_update_7759) joint_register_7759_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7759_straight : straight_statements joint_register_7759_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7759_mid_safe : formal_typed_suffix_safe flat_memories 7759 joint_register_7759_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7759_tail_safe : formal_typed_suffix_safe flat_memories 7759 joint_register_7759_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7759_identity : register_identity_b 7759 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7759_commit inputs path old current result old_value :
 VM.find 7759 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 7875 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 7759 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H7875 Step.
 destruct H7875 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8265 flat_statements joint_register_7759_decl joint_register_7759_mid joint_register_7759_tail 7759 7875 joint_register_7759_reg 1 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7759_position joint_register_7759_split joint_register_7759_straight joint_register_7759_mid_safe joint_register_7759_tail_safe joint_register_7759_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7760_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7760)))).
Definition joint_register_7760_decl := match straight_drop 8267 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7760_tail := match straight_drop 8863 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7760_mid := take_statements 595 joint_register_7760_decl.
Lemma joint_register_7760_position : straight_drop 8266 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7760 joint_register_7760_reg) joint_register_7760_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7760_split : joint_register_7760_decl = statement_append joint_register_7760_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7760) joint_register_update_7760) joint_register_7760_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7760_straight : straight_statements joint_register_7760_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7760_mid_safe : formal_typed_suffix_safe flat_memories 7760 joint_register_7760_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7760_tail_safe : formal_typed_suffix_safe flat_memories 7760 joint_register_7760_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7760_identity : register_identity_b 7760 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7760_commit inputs path old current result old_value :
 VM.find 7760 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 7876 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 7760 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H7876 Step.
 destruct H7876 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8266 flat_statements joint_register_7760_decl joint_register_7760_mid joint_register_7760_tail 7760 7876 joint_register_7760_reg 1 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7760_position joint_register_7760_split joint_register_7760_straight joint_register_7760_mid_safe joint_register_7760_tail_safe joint_register_7760_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7762_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7762)))).
Definition joint_register_7762_decl := match straight_drop 8269 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7762_tail := match straight_drop 8864 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7762_mid := take_statements 594 joint_register_7762_decl.
Lemma joint_register_7762_position : straight_drop 8268 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7762 joint_register_7762_reg) joint_register_7762_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7762_split : joint_register_7762_decl = statement_append joint_register_7762_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7762) joint_register_update_7762) joint_register_7762_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7762_straight : straight_statements joint_register_7762_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7762_mid_safe : formal_typed_suffix_safe flat_memories 7762 joint_register_7762_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7762_tail_safe : formal_typed_suffix_safe flat_memories 7762 joint_register_7762_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7762_identity : register_identity_b 7762 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7762_commit inputs path old current result old_value :
 VM.find 7762 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 7761 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 7762 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H7761 Step.
 destruct H7761 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8268 flat_statements joint_register_7762_decl joint_register_7762_mid joint_register_7762_tail 7762 7761 joint_register_7762_reg 1 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7762_position joint_register_7762_split joint_register_7762_straight joint_register_7762_mid_safe joint_register_7762_tail_safe joint_register_7762_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7768_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 33)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7768)))).
Definition joint_register_7768_decl := match straight_drop 8275 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7768_tail := match straight_drop 8865 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7768_mid := take_statements 589 joint_register_7768_decl.
Lemma joint_register_7768_position : straight_drop 8274 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7768 joint_register_7768_reg) joint_register_7768_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7768_split : joint_register_7768_decl = statement_append joint_register_7768_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7768) joint_register_update_7768) joint_register_7768_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7768_straight : straight_statements joint_register_7768_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7768_mid_safe : formal_typed_suffix_safe flat_memories 7768 joint_register_7768_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7768_tail_safe : formal_typed_suffix_safe flat_memories 7768 joint_register_7768_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7768_identity : register_identity_b 7768 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7768_commit inputs path old current result old_value :
 VM.find 7768 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 33) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7767 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7781 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 33%nat /\ VM.find 7768 result = Some (Gval (Fuint 33) word).
Proof.
 intros Old Typed H65 H7767 H7781 Step.
 eapply (concrete_register_mux_commit 8274 flat_statements joint_register_7768_decl joint_register_7768_mid joint_register_7768_tail 7768 joint_register_7768_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 7767)) (@Eref VarOrder.T (@Eid VarOrder.T 7781)) inputs path flat_memories old current result old_value 33
 joint_register_7768_position joint_register_7768_split joint_register_7768_straight joint_register_7768_mid_safe joint_register_7768_tail_safe Old Typed joint_register_7768_identity).
 - apply joint_register_ready_7768; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_7768_commit.
