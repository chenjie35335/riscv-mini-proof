Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_7751_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7751)))).
Definition joint_register_7751_decl := match straight_drop 8258 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7751_tail := match straight_drop 8854 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7751_mid := take_statements 595 joint_register_7751_decl.
Lemma joint_register_7751_position : straight_drop 8257 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7751 joint_register_7751_reg) joint_register_7751_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7751_split : joint_register_7751_decl = statement_append joint_register_7751_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7751) joint_register_update_7751) joint_register_7751_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7751_straight : straight_statements joint_register_7751_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7751_mid_safe : formal_typed_suffix_safe flat_memories 7751 joint_register_7751_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7751_tail_safe : formal_typed_suffix_safe flat_memories 7751 joint_register_7751_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7751_identity : register_identity_b 7751 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7751_commit inputs path old current result old_value :
 VM.find 7751 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7877 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8161 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7751 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7877 H8161 Step.
 eapply (concrete_register_mux_commit 8257 flat_statements joint_register_7751_decl joint_register_7751_mid joint_register_7751_tail 7751 joint_register_7751_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8161)) (@Eref VarOrder.T (@Eid VarOrder.T 7877)) inputs path flat_memories old current result old_value 32
 joint_register_7751_position joint_register_7751_split joint_register_7751_straight joint_register_7751_mid_safe joint_register_7751_tail_safe Old Typed joint_register_7751_identity).
 - apply joint_register_ready_7751; assumption.
 - exact Step.
Qed.
Definition joint_register_7752_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7752)))).
Definition joint_register_7752_decl := match straight_drop 8259 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7752_tail := match straight_drop 8855 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7752_mid := take_statements 595 joint_register_7752_decl.
Lemma joint_register_7752_position : straight_drop 8258 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7752 joint_register_7752_reg) joint_register_7752_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7752_split : joint_register_7752_decl = statement_append joint_register_7752_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7752) joint_register_update_7752) joint_register_7752_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7752_straight : straight_statements joint_register_7752_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7752_mid_safe : formal_typed_suffix_safe flat_memories 7752 joint_register_7752_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7752_tail_safe : formal_typed_suffix_safe flat_memories 7752 joint_register_7752_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7752_identity : register_identity_b 7752 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7752_commit inputs path old current result old_value :
 VM.find 7752 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7879 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8162 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7752 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7879 H8162 Step.
 eapply (concrete_register_mux_commit 8258 flat_statements joint_register_7752_decl joint_register_7752_mid joint_register_7752_tail 7752 joint_register_7752_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8162)) (@Eref VarOrder.T (@Eid VarOrder.T 7879)) inputs path flat_memories old current result old_value 32
 joint_register_7752_position joint_register_7752_split joint_register_7752_straight joint_register_7752_mid_safe joint_register_7752_tail_safe Old Typed joint_register_7752_identity).
 - apply joint_register_ready_7752; assumption.
 - exact Step.
Qed.
Definition joint_register_7753_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7753)))).
Definition joint_register_7753_decl := match straight_drop 8260 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7753_tail := match straight_drop 8856 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7753_mid := take_statements 595 joint_register_7753_decl.
Lemma joint_register_7753_position : straight_drop 8259 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7753 joint_register_7753_reg) joint_register_7753_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7753_split : joint_register_7753_decl = statement_append joint_register_7753_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7753) joint_register_update_7753) joint_register_7753_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7753_straight : straight_statements joint_register_7753_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7753_mid_safe : formal_typed_suffix_safe flat_memories 7753 joint_register_7753_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7753_tail_safe : formal_typed_suffix_safe flat_memories 7753 joint_register_7753_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7753_identity : register_identity_b 7753 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7753_commit inputs path old current result old_value :
 VM.find 7753 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7880 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8163 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7753 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7880 H8163 Step.
 eapply (concrete_register_mux_commit 8259 flat_statements joint_register_7753_decl joint_register_7753_mid joint_register_7753_tail 7753 joint_register_7753_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8163)) (@Eref VarOrder.T (@Eid VarOrder.T 7880)) inputs path flat_memories old current result old_value 32
 joint_register_7753_position joint_register_7753_split joint_register_7753_straight joint_register_7753_mid_safe joint_register_7753_tail_safe Old Typed joint_register_7753_identity).
 - apply joint_register_ready_7753; assumption.
 - exact Step.
Qed.
Definition joint_register_7754_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 2)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7754)))).
Definition joint_register_7754_decl := match straight_drop 8261 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7754_tail := match straight_drop 8857 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7754_mid := take_statements 595 joint_register_7754_decl.
Lemma joint_register_7754_position : straight_drop 8260 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7754 joint_register_7754_reg) joint_register_7754_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7754_split : joint_register_7754_decl = statement_append joint_register_7754_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7754) joint_register_update_7754) joint_register_7754_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7754_straight : straight_statements joint_register_7754_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7754_mid_safe : formal_typed_suffix_safe flat_memories 7754 joint_register_7754_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7754_tail_safe : formal_typed_suffix_safe flat_memories 7754 joint_register_7754_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7754_identity : register_identity_b 7754 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7754_commit inputs path old current result old_value :
 VM.find 7754 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 2) ->
 (exists ground bits, VM.find 7871 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 2%nat /\ VM.find 7754 result = Some (Gval (Fuint 2) word).
Proof.
 intros Old Typed H7871 Step.
 destruct H7871 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8260 flat_statements joint_register_7754_decl joint_register_7754_mid joint_register_7754_tail 7754 7871 joint_register_7754_reg 2 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7754_position joint_register_7754_split joint_register_7754_straight joint_register_7754_mid_safe joint_register_7754_tail_safe joint_register_7754_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7755_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 3)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7755)))).
Definition joint_register_7755_decl := match straight_drop 8262 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7755_tail := match straight_drop 8858 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7755_mid := take_statements 595 joint_register_7755_decl.
Lemma joint_register_7755_position : straight_drop 8261 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7755 joint_register_7755_reg) joint_register_7755_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7755_split : joint_register_7755_decl = statement_append joint_register_7755_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7755) joint_register_update_7755) joint_register_7755_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7755_straight : straight_statements joint_register_7755_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7755_mid_safe : formal_typed_suffix_safe flat_memories 7755 joint_register_7755_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7755_tail_safe : formal_typed_suffix_safe flat_memories 7755 joint_register_7755_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7755_identity : register_identity_b 7755 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7755_commit inputs path old current result old_value :
 VM.find 7755 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 (exists ground bits, VM.find 7872 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 3%nat /\ VM.find 7755 result = Some (Gval (Fuint 3) word).
Proof.
 intros Old Typed H7872 Step.
 destruct H7872 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8261 flat_statements joint_register_7755_decl joint_register_7755_mid joint_register_7755_tail 7755 7872 joint_register_7755_reg 3 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7755_position joint_register_7755_split joint_register_7755_straight joint_register_7755_mid_safe joint_register_7755_tail_safe joint_register_7755_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7756_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 2)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7756)))).
Definition joint_register_7756_decl := match straight_drop 8263 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7756_tail := match straight_drop 8859 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7756_mid := take_statements 595 joint_register_7756_decl.
Lemma joint_register_7756_position : straight_drop 8262 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7756 joint_register_7756_reg) joint_register_7756_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7756_split : joint_register_7756_decl = statement_append joint_register_7756_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7756) joint_register_update_7756) joint_register_7756_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7756_straight : straight_statements joint_register_7756_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7756_mid_safe : formal_typed_suffix_safe flat_memories 7756 joint_register_7756_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7756_tail_safe : formal_typed_suffix_safe flat_memories 7756 joint_register_7756_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7756_identity : register_identity_b 7756 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7756_commit inputs path old current result old_value :
 VM.find 7756 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 2) ->
 (exists ground bits, VM.find 7881 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 2%nat /\ VM.find 7756 result = Some (Gval (Fuint 2) word).
Proof.
 intros Old Typed H7881 Step.
 destruct H7881 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8262 flat_statements joint_register_7756_decl joint_register_7756_mid joint_register_7756_tail 7756 7881 joint_register_7756_reg 2 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7756_position joint_register_7756_split joint_register_7756_straight joint_register_7756_mid_safe joint_register_7756_tail_safe joint_register_7756_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7757_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7757)))).
Definition joint_register_7757_decl := match straight_drop 8264 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7757_tail := match straight_drop 8860 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7757_mid := take_statements 595 joint_register_7757_decl.
Lemma joint_register_7757_position : straight_drop 8263 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7757 joint_register_7757_reg) joint_register_7757_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7757_split : joint_register_7757_decl = statement_append joint_register_7757_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7757) joint_register_update_7757) joint_register_7757_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7757_straight : straight_statements joint_register_7757_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7757_mid_safe : formal_typed_suffix_safe flat_memories 7757 joint_register_7757_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7757_tail_safe : formal_typed_suffix_safe flat_memories 7757 joint_register_7757_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7757_identity : register_identity_b 7757 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7757_commit inputs path old current result old_value :
 VM.find 7757 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 7873 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 7757 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H7873 Step.
 destruct H7873 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8263 flat_statements joint_register_7757_decl joint_register_7757_mid joint_register_7757_tail 7757 7873 joint_register_7757_reg 1 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7757_position joint_register_7757_split joint_register_7757_straight joint_register_7757_mid_safe joint_register_7757_tail_safe joint_register_7757_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_7758_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 3)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7758)))).
Definition joint_register_7758_decl := match straight_drop 8265 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7758_tail := match straight_drop 8861 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7758_mid := take_statements 595 joint_register_7758_decl.
Lemma joint_register_7758_position : straight_drop 8264 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7758 joint_register_7758_reg) joint_register_7758_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7758_split : joint_register_7758_decl = statement_append joint_register_7758_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7758) joint_register_update_7758) joint_register_7758_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7758_straight : straight_statements joint_register_7758_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7758_mid_safe : formal_typed_suffix_safe flat_memories 7758 joint_register_7758_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7758_tail_safe : formal_typed_suffix_safe flat_memories 7758 joint_register_7758_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7758_identity : register_identity_b 7758 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7758_commit inputs path old current result old_value :
 VM.find 7758 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 3) ->
 (exists ground bits, VM.find 7874 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 3%nat /\ VM.find 7758 result = Some (Gval (Fuint 3) word).
Proof.
 intros Old Typed H7874 Step.
 destruct H7874 as [ground [bits Source]].
 exact (concrete_register_direct_commit 8264 flat_statements joint_register_7758_decl joint_register_7758_mid joint_register_7758_tail 7758 7874 joint_register_7758_reg 3 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_7758_position joint_register_7758_split joint_register_7758_straight joint_register_7758_mid_safe joint_register_7758_tail_safe joint_register_7758_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions joint_register_7758_commit.
