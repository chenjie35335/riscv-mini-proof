Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_142_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 142)))).
Definition joint_register_142_decl := match straight_drop 120 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_142_tail := match straight_drop 767 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_142_mid := take_statements 646 joint_register_142_decl.
Lemma joint_register_142_position : straight_drop 119 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 142 joint_register_142_reg) joint_register_142_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_142_split : joint_register_142_decl = statement_append joint_register_142_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 142) joint_register_update_142) joint_register_142_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_142_straight : straight_statements joint_register_142_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_142_mid_safe : formal_typed_suffix_safe flat_memories 142 joint_register_142_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_142_tail_safe : formal_typed_suffix_safe flat_memories 142 joint_register_142_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_142_identity : register_identity_b 142 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_142_commit inputs path old current result old_value :
 VM.find 142 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 761 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 142 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H761 Step.
 eapply (concrete_register_mux_commit 119 flat_statements joint_register_142_decl joint_register_142_mid joint_register_142_tail 142 joint_register_142_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 761)) inputs path flat_memories old current result old_value 32
 joint_register_142_position joint_register_142_split joint_register_142_straight joint_register_142_mid_safe joint_register_142_tail_safe Old Typed joint_register_142_identity).
 - apply joint_register_ready_142; assumption.
 - exact Step.
Qed.
Definition joint_register_143_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 143)))).
Definition joint_register_143_decl := match straight_drop 121 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_143_tail := match straight_drop 768 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_143_mid := take_statements 646 joint_register_143_decl.
Lemma joint_register_143_position : straight_drop 120 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 143 joint_register_143_reg) joint_register_143_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_143_split : joint_register_143_decl = statement_append joint_register_143_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 143) joint_register_update_143) joint_register_143_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_143_straight : straight_statements joint_register_143_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_143_mid_safe : formal_typed_suffix_safe flat_memories 143 joint_register_143_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_143_tail_safe : formal_typed_suffix_safe flat_memories 143 joint_register_143_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_143_identity : register_identity_b 143 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_143_commit inputs path old current result old_value :
 VM.find 143 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 762 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 143 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H762 Step.
 eapply (concrete_register_mux_commit 120 flat_statements joint_register_143_decl joint_register_143_mid joint_register_143_tail 143 joint_register_143_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 762)) inputs path flat_memories old current result old_value 32
 joint_register_143_position joint_register_143_split joint_register_143_straight joint_register_143_mid_safe joint_register_143_tail_safe Old Typed joint_register_143_identity).
 - apply joint_register_ready_143; assumption.
 - exact Step.
Qed.
Definition joint_register_144_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 144)))).
Definition joint_register_144_decl := match straight_drop 122 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_144_tail := match straight_drop 769 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_144_mid := take_statements 646 joint_register_144_decl.
Lemma joint_register_144_position : straight_drop 121 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 144 joint_register_144_reg) joint_register_144_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_144_split : joint_register_144_decl = statement_append joint_register_144_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 144) joint_register_update_144) joint_register_144_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_144_straight : straight_statements joint_register_144_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_144_mid_safe : formal_typed_suffix_safe flat_memories 144 joint_register_144_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_144_tail_safe : formal_typed_suffix_safe flat_memories 144 joint_register_144_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_144_identity : register_identity_b 144 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_144_commit inputs path old current result old_value :
 VM.find 144 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 767 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 144 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H767 Step.
 eapply (concrete_register_mux_commit 121 flat_statements joint_register_144_decl joint_register_144_mid joint_register_144_tail 144 joint_register_144_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 767)) inputs path flat_memories old current result old_value 32
 joint_register_144_position joint_register_144_split joint_register_144_straight joint_register_144_mid_safe joint_register_144_tail_safe Old Typed joint_register_144_identity).
 - apply joint_register_ready_144; assumption.
 - exact Step.
Qed.
Definition joint_register_145_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 145)))).
Definition joint_register_145_decl := match straight_drop 123 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_145_tail := match straight_drop 770 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_145_mid := take_statements 646 joint_register_145_decl.
Lemma joint_register_145_position : straight_drop 122 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 145 joint_register_145_reg) joint_register_145_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_145_split : joint_register_145_decl = statement_append joint_register_145_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 145) joint_register_update_145) joint_register_145_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_145_straight : straight_statements joint_register_145_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_145_mid_safe : formal_typed_suffix_safe flat_memories 145 joint_register_145_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_145_tail_safe : formal_typed_suffix_safe flat_memories 145 joint_register_145_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_145_identity : register_identity_b 145 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_145_commit inputs path old current result old_value :
 VM.find 145 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 769 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 145 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H769 Step.
 eapply (concrete_register_mux_commit 122 flat_statements joint_register_145_decl joint_register_145_mid joint_register_145_tail 145 joint_register_145_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 769)) inputs path flat_memories old current result old_value 32
 joint_register_145_position joint_register_145_split joint_register_145_straight joint_register_145_mid_safe joint_register_145_tail_safe Old Typed joint_register_145_identity).
 - apply joint_register_ready_145; assumption.
 - exact Step.
Qed.
Definition joint_register_146_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 146)))).
Definition joint_register_146_decl := match straight_drop 124 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_146_tail := match straight_drop 771 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_146_mid := take_statements 646 joint_register_146_decl.
Lemma joint_register_146_position : straight_drop 123 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 146 joint_register_146_reg) joint_register_146_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_146_split : joint_register_146_decl = statement_append joint_register_146_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 146) joint_register_update_146) joint_register_146_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_146_straight : straight_statements joint_register_146_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_146_mid_safe : formal_typed_suffix_safe flat_memories 146 joint_register_146_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_146_tail_safe : formal_typed_suffix_safe flat_memories 146 joint_register_146_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_146_identity : register_identity_b 146 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_146_commit inputs path old current result old_value :
 VM.find 146 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 768 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 146 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H768 Step.
 eapply (concrete_register_mux_commit 123 flat_statements joint_register_146_decl joint_register_146_mid joint_register_146_tail 146 joint_register_146_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 768)) inputs path flat_memories old current result old_value 32
 joint_register_146_position joint_register_146_split joint_register_146_straight joint_register_146_mid_safe joint_register_146_tail_safe Old Typed joint_register_146_identity).
 - apply joint_register_ready_146; assumption.
 - exact Step.
Qed.
Definition joint_register_147_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 147)))).
Definition joint_register_147_decl := match straight_drop 125 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_147_tail := match straight_drop 772 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_147_mid := take_statements 646 joint_register_147_decl.
Lemma joint_register_147_position : straight_drop 124 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 147 joint_register_147_reg) joint_register_147_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_147_split : joint_register_147_decl = statement_append joint_register_147_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 147) joint_register_update_147) joint_register_147_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_147_straight : straight_statements joint_register_147_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_147_mid_safe : formal_typed_suffix_safe flat_memories 147 joint_register_147_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_147_tail_safe : formal_typed_suffix_safe flat_memories 147 joint_register_147_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_147_identity : register_identity_b 147 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_147_commit inputs path old current result old_value :
 VM.find 147 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 770 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 147 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H770 Step.
 eapply (concrete_register_mux_commit 124 flat_statements joint_register_147_decl joint_register_147_mid joint_register_147_tail 147 joint_register_147_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 770)) inputs path flat_memories old current result old_value 32
 joint_register_147_position joint_register_147_split joint_register_147_straight joint_register_147_mid_safe joint_register_147_tail_safe Old Typed joint_register_147_identity).
 - apply joint_register_ready_147; assumption.
 - exact Step.
Qed.
Definition joint_register_150_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 2)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 150)))).
Definition joint_register_150_decl := match straight_drop 128 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_150_tail := match straight_drop 773 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_150_mid := take_statements 644 joint_register_150_decl.
Lemma joint_register_150_position : straight_drop 127 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 150 joint_register_150_reg) joint_register_150_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_150_split : joint_register_150_decl = statement_append joint_register_150_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 150) joint_register_update_150) joint_register_150_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_150_straight : straight_statements joint_register_150_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_150_mid_safe : formal_typed_suffix_safe flat_memories 150 joint_register_150_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_150_tail_safe : formal_typed_suffix_safe flat_memories 150 joint_register_150_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_150_identity : register_identity_b 150 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_150_commit inputs path old current result old_value :
 VM.find 150 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 2) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 752 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 2%nat /\ VM.find 150 result = Some (Gval (Fuint 2) word).
Proof.
 intros Old Typed H116 H752 Step.
 eapply (concrete_register_mux_commit 127 flat_statements joint_register_150_decl joint_register_150_mid joint_register_150_tail 150 joint_register_150_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 752)) inputs path flat_memories old current result old_value 2
 joint_register_150_position joint_register_150_split joint_register_150_straight joint_register_150_mid_safe joint_register_150_tail_safe Old Typed joint_register_150_identity).
 - apply joint_register_ready_150; assumption.
 - exact Step.
Qed.
Definition joint_register_151_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 2)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 151)))).
Definition joint_register_151_decl := match straight_drop 129 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_151_tail := match straight_drop 774 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_151_mid := take_statements 644 joint_register_151_decl.
Lemma joint_register_151_position : straight_drop 128 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 151 joint_register_151_reg) joint_register_151_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_151_split : joint_register_151_decl = statement_append joint_register_151_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 151) joint_register_update_151) joint_register_151_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_151_straight : straight_statements joint_register_151_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_151_mid_safe : formal_typed_suffix_safe flat_memories 151 joint_register_151_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_151_tail_safe : formal_typed_suffix_safe flat_memories 151 joint_register_151_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_151_identity : register_identity_b 151 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_151_commit inputs path old current result old_value :
 VM.find 151 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 2) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 754 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 2%nat /\ VM.find 151 result = Some (Gval (Fuint 2) word).
Proof.
 intros Old Typed H116 H754 Step.
 eapply (concrete_register_mux_commit 128 flat_statements joint_register_151_decl joint_register_151_mid joint_register_151_tail 151 joint_register_151_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 754)) inputs path flat_memories old current result old_value 2
 joint_register_151_position joint_register_151_split joint_register_151_straight joint_register_151_mid_safe joint_register_151_tail_safe Old Typed joint_register_151_identity).
 - apply joint_register_ready_151; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_151_commit.
