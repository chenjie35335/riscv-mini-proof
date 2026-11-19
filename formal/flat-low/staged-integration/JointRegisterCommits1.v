Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_152_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 152)))).
Definition joint_register_152_decl := match straight_drop 130 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_152_tail := match straight_drop 775 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_152_mid := take_statements 644 joint_register_152_decl.
Lemma joint_register_152_position : straight_drop 129 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 152 joint_register_152_reg) joint_register_152_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_152_split : joint_register_152_decl = statement_append joint_register_152_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 152) joint_register_update_152) joint_register_152_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_152_straight : straight_statements joint_register_152_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_152_mid_safe : formal_typed_suffix_safe flat_memories 152 joint_register_152_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_152_tail_safe : formal_typed_suffix_safe flat_memories 152 joint_register_152_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_152_identity : register_identity_b 152 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_152_commit inputs path old current result old_value :
 VM.find 152 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 753 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 152 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H753 Step.
 eapply (concrete_register_mux_commit 129 flat_statements joint_register_152_decl joint_register_152_mid joint_register_152_tail 152 joint_register_152_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 753)) inputs path flat_memories old current result old_value 1
 joint_register_152_position joint_register_152_split joint_register_152_straight joint_register_152_mid_safe joint_register_152_tail_safe Old Typed joint_register_152_identity).
 - apply joint_register_ready_152; assumption.
 - exact Step.
Qed.
Definition joint_register_153_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 153)))).
Definition joint_register_153_decl := match straight_drop 131 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_153_tail := match straight_drop 776 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_153_mid := take_statements 644 joint_register_153_decl.
Lemma joint_register_153_position : straight_drop 130 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 153 joint_register_153_reg) joint_register_153_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_153_split : joint_register_153_decl = statement_append joint_register_153_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 153) joint_register_update_153) joint_register_153_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_153_straight : straight_statements joint_register_153_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_153_mid_safe : formal_typed_suffix_safe flat_memories 153 joint_register_153_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_153_tail_safe : formal_typed_suffix_safe flat_memories 153 joint_register_153_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_153_identity : register_identity_b 153 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_153_commit inputs path old current result old_value :
 VM.find 153 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 755 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 153 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H755 Step.
 eapply (concrete_register_mux_commit 130 flat_statements joint_register_153_decl joint_register_153_mid joint_register_153_tail 153 joint_register_153_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 755)) inputs path flat_memories old current result old_value 1
 joint_register_153_position joint_register_153_split joint_register_153_straight joint_register_153_mid_safe joint_register_153_tail_safe Old Typed joint_register_153_identity).
 - apply joint_register_ready_153; assumption.
 - exact Step.
Qed.
Definition joint_register_167_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 167)))).
Definition joint_register_167_decl := match straight_drop 145 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_167_tail := match straight_drop 777 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_167_mid := take_statements 631 joint_register_167_decl.
Lemma joint_register_167_position : straight_drop 144 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 167 joint_register_167_reg) joint_register_167_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_167_split : joint_register_167_decl = statement_append joint_register_167_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 167) joint_register_update_167) joint_register_167_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_167_straight : straight_statements joint_register_167_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_167_mid_safe : formal_typed_suffix_safe flat_memories 167 joint_register_167_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_167_tail_safe : formal_typed_suffix_safe flat_memories 167 joint_register_167_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_167_identity : register_identity_b 167 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_167_commit inputs path old current result old_value :
 VM.find 167 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 757 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 167 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H757 Step.
 eapply (concrete_register_mux_commit 144 flat_statements joint_register_167_decl joint_register_167_mid joint_register_167_tail 167 joint_register_167_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 757)) inputs path flat_memories old current result old_value 1
 joint_register_167_position joint_register_167_split joint_register_167_straight joint_register_167_mid_safe joint_register_167_tail_safe Old Typed joint_register_167_identity).
 - apply joint_register_ready_167; assumption.
 - exact Step.
Qed.
Definition joint_register_168_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 168)))).
Definition joint_register_168_decl := match straight_drop 146 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_168_tail := match straight_drop 778 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_168_mid := take_statements 631 joint_register_168_decl.
Lemma joint_register_168_position : straight_drop 145 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 168 joint_register_168_reg) joint_register_168_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_168_split : joint_register_168_decl = statement_append joint_register_168_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 168) joint_register_update_168) joint_register_168_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_168_straight : straight_statements joint_register_168_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_168_mid_safe : formal_typed_suffix_safe flat_memories 168 joint_register_168_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_168_tail_safe : formal_typed_suffix_safe flat_memories 168 joint_register_168_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_168_identity : register_identity_b 168 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_168_commit inputs path old current result old_value :
 VM.find 168 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 759 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 168 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H759 Step.
 eapply (concrete_register_mux_commit 145 flat_statements joint_register_168_decl joint_register_168_mid joint_register_168_tail 168 joint_register_168_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 759)) inputs path flat_memories old current result old_value 1
 joint_register_168_position joint_register_168_split joint_register_168_straight joint_register_168_mid_safe joint_register_168_tail_safe Old Typed joint_register_168_identity).
 - apply joint_register_ready_168; assumption.
 - exact Step.
Qed.
Definition joint_register_169_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 169)))).
Definition joint_register_169_decl := match straight_drop 147 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_169_tail := match straight_drop 779 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_169_mid := take_statements 631 joint_register_169_decl.
Lemma joint_register_169_position : straight_drop 146 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 169 joint_register_169_reg) joint_register_169_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_169_split : joint_register_169_decl = statement_append joint_register_169_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 169) joint_register_update_169) joint_register_169_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_169_straight : straight_statements joint_register_169_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_169_mid_safe : formal_typed_suffix_safe flat_memories 169 joint_register_169_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_169_tail_safe : formal_typed_suffix_safe flat_memories 169 joint_register_169_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_169_identity : register_identity_b 169 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_169_commit inputs path old current result old_value :
 VM.find 169 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 758 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 169 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H758 Step.
 eapply (concrete_register_mux_commit 146 flat_statements joint_register_169_decl joint_register_169_mid joint_register_169_tail 169 joint_register_169_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 758)) inputs path flat_memories old current result old_value 1
 joint_register_169_position joint_register_169_split joint_register_169_straight joint_register_169_mid_safe joint_register_169_tail_safe Old Typed joint_register_169_identity).
 - apply joint_register_ready_169; assumption.
 - exact Step.
Qed.
Definition joint_register_170_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 170)))).
Definition joint_register_170_decl := match straight_drop 148 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_170_tail := match straight_drop 780 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_170_mid := take_statements 631 joint_register_170_decl.
Lemma joint_register_170_position : straight_drop 147 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 170 joint_register_170_reg) joint_register_170_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_170_split : joint_register_170_decl = statement_append joint_register_170_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 170) joint_register_update_170) joint_register_170_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_170_straight : straight_statements joint_register_170_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_170_mid_safe : formal_typed_suffix_safe flat_memories 170 joint_register_170_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_170_tail_safe : formal_typed_suffix_safe flat_memories 170 joint_register_170_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_170_identity : register_identity_b 170 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_170_commit inputs path old current result old_value :
 VM.find 170 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 760 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 1%nat /\ VM.find 170 result = Some (Gval (Fuint 1) word).
Proof.
 intros Old Typed H116 H760 Step.
 eapply (concrete_register_mux_commit 147 flat_statements joint_register_170_decl joint_register_170_mid joint_register_170_tail 170 joint_register_170_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 760)) inputs path flat_memories old current result old_value 1
 joint_register_170_position joint_register_170_split joint_register_170_straight joint_register_170_mid_safe joint_register_170_tail_safe Old Typed joint_register_170_identity).
 - apply joint_register_ready_170; assumption.
 - exact Step.
Qed.
Definition joint_register_187_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 187)))).
Definition joint_register_187_decl := match straight_drop 165 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_187_tail := match straight_drop 781 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_187_mid := take_statements 615 joint_register_187_decl.
Lemma joint_register_187_position : straight_drop 164 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 187 joint_register_187_reg) joint_register_187_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_187_split : joint_register_187_decl = statement_append joint_register_187_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 187) joint_register_update_187) joint_register_187_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_187_straight : straight_statements joint_register_187_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_187_mid_safe : formal_typed_suffix_safe flat_memories 187 joint_register_187_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_187_tail_safe : formal_typed_suffix_safe flat_memories 187 joint_register_187_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_187_identity : register_identity_b 187 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_187_commit inputs path old current result old_value :
 VM.find 187 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 763 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 187 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H763 Step.
 destruct H763 as [ground [bits Source]].
 exact (concrete_register_direct_commit 164 flat_statements joint_register_187_decl joint_register_187_mid joint_register_187_tail 187 763 joint_register_187_reg 32 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_187_position joint_register_187_split joint_register_187_straight joint_register_187_mid_safe joint_register_187_tail_safe joint_register_187_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_188_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 188)))).
Definition joint_register_188_decl := match straight_drop 166 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_188_tail := match straight_drop 782 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_188_mid := take_statements 615 joint_register_188_decl.
Lemma joint_register_188_position : straight_drop 165 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 188 joint_register_188_reg) joint_register_188_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_188_split : joint_register_188_decl = statement_append joint_register_188_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 188) joint_register_update_188) joint_register_188_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_188_straight : straight_statements joint_register_188_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_188_mid_safe : formal_typed_suffix_safe flat_memories 188 joint_register_188_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_188_tail_safe : formal_typed_suffix_safe flat_memories 188 joint_register_188_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_188_identity : register_identity_b 188 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_188_commit inputs path old current result old_value :
 VM.find 188 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 764 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 188 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H764 Step.
 destruct H764 as [ground [bits Source]].
 exact (concrete_register_direct_commit 165 flat_statements joint_register_188_decl joint_register_188_mid joint_register_188_tail 188 764 joint_register_188_reg 32 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_188_position joint_register_188_split joint_register_188_straight joint_register_188_mid_safe joint_register_188_tail_safe joint_register_188_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions joint_register_188_commit.
