Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_189_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 189)))).
Definition joint_register_189_decl := match straight_drop 167 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_189_tail := match straight_drop 783 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_189_mid := take_statements 615 joint_register_189_decl.
Lemma joint_register_189_position : straight_drop 166 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 189 joint_register_189_reg) joint_register_189_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_189_split : joint_register_189_decl = statement_append joint_register_189_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 189) joint_register_update_189) joint_register_189_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_189_straight : straight_statements joint_register_189_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_189_mid_safe : formal_typed_suffix_safe flat_memories 189 joint_register_189_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_189_tail_safe : formal_typed_suffix_safe flat_memories 189 joint_register_189_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_189_identity : register_identity_b 189 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_189_commit inputs path old current result old_value :
 VM.find 189 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 750 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 189 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H750 Step.
 eapply (concrete_register_unary_commit 166 flat_statements joint_register_189_decl joint_register_189_mid joint_register_189_tail 189 joint_register_189_reg (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 750)) inputs path flat_memories old current result old_value 32
 joint_register_189_position joint_register_189_split joint_register_189_straight joint_register_189_mid_safe joint_register_189_tail_safe Old Typed joint_register_189_identity).
 - apply joint_register_ready_189; assumption.
 - exact Step.
Qed.
Definition joint_register_190_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 190)))).
Definition joint_register_190_decl := match straight_drop 168 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_190_tail := match straight_drop 784 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_190_mid := take_statements 615 joint_register_190_decl.
Lemma joint_register_190_position : straight_drop 167 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 190 joint_register_190_reg) joint_register_190_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_190_split : joint_register_190_decl = statement_append joint_register_190_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 190) joint_register_update_190) joint_register_190_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_190_straight : straight_statements joint_register_190_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_190_mid_safe : formal_typed_suffix_safe flat_memories 190 joint_register_190_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_190_tail_safe : formal_typed_suffix_safe flat_memories 190 joint_register_190_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_190_identity : register_identity_b 190 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_190_commit inputs path old current result old_value :
 VM.find 190 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 751 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 190 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H751 Step.
 destruct H751 as [ground [bits Source]].
 exact (concrete_register_direct_commit 167 flat_statements joint_register_190_decl joint_register_190_mid joint_register_190_tail 190 751 joint_register_190_reg 32 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_190_position joint_register_190_split joint_register_190_straight joint_register_190_mid_safe joint_register_190_tail_safe joint_register_190_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_191_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 191)))).
Definition joint_register_191_decl := match straight_drop 169 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_191_tail := match straight_drop 785 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_191_mid := take_statements 615 joint_register_191_decl.
Lemma joint_register_191_position : straight_drop 168 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 191 joint_register_191_reg) joint_register_191_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_191_split : joint_register_191_decl = statement_append joint_register_191_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 191) joint_register_update_191) joint_register_191_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_191_straight : straight_statements joint_register_191_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_191_mid_safe : formal_typed_suffix_safe flat_memories 191 joint_register_191_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_191_tail_safe : formal_typed_suffix_safe flat_memories 191 joint_register_191_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_191_identity : register_identity_b 191 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_191_commit inputs path old current result old_value :
 VM.find 191 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 756 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 191 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H756 Step.
 destruct H756 as [ground [bits Source]].
 exact (concrete_register_direct_commit 168 flat_statements joint_register_191_decl joint_register_191_mid joint_register_191_tail 191 756 joint_register_191_reg 32 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_191_position joint_register_191_split joint_register_191_straight joint_register_191_mid_safe joint_register_191_tail_safe joint_register_191_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_192_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 192)))).
Definition joint_register_192_decl := match straight_drop 170 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_192_tail := match straight_drop 786 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_192_mid := take_statements 615 joint_register_192_decl.
Lemma joint_register_192_position : straight_drop 169 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 192 joint_register_192_reg) joint_register_192_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_192_split : joint_register_192_decl = statement_append joint_register_192_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 192) joint_register_update_192) joint_register_192_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_192_straight : straight_statements joint_register_192_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_192_mid_safe : formal_typed_suffix_safe flat_memories 192 joint_register_192_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_192_tail_safe : formal_typed_suffix_safe flat_memories 192 joint_register_192_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_192_identity : register_identity_b 192 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_192_commit inputs path old current result old_value :
 VM.find 192 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 116 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 765 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 192 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H116 H765 Step.
 eapply (concrete_register_mux_commit 169 flat_statements joint_register_192_decl joint_register_192_mid joint_register_192_tail 192 joint_register_192_reg (@Eref VarOrder.T (@Eid VarOrder.T 116)) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 765)) inputs path flat_memories old current result old_value 32
 joint_register_192_position joint_register_192_split joint_register_192_straight joint_register_192_mid_safe joint_register_192_tail_safe Old Typed joint_register_192_identity).
 - apply joint_register_ready_192; assumption.
 - exact Step.
Qed.
Definition joint_register_193_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 115)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 193)))).
Definition joint_register_193_decl := match straight_drop 171 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_193_tail := match straight_drop 787 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_193_mid := take_statements 615 joint_register_193_decl.
Lemma joint_register_193_position : straight_drop 170 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 193 joint_register_193_reg) joint_register_193_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_193_split : joint_register_193_decl = statement_append joint_register_193_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 193) joint_register_update_193) joint_register_193_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_193_straight : straight_statements joint_register_193_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_193_mid_safe : formal_typed_suffix_safe flat_memories 193 joint_register_193_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_193_tail_safe : formal_typed_suffix_safe flat_memories 193 joint_register_193_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_193_identity : register_identity_b 193 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_193_commit inputs path old current result old_value :
 VM.find 193 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 766 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 193 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H766 Step.
 destruct H766 as [ground [bits Source]].
 exact (concrete_register_direct_commit 170 flat_statements joint_register_193_decl joint_register_193_mid joint_register_193_tail 193 766 joint_register_193_reg 32 ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 joint_register_193_position joint_register_193_split joint_register_193_straight joint_register_193_mid_safe joint_register_193_tail_safe joint_register_193_identity Old Typed (Logic.eq_refl _) Source Step).
Qed.
Definition joint_register_851_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 851)))).
Definition joint_register_851_decl := match straight_drop 861 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_851_tail := match straight_drop 1193 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_851_mid := take_statements 331 joint_register_851_decl.
Lemma joint_register_851_position : straight_drop 860 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 851 joint_register_851_reg) joint_register_851_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_851_split : joint_register_851_decl = statement_append joint_register_851_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 851) joint_register_update_851) joint_register_851_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_851_straight : straight_statements joint_register_851_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_851_mid_safe : formal_typed_suffix_safe flat_memories 851 joint_register_851_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_851_tail_safe : formal_typed_suffix_safe flat_memories 851 joint_register_851_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_851_identity : register_identity_b 851 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_851_commit inputs path old current result old_value :
 VM.find 851 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1021 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1085 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 851 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1021 H1085 Step.
 eapply (concrete_register_mux_commit 860 flat_statements joint_register_851_decl joint_register_851_mid joint_register_851_tail 851 joint_register_851_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021)) inputs path flat_memories old current result old_value 32
 joint_register_851_position joint_register_851_split joint_register_851_straight joint_register_851_mid_safe joint_register_851_tail_safe Old Typed joint_register_851_identity).
 - apply joint_register_ready_851; assumption.
 - exact Step.
Qed.
Definition joint_register_852_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 852)))).
Definition joint_register_852_decl := match straight_drop 862 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_852_tail := match straight_drop 1194 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_852_mid := take_statements 331 joint_register_852_decl.
Lemma joint_register_852_position : straight_drop 861 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 852 joint_register_852_reg) joint_register_852_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_852_split : joint_register_852_decl = statement_append joint_register_852_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 852) joint_register_update_852) joint_register_852_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_852_straight : straight_statements joint_register_852_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_852_mid_safe : formal_typed_suffix_safe flat_memories 852 joint_register_852_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_852_tail_safe : formal_typed_suffix_safe flat_memories 852 joint_register_852_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_852_identity : register_identity_b 852 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_852_commit inputs path old current result old_value :
 VM.find 852 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1022 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1086 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 852 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1022 H1086 Step.
 eapply (concrete_register_mux_commit 861 flat_statements joint_register_852_decl joint_register_852_mid joint_register_852_tail 852 joint_register_852_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1086)) (@Eref VarOrder.T (@Eid VarOrder.T 1022)) inputs path flat_memories old current result old_value 32
 joint_register_852_position joint_register_852_split joint_register_852_straight joint_register_852_mid_safe joint_register_852_tail_safe Old Typed joint_register_852_identity).
 - apply joint_register_ready_852; assumption.
 - exact Step.
Qed.
Definition joint_register_853_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 853)))).
Definition joint_register_853_decl := match straight_drop 863 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_853_tail := match straight_drop 1195 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_853_mid := take_statements 331 joint_register_853_decl.
Lemma joint_register_853_position : straight_drop 862 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 853 joint_register_853_reg) joint_register_853_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_853_split : joint_register_853_decl = statement_append joint_register_853_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 853) joint_register_update_853) joint_register_853_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_853_straight : straight_statements joint_register_853_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_853_mid_safe : formal_typed_suffix_safe flat_memories 853 joint_register_853_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_853_tail_safe : formal_typed_suffix_safe flat_memories 853 joint_register_853_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_853_identity : register_identity_b 853 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_853_commit inputs path old current result old_value :
 VM.find 853 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1023 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1087 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 853 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1023 H1087 Step.
 eapply (concrete_register_mux_commit 862 flat_statements joint_register_853_decl joint_register_853_mid joint_register_853_tail 853 joint_register_853_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1087)) (@Eref VarOrder.T (@Eid VarOrder.T 1023)) inputs path flat_memories old current result old_value 32
 joint_register_853_position joint_register_853_split joint_register_853_straight joint_register_853_mid_safe joint_register_853_tail_safe Old Typed joint_register_853_identity).
 - apply joint_register_ready_853; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_853_commit.
