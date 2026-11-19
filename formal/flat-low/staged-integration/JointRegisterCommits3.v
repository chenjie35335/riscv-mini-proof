Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_854_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 854)))).
Definition joint_register_854_decl := match straight_drop 864 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_854_tail := match straight_drop 1196 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_854_mid := take_statements 331 joint_register_854_decl.
Lemma joint_register_854_position : straight_drop 863 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 854 joint_register_854_reg) joint_register_854_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_854_split : joint_register_854_decl = statement_append joint_register_854_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 854) joint_register_update_854) joint_register_854_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_854_straight : straight_statements joint_register_854_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_854_mid_safe : formal_typed_suffix_safe flat_memories 854 joint_register_854_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_854_tail_safe : formal_typed_suffix_safe flat_memories 854 joint_register_854_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_854_identity : register_identity_b 854 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_854_commit inputs path old current result old_value :
 VM.find 854 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1024 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1088 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 854 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1024 H1088 Step.
 eapply (concrete_register_mux_commit 863 flat_statements joint_register_854_decl joint_register_854_mid joint_register_854_tail 854 joint_register_854_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1088)) (@Eref VarOrder.T (@Eid VarOrder.T 1024)) inputs path flat_memories old current result old_value 32
 joint_register_854_position joint_register_854_split joint_register_854_straight joint_register_854_mid_safe joint_register_854_tail_safe Old Typed joint_register_854_identity).
 - apply joint_register_ready_854; assumption.
 - exact Step.
Qed.
Definition joint_register_855_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 855)))).
Definition joint_register_855_decl := match straight_drop 865 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_855_tail := match straight_drop 1197 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_855_mid := take_statements 331 joint_register_855_decl.
Lemma joint_register_855_position : straight_drop 864 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 855 joint_register_855_reg) joint_register_855_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_855_split : joint_register_855_decl = statement_append joint_register_855_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 855) joint_register_update_855) joint_register_855_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_855_straight : straight_statements joint_register_855_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_855_mid_safe : formal_typed_suffix_safe flat_memories 855 joint_register_855_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_855_tail_safe : formal_typed_suffix_safe flat_memories 855 joint_register_855_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_855_identity : register_identity_b 855 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_855_commit inputs path old current result old_value :
 VM.find 855 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1025 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1089 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 855 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1025 H1089 Step.
 eapply (concrete_register_mux_commit 864 flat_statements joint_register_855_decl joint_register_855_mid joint_register_855_tail 855 joint_register_855_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1089)) (@Eref VarOrder.T (@Eid VarOrder.T 1025)) inputs path flat_memories old current result old_value 32
 joint_register_855_position joint_register_855_split joint_register_855_straight joint_register_855_mid_safe joint_register_855_tail_safe Old Typed joint_register_855_identity).
 - apply joint_register_ready_855; assumption.
 - exact Step.
Qed.
Definition joint_register_856_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 856)))).
Definition joint_register_856_decl := match straight_drop 866 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_856_tail := match straight_drop 1198 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_856_mid := take_statements 331 joint_register_856_decl.
Lemma joint_register_856_position : straight_drop 865 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 856 joint_register_856_reg) joint_register_856_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_856_split : joint_register_856_decl = statement_append joint_register_856_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 856) joint_register_update_856) joint_register_856_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_856_straight : straight_statements joint_register_856_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_856_mid_safe : formal_typed_suffix_safe flat_memories 856 joint_register_856_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_856_tail_safe : formal_typed_suffix_safe flat_memories 856 joint_register_856_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_856_identity : register_identity_b 856 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_856_commit inputs path old current result old_value :
 VM.find 856 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1026 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1090 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 856 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1026 H1090 Step.
 eapply (concrete_register_mux_commit 865 flat_statements joint_register_856_decl joint_register_856_mid joint_register_856_tail 856 joint_register_856_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1090)) (@Eref VarOrder.T (@Eid VarOrder.T 1026)) inputs path flat_memories old current result old_value 32
 joint_register_856_position joint_register_856_split joint_register_856_straight joint_register_856_mid_safe joint_register_856_tail_safe Old Typed joint_register_856_identity).
 - apply joint_register_ready_856; assumption.
 - exact Step.
Qed.
Definition joint_register_857_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 857)))).
Definition joint_register_857_decl := match straight_drop 867 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_857_tail := match straight_drop 1199 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_857_mid := take_statements 331 joint_register_857_decl.
Lemma joint_register_857_position : straight_drop 866 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 857 joint_register_857_reg) joint_register_857_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_857_split : joint_register_857_decl = statement_append joint_register_857_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 857) joint_register_update_857) joint_register_857_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_857_straight : straight_statements joint_register_857_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_857_mid_safe : formal_typed_suffix_safe flat_memories 857 joint_register_857_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_857_tail_safe : formal_typed_suffix_safe flat_memories 857 joint_register_857_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_857_identity : register_identity_b 857 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_857_commit inputs path old current result old_value :
 VM.find 857 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1027 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1091 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 857 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1027 H1091 Step.
 eapply (concrete_register_mux_commit 866 flat_statements joint_register_857_decl joint_register_857_mid joint_register_857_tail 857 joint_register_857_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1091)) (@Eref VarOrder.T (@Eid VarOrder.T 1027)) inputs path flat_memories old current result old_value 32
 joint_register_857_position joint_register_857_split joint_register_857_straight joint_register_857_mid_safe joint_register_857_tail_safe Old Typed joint_register_857_identity).
 - apply joint_register_ready_857; assumption.
 - exact Step.
Qed.
Definition joint_register_858_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 858)))).
Definition joint_register_858_decl := match straight_drop 868 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_858_tail := match straight_drop 1200 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_858_mid := take_statements 331 joint_register_858_decl.
Lemma joint_register_858_position : straight_drop 867 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 858 joint_register_858_reg) joint_register_858_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_858_split : joint_register_858_decl = statement_append joint_register_858_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 858) joint_register_update_858) joint_register_858_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_858_straight : straight_statements joint_register_858_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_858_mid_safe : formal_typed_suffix_safe flat_memories 858 joint_register_858_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_858_tail_safe : formal_typed_suffix_safe flat_memories 858 joint_register_858_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_858_identity : register_identity_b 858 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_858_commit inputs path old current result old_value :
 VM.find 858 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1028 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1092 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 858 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1028 H1092 Step.
 eapply (concrete_register_mux_commit 867 flat_statements joint_register_858_decl joint_register_858_mid joint_register_858_tail 858 joint_register_858_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1092)) (@Eref VarOrder.T (@Eid VarOrder.T 1028)) inputs path flat_memories old current result old_value 32
 joint_register_858_position joint_register_858_split joint_register_858_straight joint_register_858_mid_safe joint_register_858_tail_safe Old Typed joint_register_858_identity).
 - apply joint_register_ready_858; assumption.
 - exact Step.
Qed.
Definition joint_register_859_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 859)))).
Definition joint_register_859_decl := match straight_drop 869 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_859_tail := match straight_drop 1201 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_859_mid := take_statements 331 joint_register_859_decl.
Lemma joint_register_859_position : straight_drop 868 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 859 joint_register_859_reg) joint_register_859_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_859_split : joint_register_859_decl = statement_append joint_register_859_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 859) joint_register_update_859) joint_register_859_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_859_straight : straight_statements joint_register_859_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_859_mid_safe : formal_typed_suffix_safe flat_memories 859 joint_register_859_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_859_tail_safe : formal_typed_suffix_safe flat_memories 859 joint_register_859_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_859_identity : register_identity_b 859 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_859_commit inputs path old current result old_value :
 VM.find 859 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1029 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1093 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 859 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1029 H1093 Step.
 eapply (concrete_register_mux_commit 868 flat_statements joint_register_859_decl joint_register_859_mid joint_register_859_tail 859 joint_register_859_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1093)) (@Eref VarOrder.T (@Eid VarOrder.T 1029)) inputs path flat_memories old current result old_value 32
 joint_register_859_position joint_register_859_split joint_register_859_straight joint_register_859_mid_safe joint_register_859_tail_safe Old Typed joint_register_859_identity).
 - apply joint_register_ready_859; assumption.
 - exact Step.
Qed.
Definition joint_register_860_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 860)))).
Definition joint_register_860_decl := match straight_drop 870 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_860_tail := match straight_drop 1202 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_860_mid := take_statements 331 joint_register_860_decl.
Lemma joint_register_860_position : straight_drop 869 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 860 joint_register_860_reg) joint_register_860_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_860_split : joint_register_860_decl = statement_append joint_register_860_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 860) joint_register_update_860) joint_register_860_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_860_straight : straight_statements joint_register_860_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_860_mid_safe : formal_typed_suffix_safe flat_memories 860 joint_register_860_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_860_tail_safe : formal_typed_suffix_safe flat_memories 860 joint_register_860_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_860_identity : register_identity_b 860 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_860_commit inputs path old current result old_value :
 VM.find 860 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1030 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1094 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 860 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1030 H1094 Step.
 eapply (concrete_register_mux_commit 869 flat_statements joint_register_860_decl joint_register_860_mid joint_register_860_tail 860 joint_register_860_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1094)) (@Eref VarOrder.T (@Eid VarOrder.T 1030)) inputs path flat_memories old current result old_value 32
 joint_register_860_position joint_register_860_split joint_register_860_straight joint_register_860_mid_safe joint_register_860_tail_safe Old Typed joint_register_860_identity).
 - apply joint_register_ready_860; assumption.
 - exact Step.
Qed.
Definition joint_register_861_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 861)))).
Definition joint_register_861_decl := match straight_drop 871 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_861_tail := match straight_drop 1203 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_861_mid := take_statements 331 joint_register_861_decl.
Lemma joint_register_861_position : straight_drop 870 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 861 joint_register_861_reg) joint_register_861_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_861_split : joint_register_861_decl = statement_append joint_register_861_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 861) joint_register_update_861) joint_register_861_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_861_straight : straight_statements joint_register_861_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_861_mid_safe : formal_typed_suffix_safe flat_memories 861 joint_register_861_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_861_tail_safe : formal_typed_suffix_safe flat_memories 861 joint_register_861_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_861_identity : register_identity_b 861 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_861_commit inputs path old current result old_value :
 VM.find 861 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1031 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1095 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 861 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1031 H1095 Step.
 eapply (concrete_register_mux_commit 870 flat_statements joint_register_861_decl joint_register_861_mid joint_register_861_tail 861 joint_register_861_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1095)) (@Eref VarOrder.T (@Eid VarOrder.T 1031)) inputs path flat_memories old current result old_value 32
 joint_register_861_position joint_register_861_split joint_register_861_straight joint_register_861_mid_safe joint_register_861_tail_safe Old Typed joint_register_861_identity).
 - apply joint_register_ready_861; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_861_commit.
