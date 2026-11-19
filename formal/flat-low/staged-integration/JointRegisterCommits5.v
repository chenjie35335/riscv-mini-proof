Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_870_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 870)))).
Definition joint_register_870_decl := match straight_drop 880 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_870_tail := match straight_drop 1212 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_870_mid := take_statements 331 joint_register_870_decl.
Lemma joint_register_870_position : straight_drop 879 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 870 joint_register_870_reg) joint_register_870_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_870_split : joint_register_870_decl = statement_append joint_register_870_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 870) joint_register_update_870) joint_register_870_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_870_straight : straight_statements joint_register_870_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_870_mid_safe : formal_typed_suffix_safe flat_memories 870 joint_register_870_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_870_tail_safe : formal_typed_suffix_safe flat_memories 870 joint_register_870_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_870_identity : register_identity_b 870 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_870_commit inputs path old current result old_value :
 VM.find 870 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1040 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1104 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 870 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1040 H1104 Step.
 eapply (concrete_register_mux_commit 879 flat_statements joint_register_870_decl joint_register_870_mid joint_register_870_tail 870 joint_register_870_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1104)) (@Eref VarOrder.T (@Eid VarOrder.T 1040)) inputs path flat_memories old current result old_value 32
 joint_register_870_position joint_register_870_split joint_register_870_straight joint_register_870_mid_safe joint_register_870_tail_safe Old Typed joint_register_870_identity).
 - apply joint_register_ready_870; assumption.
 - exact Step.
Qed.
Definition joint_register_871_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 871)))).
Definition joint_register_871_decl := match straight_drop 881 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_871_tail := match straight_drop 1213 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_871_mid := take_statements 331 joint_register_871_decl.
Lemma joint_register_871_position : straight_drop 880 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 871 joint_register_871_reg) joint_register_871_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_871_split : joint_register_871_decl = statement_append joint_register_871_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 871) joint_register_update_871) joint_register_871_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_871_straight : straight_statements joint_register_871_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_871_mid_safe : formal_typed_suffix_safe flat_memories 871 joint_register_871_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_871_tail_safe : formal_typed_suffix_safe flat_memories 871 joint_register_871_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_871_identity : register_identity_b 871 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_871_commit inputs path old current result old_value :
 VM.find 871 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1041 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1105 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 871 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1041 H1105 Step.
 eapply (concrete_register_mux_commit 880 flat_statements joint_register_871_decl joint_register_871_mid joint_register_871_tail 871 joint_register_871_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1105)) (@Eref VarOrder.T (@Eid VarOrder.T 1041)) inputs path flat_memories old current result old_value 32
 joint_register_871_position joint_register_871_split joint_register_871_straight joint_register_871_mid_safe joint_register_871_tail_safe Old Typed joint_register_871_identity).
 - apply joint_register_ready_871; assumption.
 - exact Step.
Qed.
Definition joint_register_872_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 872)))).
Definition joint_register_872_decl := match straight_drop 882 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_872_tail := match straight_drop 1214 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_872_mid := take_statements 331 joint_register_872_decl.
Lemma joint_register_872_position : straight_drop 881 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 872 joint_register_872_reg) joint_register_872_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_872_split : joint_register_872_decl = statement_append joint_register_872_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 872) joint_register_update_872) joint_register_872_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_872_straight : straight_statements joint_register_872_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_872_mid_safe : formal_typed_suffix_safe flat_memories 872 joint_register_872_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_872_tail_safe : formal_typed_suffix_safe flat_memories 872 joint_register_872_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_872_identity : register_identity_b 872 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_872_commit inputs path old current result old_value :
 VM.find 872 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1042 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1106 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 872 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1042 H1106 Step.
 eapply (concrete_register_mux_commit 881 flat_statements joint_register_872_decl joint_register_872_mid joint_register_872_tail 872 joint_register_872_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1106)) (@Eref VarOrder.T (@Eid VarOrder.T 1042)) inputs path flat_memories old current result old_value 32
 joint_register_872_position joint_register_872_split joint_register_872_straight joint_register_872_mid_safe joint_register_872_tail_safe Old Typed joint_register_872_identity).
 - apply joint_register_ready_872; assumption.
 - exact Step.
Qed.
Definition joint_register_873_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 873)))).
Definition joint_register_873_decl := match straight_drop 883 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_873_tail := match straight_drop 1215 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_873_mid := take_statements 331 joint_register_873_decl.
Lemma joint_register_873_position : straight_drop 882 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 873 joint_register_873_reg) joint_register_873_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_873_split : joint_register_873_decl = statement_append joint_register_873_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 873) joint_register_update_873) joint_register_873_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_873_straight : straight_statements joint_register_873_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_873_mid_safe : formal_typed_suffix_safe flat_memories 873 joint_register_873_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_873_tail_safe : formal_typed_suffix_safe flat_memories 873 joint_register_873_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_873_identity : register_identity_b 873 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_873_commit inputs path old current result old_value :
 VM.find 873 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1043 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1107 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 873 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1043 H1107 Step.
 eapply (concrete_register_mux_commit 882 flat_statements joint_register_873_decl joint_register_873_mid joint_register_873_tail 873 joint_register_873_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1107)) (@Eref VarOrder.T (@Eid VarOrder.T 1043)) inputs path flat_memories old current result old_value 32
 joint_register_873_position joint_register_873_split joint_register_873_straight joint_register_873_mid_safe joint_register_873_tail_safe Old Typed joint_register_873_identity).
 - apply joint_register_ready_873; assumption.
 - exact Step.
Qed.
Definition joint_register_874_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 874)))).
Definition joint_register_874_decl := match straight_drop 884 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_874_tail := match straight_drop 1216 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_874_mid := take_statements 331 joint_register_874_decl.
Lemma joint_register_874_position : straight_drop 883 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 874 joint_register_874_reg) joint_register_874_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_874_split : joint_register_874_decl = statement_append joint_register_874_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 874) joint_register_update_874) joint_register_874_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_874_straight : straight_statements joint_register_874_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_874_mid_safe : formal_typed_suffix_safe flat_memories 874 joint_register_874_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_874_tail_safe : formal_typed_suffix_safe flat_memories 874 joint_register_874_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_874_identity : register_identity_b 874 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_874_commit inputs path old current result old_value :
 VM.find 874 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1044 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1108 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 874 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1044 H1108 Step.
 eapply (concrete_register_mux_commit 883 flat_statements joint_register_874_decl joint_register_874_mid joint_register_874_tail 874 joint_register_874_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1108)) (@Eref VarOrder.T (@Eid VarOrder.T 1044)) inputs path flat_memories old current result old_value 32
 joint_register_874_position joint_register_874_split joint_register_874_straight joint_register_874_mid_safe joint_register_874_tail_safe Old Typed joint_register_874_identity).
 - apply joint_register_ready_874; assumption.
 - exact Step.
Qed.
Definition joint_register_875_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 875)))).
Definition joint_register_875_decl := match straight_drop 885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_875_tail := match straight_drop 1217 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_875_mid := take_statements 331 joint_register_875_decl.
Lemma joint_register_875_position : straight_drop 884 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 875 joint_register_875_reg) joint_register_875_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_875_split : joint_register_875_decl = statement_append joint_register_875_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 875) joint_register_update_875) joint_register_875_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_875_straight : straight_statements joint_register_875_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_875_mid_safe : formal_typed_suffix_safe flat_memories 875 joint_register_875_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_875_tail_safe : formal_typed_suffix_safe flat_memories 875 joint_register_875_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_875_identity : register_identity_b 875 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_875_commit inputs path old current result old_value :
 VM.find 875 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1045 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1109 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 875 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1045 H1109 Step.
 eapply (concrete_register_mux_commit 884 flat_statements joint_register_875_decl joint_register_875_mid joint_register_875_tail 875 joint_register_875_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1109)) (@Eref VarOrder.T (@Eid VarOrder.T 1045)) inputs path flat_memories old current result old_value 32
 joint_register_875_position joint_register_875_split joint_register_875_straight joint_register_875_mid_safe joint_register_875_tail_safe Old Typed joint_register_875_identity).
 - apply joint_register_ready_875; assumption.
 - exact Step.
Qed.
Definition joint_register_876_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 876)))).
Definition joint_register_876_decl := match straight_drop 886 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_876_tail := match straight_drop 1218 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_876_mid := take_statements 331 joint_register_876_decl.
Lemma joint_register_876_position : straight_drop 885 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 876 joint_register_876_reg) joint_register_876_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_876_split : joint_register_876_decl = statement_append joint_register_876_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 876) joint_register_update_876) joint_register_876_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_876_straight : straight_statements joint_register_876_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_876_mid_safe : formal_typed_suffix_safe flat_memories 876 joint_register_876_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_876_tail_safe : formal_typed_suffix_safe flat_memories 876 joint_register_876_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_876_identity : register_identity_b 876 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_876_commit inputs path old current result old_value :
 VM.find 876 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1046 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1110 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 876 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1046 H1110 Step.
 eapply (concrete_register_mux_commit 885 flat_statements joint_register_876_decl joint_register_876_mid joint_register_876_tail 876 joint_register_876_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1110)) (@Eref VarOrder.T (@Eid VarOrder.T 1046)) inputs path flat_memories old current result old_value 32
 joint_register_876_position joint_register_876_split joint_register_876_straight joint_register_876_mid_safe joint_register_876_tail_safe Old Typed joint_register_876_identity).
 - apply joint_register_ready_876; assumption.
 - exact Step.
Qed.
Definition joint_register_877_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 877)))).
Definition joint_register_877_decl := match straight_drop 887 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_877_tail := match straight_drop 1219 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_877_mid := take_statements 331 joint_register_877_decl.
Lemma joint_register_877_position : straight_drop 886 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 877 joint_register_877_reg) joint_register_877_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_877_split : joint_register_877_decl = statement_append joint_register_877_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 877) joint_register_update_877) joint_register_877_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_877_straight : straight_statements joint_register_877_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_877_mid_safe : formal_typed_suffix_safe flat_memories 877 joint_register_877_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_877_tail_safe : formal_typed_suffix_safe flat_memories 877 joint_register_877_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_877_identity : register_identity_b 877 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_877_commit inputs path old current result old_value :
 VM.find 877 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1047 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1111 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 877 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1047 H1111 Step.
 eapply (concrete_register_mux_commit 886 flat_statements joint_register_877_decl joint_register_877_mid joint_register_877_tail 877 joint_register_877_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1111)) (@Eref VarOrder.T (@Eid VarOrder.T 1047)) inputs path flat_memories old current result old_value 32
 joint_register_877_position joint_register_877_split joint_register_877_straight joint_register_877_mid_safe joint_register_877_tail_safe Old Typed joint_register_877_identity).
 - apply joint_register_ready_877; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_877_commit.
