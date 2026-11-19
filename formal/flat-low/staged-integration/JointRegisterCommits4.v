Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_862_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 862)))).
Definition joint_register_862_decl := match straight_drop 872 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_862_tail := match straight_drop 1204 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_862_mid := take_statements 331 joint_register_862_decl.
Lemma joint_register_862_position : straight_drop 871 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 862 joint_register_862_reg) joint_register_862_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_862_split : joint_register_862_decl = statement_append joint_register_862_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 862) joint_register_update_862) joint_register_862_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_862_straight : straight_statements joint_register_862_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_862_mid_safe : formal_typed_suffix_safe flat_memories 862 joint_register_862_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_862_tail_safe : formal_typed_suffix_safe flat_memories 862 joint_register_862_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_862_identity : register_identity_b 862 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_862_commit inputs path old current result old_value :
 VM.find 862 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1032 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1096 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 862 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1032 H1096 Step.
 eapply (concrete_register_mux_commit 871 flat_statements joint_register_862_decl joint_register_862_mid joint_register_862_tail 862 joint_register_862_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1096)) (@Eref VarOrder.T (@Eid VarOrder.T 1032)) inputs path flat_memories old current result old_value 32
 joint_register_862_position joint_register_862_split joint_register_862_straight joint_register_862_mid_safe joint_register_862_tail_safe Old Typed joint_register_862_identity).
 - apply joint_register_ready_862; assumption.
 - exact Step.
Qed.
Definition joint_register_863_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 863)))).
Definition joint_register_863_decl := match straight_drop 873 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_863_tail := match straight_drop 1205 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_863_mid := take_statements 331 joint_register_863_decl.
Lemma joint_register_863_position : straight_drop 872 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 863 joint_register_863_reg) joint_register_863_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_863_split : joint_register_863_decl = statement_append joint_register_863_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 863) joint_register_update_863) joint_register_863_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_863_straight : straight_statements joint_register_863_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_863_mid_safe : formal_typed_suffix_safe flat_memories 863 joint_register_863_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_863_tail_safe : formal_typed_suffix_safe flat_memories 863 joint_register_863_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_863_identity : register_identity_b 863 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_863_commit inputs path old current result old_value :
 VM.find 863 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1033 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1097 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 863 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1033 H1097 Step.
 eapply (concrete_register_mux_commit 872 flat_statements joint_register_863_decl joint_register_863_mid joint_register_863_tail 863 joint_register_863_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1097)) (@Eref VarOrder.T (@Eid VarOrder.T 1033)) inputs path flat_memories old current result old_value 32
 joint_register_863_position joint_register_863_split joint_register_863_straight joint_register_863_mid_safe joint_register_863_tail_safe Old Typed joint_register_863_identity).
 - apply joint_register_ready_863; assumption.
 - exact Step.
Qed.
Definition joint_register_864_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 864)))).
Definition joint_register_864_decl := match straight_drop 874 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_864_tail := match straight_drop 1206 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_864_mid := take_statements 331 joint_register_864_decl.
Lemma joint_register_864_position : straight_drop 873 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 864 joint_register_864_reg) joint_register_864_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_864_split : joint_register_864_decl = statement_append joint_register_864_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 864) joint_register_update_864) joint_register_864_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_864_straight : straight_statements joint_register_864_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_864_mid_safe : formal_typed_suffix_safe flat_memories 864 joint_register_864_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_864_tail_safe : formal_typed_suffix_safe flat_memories 864 joint_register_864_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_864_identity : register_identity_b 864 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_864_commit inputs path old current result old_value :
 VM.find 864 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1034 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1098 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 864 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1034 H1098 Step.
 eapply (concrete_register_mux_commit 873 flat_statements joint_register_864_decl joint_register_864_mid joint_register_864_tail 864 joint_register_864_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1098)) (@Eref VarOrder.T (@Eid VarOrder.T 1034)) inputs path flat_memories old current result old_value 32
 joint_register_864_position joint_register_864_split joint_register_864_straight joint_register_864_mid_safe joint_register_864_tail_safe Old Typed joint_register_864_identity).
 - apply joint_register_ready_864; assumption.
 - exact Step.
Qed.
Definition joint_register_865_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 865)))).
Definition joint_register_865_decl := match straight_drop 875 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_865_tail := match straight_drop 1207 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_865_mid := take_statements 331 joint_register_865_decl.
Lemma joint_register_865_position : straight_drop 874 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 865 joint_register_865_reg) joint_register_865_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_865_split : joint_register_865_decl = statement_append joint_register_865_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 865) joint_register_update_865) joint_register_865_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_865_straight : straight_statements joint_register_865_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_865_mid_safe : formal_typed_suffix_safe flat_memories 865 joint_register_865_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_865_tail_safe : formal_typed_suffix_safe flat_memories 865 joint_register_865_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_865_identity : register_identity_b 865 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_865_commit inputs path old current result old_value :
 VM.find 865 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1035 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1099 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 865 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1035 H1099 Step.
 eapply (concrete_register_mux_commit 874 flat_statements joint_register_865_decl joint_register_865_mid joint_register_865_tail 865 joint_register_865_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1099)) (@Eref VarOrder.T (@Eid VarOrder.T 1035)) inputs path flat_memories old current result old_value 32
 joint_register_865_position joint_register_865_split joint_register_865_straight joint_register_865_mid_safe joint_register_865_tail_safe Old Typed joint_register_865_identity).
 - apply joint_register_ready_865; assumption.
 - exact Step.
Qed.
Definition joint_register_866_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 866)))).
Definition joint_register_866_decl := match straight_drop 876 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_866_tail := match straight_drop 1208 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_866_mid := take_statements 331 joint_register_866_decl.
Lemma joint_register_866_position : straight_drop 875 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 866 joint_register_866_reg) joint_register_866_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_866_split : joint_register_866_decl = statement_append joint_register_866_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 866) joint_register_update_866) joint_register_866_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_866_straight : straight_statements joint_register_866_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_866_mid_safe : formal_typed_suffix_safe flat_memories 866 joint_register_866_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_866_tail_safe : formal_typed_suffix_safe flat_memories 866 joint_register_866_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_866_identity : register_identity_b 866 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_866_commit inputs path old current result old_value :
 VM.find 866 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1036 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1100 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 866 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1036 H1100 Step.
 eapply (concrete_register_mux_commit 875 flat_statements joint_register_866_decl joint_register_866_mid joint_register_866_tail 866 joint_register_866_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1100)) (@Eref VarOrder.T (@Eid VarOrder.T 1036)) inputs path flat_memories old current result old_value 32
 joint_register_866_position joint_register_866_split joint_register_866_straight joint_register_866_mid_safe joint_register_866_tail_safe Old Typed joint_register_866_identity).
 - apply joint_register_ready_866; assumption.
 - exact Step.
Qed.
Definition joint_register_867_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 867)))).
Definition joint_register_867_decl := match straight_drop 877 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_867_tail := match straight_drop 1209 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_867_mid := take_statements 331 joint_register_867_decl.
Lemma joint_register_867_position : straight_drop 876 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 867 joint_register_867_reg) joint_register_867_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_867_split : joint_register_867_decl = statement_append joint_register_867_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 867) joint_register_update_867) joint_register_867_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_867_straight : straight_statements joint_register_867_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_867_mid_safe : formal_typed_suffix_safe flat_memories 867 joint_register_867_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_867_tail_safe : formal_typed_suffix_safe flat_memories 867 joint_register_867_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_867_identity : register_identity_b 867 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_867_commit inputs path old current result old_value :
 VM.find 867 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1037 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1101 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 867 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1037 H1101 Step.
 eapply (concrete_register_mux_commit 876 flat_statements joint_register_867_decl joint_register_867_mid joint_register_867_tail 867 joint_register_867_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1101)) (@Eref VarOrder.T (@Eid VarOrder.T 1037)) inputs path flat_memories old current result old_value 32
 joint_register_867_position joint_register_867_split joint_register_867_straight joint_register_867_mid_safe joint_register_867_tail_safe Old Typed joint_register_867_identity).
 - apply joint_register_ready_867; assumption.
 - exact Step.
Qed.
Definition joint_register_868_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 868)))).
Definition joint_register_868_decl := match straight_drop 878 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_868_tail := match straight_drop 1210 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_868_mid := take_statements 331 joint_register_868_decl.
Lemma joint_register_868_position : straight_drop 877 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 868 joint_register_868_reg) joint_register_868_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_868_split : joint_register_868_decl = statement_append joint_register_868_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 868) joint_register_update_868) joint_register_868_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_868_straight : straight_statements joint_register_868_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_868_mid_safe : formal_typed_suffix_safe flat_memories 868 joint_register_868_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_868_tail_safe : formal_typed_suffix_safe flat_memories 868 joint_register_868_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_868_identity : register_identity_b 868 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_868_commit inputs path old current result old_value :
 VM.find 868 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1038 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1102 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 868 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1038 H1102 Step.
 eapply (concrete_register_mux_commit 877 flat_statements joint_register_868_decl joint_register_868_mid joint_register_868_tail 868 joint_register_868_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1102)) (@Eref VarOrder.T (@Eid VarOrder.T 1038)) inputs path flat_memories old current result old_value 32
 joint_register_868_position joint_register_868_split joint_register_868_straight joint_register_868_mid_safe joint_register_868_tail_safe Old Typed joint_register_868_identity).
 - apply joint_register_ready_868; assumption.
 - exact Step.
Qed.
Definition joint_register_869_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 869)))).
Definition joint_register_869_decl := match straight_drop 879 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_869_tail := match straight_drop 1211 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_869_mid := take_statements 331 joint_register_869_decl.
Lemma joint_register_869_position : straight_drop 878 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 869 joint_register_869_reg) joint_register_869_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_869_split : joint_register_869_decl = statement_append joint_register_869_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 869) joint_register_update_869) joint_register_869_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_869_straight : straight_statements joint_register_869_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_869_mid_safe : formal_typed_suffix_safe flat_memories 869 joint_register_869_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_869_tail_safe : formal_typed_suffix_safe flat_memories 869 joint_register_869_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_869_identity : register_identity_b 869 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_869_commit inputs path old current result old_value :
 VM.find 869 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1039 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1103 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 869 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1039 H1103 Step.
 eapply (concrete_register_mux_commit 878 flat_statements joint_register_869_decl joint_register_869_mid joint_register_869_tail 869 joint_register_869_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1103)) (@Eref VarOrder.T (@Eid VarOrder.T 1039)) inputs path flat_memories old current result old_value 32
 joint_register_869_position joint_register_869_split joint_register_869_straight joint_register_869_mid_safe joint_register_869_tail_safe Old Typed joint_register_869_identity).
 - apply joint_register_ready_869; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_869_commit.
