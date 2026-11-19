Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_878_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 878)))).
Definition joint_register_878_decl := match straight_drop 888 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_878_tail := match straight_drop 1220 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_878_mid := take_statements 331 joint_register_878_decl.
Lemma joint_register_878_position : straight_drop 887 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 878 joint_register_878_reg) joint_register_878_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_878_split : joint_register_878_decl = statement_append joint_register_878_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 878) joint_register_update_878) joint_register_878_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_878_straight : straight_statements joint_register_878_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_878_mid_safe : formal_typed_suffix_safe flat_memories 878 joint_register_878_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_878_tail_safe : formal_typed_suffix_safe flat_memories 878 joint_register_878_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_878_identity : register_identity_b 878 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_878_commit inputs path old current result old_value :
 VM.find 878 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1048 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1112 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 878 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1048 H1112 Step.
 eapply (concrete_register_mux_commit 887 flat_statements joint_register_878_decl joint_register_878_mid joint_register_878_tail 878 joint_register_878_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1112)) (@Eref VarOrder.T (@Eid VarOrder.T 1048)) inputs path flat_memories old current result old_value 32
 joint_register_878_position joint_register_878_split joint_register_878_straight joint_register_878_mid_safe joint_register_878_tail_safe Old Typed joint_register_878_identity).
 - apply joint_register_ready_878; assumption.
 - exact Step.
Qed.
Definition joint_register_879_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 879)))).
Definition joint_register_879_decl := match straight_drop 889 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_879_tail := match straight_drop 1221 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_879_mid := take_statements 331 joint_register_879_decl.
Lemma joint_register_879_position : straight_drop 888 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 879 joint_register_879_reg) joint_register_879_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_879_split : joint_register_879_decl = statement_append joint_register_879_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 879) joint_register_update_879) joint_register_879_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_879_straight : straight_statements joint_register_879_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_879_mid_safe : formal_typed_suffix_safe flat_memories 879 joint_register_879_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_879_tail_safe : formal_typed_suffix_safe flat_memories 879 joint_register_879_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_879_identity : register_identity_b 879 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_879_commit inputs path old current result old_value :
 VM.find 879 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1049 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1113 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 879 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1049 H1113 Step.
 eapply (concrete_register_mux_commit 888 flat_statements joint_register_879_decl joint_register_879_mid joint_register_879_tail 879 joint_register_879_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1113)) (@Eref VarOrder.T (@Eid VarOrder.T 1049)) inputs path flat_memories old current result old_value 32
 joint_register_879_position joint_register_879_split joint_register_879_straight joint_register_879_mid_safe joint_register_879_tail_safe Old Typed joint_register_879_identity).
 - apply joint_register_ready_879; assumption.
 - exact Step.
Qed.
Definition joint_register_880_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 880)))).
Definition joint_register_880_decl := match straight_drop 890 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_880_tail := match straight_drop 1222 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_880_mid := take_statements 331 joint_register_880_decl.
Lemma joint_register_880_position : straight_drop 889 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 880 joint_register_880_reg) joint_register_880_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_880_split : joint_register_880_decl = statement_append joint_register_880_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 880) joint_register_update_880) joint_register_880_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_880_straight : straight_statements joint_register_880_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_880_mid_safe : formal_typed_suffix_safe flat_memories 880 joint_register_880_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_880_tail_safe : formal_typed_suffix_safe flat_memories 880 joint_register_880_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_880_identity : register_identity_b 880 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_880_commit inputs path old current result old_value :
 VM.find 880 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1050 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1114 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 880 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1050 H1114 Step.
 eapply (concrete_register_mux_commit 889 flat_statements joint_register_880_decl joint_register_880_mid joint_register_880_tail 880 joint_register_880_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1114)) (@Eref VarOrder.T (@Eid VarOrder.T 1050)) inputs path flat_memories old current result old_value 32
 joint_register_880_position joint_register_880_split joint_register_880_straight joint_register_880_mid_safe joint_register_880_tail_safe Old Typed joint_register_880_identity).
 - apply joint_register_ready_880; assumption.
 - exact Step.
Qed.
Definition joint_register_881_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 881)))).
Definition joint_register_881_decl := match straight_drop 891 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_881_tail := match straight_drop 1223 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_881_mid := take_statements 331 joint_register_881_decl.
Lemma joint_register_881_position : straight_drop 890 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 881 joint_register_881_reg) joint_register_881_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_881_split : joint_register_881_decl = statement_append joint_register_881_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 881) joint_register_update_881) joint_register_881_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_881_straight : straight_statements joint_register_881_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_881_mid_safe : formal_typed_suffix_safe flat_memories 881 joint_register_881_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_881_tail_safe : formal_typed_suffix_safe flat_memories 881 joint_register_881_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_881_identity : register_identity_b 881 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_881_commit inputs path old current result old_value :
 VM.find 881 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1051 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1115 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 881 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1051 H1115 Step.
 eapply (concrete_register_mux_commit 890 flat_statements joint_register_881_decl joint_register_881_mid joint_register_881_tail 881 joint_register_881_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1115)) (@Eref VarOrder.T (@Eid VarOrder.T 1051)) inputs path flat_memories old current result old_value 32
 joint_register_881_position joint_register_881_split joint_register_881_straight joint_register_881_mid_safe joint_register_881_tail_safe Old Typed joint_register_881_identity).
 - apply joint_register_ready_881; assumption.
 - exact Step.
Qed.
Definition joint_register_882_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 778)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 882)))).
Definition joint_register_882_decl := match straight_drop 892 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_882_tail := match straight_drop 1224 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_882_mid := take_statements 331 joint_register_882_decl.
Lemma joint_register_882_position : straight_drop 891 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 882 joint_register_882_reg) joint_register_882_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_882_split : joint_register_882_decl = statement_append joint_register_882_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 882) joint_register_update_882) joint_register_882_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_882_straight : straight_statements joint_register_882_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_882_mid_safe : formal_typed_suffix_safe flat_memories 882 joint_register_882_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_882_tail_safe : formal_typed_suffix_safe flat_memories 882 joint_register_882_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_882_identity : register_identity_b 882 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_882_commit inputs path old current result old_value :
 VM.find 882 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 779 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1052 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 1116 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 882 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H779 H1052 H1116 Step.
 eapply (concrete_register_mux_commit 891 flat_statements joint_register_882_decl joint_register_882_mid joint_register_882_tail 882 joint_register_882_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1116)) (@Eref VarOrder.T (@Eid VarOrder.T 1052)) inputs path flat_memories old current result old_value 32
 joint_register_882_position joint_register_882_split joint_register_882_straight joint_register_882_mid_safe joint_register_882_tail_safe Old Typed joint_register_882_identity).
 - apply joint_register_ready_882; assumption.
 - exact Step.
Qed.
Definition joint_register_7748_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7748)))).
Definition joint_register_7748_decl := match straight_drop 8255 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7748_tail := match straight_drop 8851 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7748_mid := take_statements 595 joint_register_7748_decl.
Lemma joint_register_7748_position : straight_drop 8254 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7748 joint_register_7748_reg) joint_register_7748_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7748_split : joint_register_7748_decl = statement_append joint_register_7748_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7748) joint_register_update_7748) joint_register_7748_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7748_straight : straight_statements joint_register_7748_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7748_mid_safe : formal_typed_suffix_safe flat_memories 7748 joint_register_7748_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7748_tail_safe : formal_typed_suffix_safe flat_memories 7748 joint_register_7748_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7748_identity : register_identity_b 7748 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7748_commit inputs path old current result old_value :
 VM.find 7748 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7801 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8158 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7748 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7801 H8158 Step.
 eapply (concrete_register_mux_commit 8254 flat_statements joint_register_7748_decl joint_register_7748_mid joint_register_7748_tail 7748 joint_register_7748_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8158)) (@Eref VarOrder.T (@Eid VarOrder.T 7801)) inputs path flat_memories old current result old_value 32
 joint_register_7748_position joint_register_7748_split joint_register_7748_straight joint_register_7748_mid_safe joint_register_7748_tail_safe Old Typed joint_register_7748_identity).
 - apply joint_register_ready_7748; assumption.
 - exact Step.
Qed.
Definition joint_register_7749_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7749)))).
Definition joint_register_7749_decl := match straight_drop 8256 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7749_tail := match straight_drop 8852 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7749_mid := take_statements 595 joint_register_7749_decl.
Lemma joint_register_7749_position : straight_drop 8255 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7749 joint_register_7749_reg) joint_register_7749_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7749_split : joint_register_7749_decl = statement_append joint_register_7749_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7749) joint_register_update_7749) joint_register_7749_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7749_straight : straight_statements joint_register_7749_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7749_mid_safe : formal_typed_suffix_safe flat_memories 7749 joint_register_7749_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7749_tail_safe : formal_typed_suffix_safe flat_memories 7749 joint_register_7749_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7749_identity : register_identity_b 7749 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7749_commit inputs path old current result old_value :
 VM.find 7749 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7800 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8159 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7749 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7800 H8159 Step.
 eapply (concrete_register_unary_commit 8255 flat_statements joint_register_7749_decl joint_register_7749_mid joint_register_7749_tail 7749 joint_register_7749_reg (Uextr 31 0) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8159)) (@Eref VarOrder.T (@Eid VarOrder.T 7800))) inputs path flat_memories old current result old_value 32
 joint_register_7749_position joint_register_7749_split joint_register_7749_straight joint_register_7749_mid_safe joint_register_7749_tail_safe Old Typed joint_register_7749_identity).
 - apply joint_register_ready_7749; assumption.
 - exact Step.
Qed.
Definition joint_register_7750_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7750)))).
Definition joint_register_7750_decl := match straight_drop 8257 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7750_tail := match straight_drop 8853 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7750_mid := take_statements 595 joint_register_7750_decl.
Lemma joint_register_7750_position : straight_drop 8256 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7750 joint_register_7750_reg) joint_register_7750_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7750_split : joint_register_7750_decl = statement_append joint_register_7750_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7750) joint_register_update_7750) joint_register_7750_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7750_straight : straight_statements joint_register_7750_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7750_mid_safe : formal_typed_suffix_safe flat_memories 7750 joint_register_7750_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7750_tail_safe : formal_typed_suffix_safe flat_memories 7750 joint_register_7750_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7750_identity : register_identity_b 7750 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_register_7750_commit inputs path old current result old_value :
 VM.find 7750 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 7878 old = Some (Gval ground bits)) ->
 (exists ground bits, VM.find 8160 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = 32%nat /\ VM.find 7750 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed H65 H7878 H8160 Step.
 eapply (concrete_register_mux_commit 8256 flat_statements joint_register_7750_decl joint_register_7750_mid joint_register_7750_tail 7750 joint_register_7750_reg (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8160)) (@Eref VarOrder.T (@Eid VarOrder.T 7878)) inputs path flat_memories old current result old_value 32
 joint_register_7750_position joint_register_7750_split joint_register_7750_straight joint_register_7750_mid_safe joint_register_7750_tail_safe Old Typed joint_register_7750_identity).
 - apply joint_register_ready_7750; assumption.
 - exact Step.
Qed.
Print Assumptions joint_register_7750_commit.
