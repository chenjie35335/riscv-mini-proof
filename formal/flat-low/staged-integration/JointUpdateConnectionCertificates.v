Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection FormalDeclaredConcreteUnaryConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_update_connection_24_decl := match straight_drop 2 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_24_tail := match straight_drop 10094 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_24_mid := take_statements 10091 joint_update_connection_24_decl.
Lemma joint_update_connection_24_position : straight_drop 1 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 24 (Gtyp (Fuint 1))) joint_update_connection_24_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_24_split : joint_update_connection_24_decl = statement_append joint_update_connection_24_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 24) (@Eref VarOrder.T (@Eid VarOrder.T 1))) joint_update_connection_24_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_24_straight : straight_statements joint_update_connection_24_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_24_mid_safe : formal_typed_suffix_safe flat_memories 24 joint_update_connection_24_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_24_tail_safe : formal_typed_suffix_safe flat_memories 24 joint_update_connection_24_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_24_nonregister : has_register 24 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_24_output invalid old current result :
 (exists ground bits, VM.find 1 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 24 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1 flat_statements joint_update_connection_24_decl joint_update_connection_24_mid joint_update_connection_24_tail
 24 1 1 ground bits invalid flat_memories old current result
 joint_update_connection_24_position joint_update_connection_24_split joint_update_connection_24_straight joint_update_connection_24_mid_safe joint_update_connection_24_tail_safe
 joint_update_connection_24_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_34_decl := match straight_drop 12 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_34_tail := match straight_drop 10098 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_34_mid := take_statements 10085 joint_update_connection_34_decl.
Lemma joint_update_connection_34_position : straight_drop 11 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 34 (Gtyp (Fuint 32))) joint_update_connection_34_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_34_split : joint_update_connection_34_decl = statement_append joint_update_connection_34_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 34) (@Eref VarOrder.T (@Eid VarOrder.T 9220))) joint_update_connection_34_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_34_straight : straight_statements joint_update_connection_34_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_34_mid_safe : formal_typed_suffix_safe flat_memories 34 joint_update_connection_34_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_34_tail_safe : formal_typed_suffix_safe flat_memories 34 joint_update_connection_34_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_34_nonregister : has_register 34 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_34_output invalid old current result :
 (exists ground bits, VM.find 9220 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 34 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 11 flat_statements joint_update_connection_34_decl joint_update_connection_34_mid joint_update_connection_34_tail
 34 9220 32 ground bits invalid flat_memories old current result
 joint_update_connection_34_position joint_update_connection_34_split joint_update_connection_34_straight joint_update_connection_34_mid_safe joint_update_connection_34_tail_safe
 joint_update_connection_34_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_41_decl := match straight_drop 19 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_41_tail := match straight_drop 10100 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_41_mid := take_statements 10080 joint_update_connection_41_decl.
Lemma joint_update_connection_41_position : straight_drop 18 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 41 (Gtyp (Fuint 32))) joint_update_connection_41_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_41_split : joint_update_connection_41_decl = statement_append joint_update_connection_41_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 41) (@Eref VarOrder.T (@Eid VarOrder.T 9222))) joint_update_connection_41_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_41_straight : straight_statements joint_update_connection_41_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_41_mid_safe : formal_typed_suffix_safe flat_memories 41 joint_update_connection_41_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_41_tail_safe : formal_typed_suffix_safe flat_memories 41 joint_update_connection_41_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_41_nonregister : has_register 41 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_41_output invalid old current result :
 (exists ground bits, VM.find 9222 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 41 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 18 flat_statements joint_update_connection_41_decl joint_update_connection_41_mid joint_update_connection_41_tail
 41 9222 32 ground bits invalid flat_memories old current result
 joint_update_connection_41_position joint_update_connection_41_split joint_update_connection_41_straight joint_update_connection_41_mid_safe joint_update_connection_41_tail_safe
 joint_update_connection_41_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_118_decl := match straight_drop 96 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_118_tail := match straight_drop 8787 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_118_mid := take_statements 8690 joint_update_connection_118_decl.
Lemma joint_update_connection_118_position : straight_drop 95 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 118 (Gtyp (Fuint 3))) joint_update_connection_118_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_118_split : joint_update_connection_118_decl = statement_append joint_update_connection_118_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 118) (@Eref VarOrder.T (@Eid VarOrder.T 7758))) joint_update_connection_118_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_118_straight : straight_statements joint_update_connection_118_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_118_mid_safe : formal_typed_suffix_safe flat_memories 118 joint_update_connection_118_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_118_tail_safe : formal_typed_suffix_safe flat_memories 118 joint_update_connection_118_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_118_nonregister : has_register 118 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_118_output invalid old current result :
 (exists ground bits, VM.find 7758 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 118 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 95 flat_statements joint_update_connection_118_decl joint_update_connection_118_mid joint_update_connection_118_tail
 118 7758 3 ground bits invalid flat_memories old current result
 joint_update_connection_118_position joint_update_connection_118_split joint_update_connection_118_straight joint_update_connection_118_mid_safe joint_update_connection_118_tail_safe
 joint_update_connection_118_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_119_decl := match straight_drop 97 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_119_tail := match straight_drop 8788 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_119_mid := take_statements 8690 joint_update_connection_119_decl.
Lemma joint_update_connection_119_position : straight_drop 96 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 119 (Gtyp (Fuint 32))) joint_update_connection_119_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_119_split : joint_update_connection_119_decl = statement_append joint_update_connection_119_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 119) (@Eref VarOrder.T (@Eid VarOrder.T 7753))) joint_update_connection_119_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_119_straight : straight_statements joint_update_connection_119_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_119_mid_safe : formal_typed_suffix_safe flat_memories 119 joint_update_connection_119_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_119_tail_safe : formal_typed_suffix_safe flat_memories 119 joint_update_connection_119_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_119_nonregister : has_register 119 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_119_output invalid old current result :
 (exists ground bits, VM.find 7753 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 119 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 96 flat_statements joint_update_connection_119_decl joint_update_connection_119_mid joint_update_connection_119_tail
 119 7753 32 ground bits invalid flat_memories old current result
 joint_update_connection_119_position joint_update_connection_119_split joint_update_connection_119_straight joint_update_connection_119_mid_safe joint_update_connection_119_tail_safe
 joint_update_connection_119_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_121_decl := match straight_drop 99 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_121_tail := match straight_drop 8789 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_121_mid := take_statements 8689 joint_update_connection_121_decl.
Lemma joint_update_connection_121_position : straight_drop 98 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 121 (Gtyp (Fuint 32))) joint_update_connection_121_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_121_split : joint_update_connection_121_decl = statement_append joint_update_connection_121_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 121) (@Eref VarOrder.T (@Eid VarOrder.T 7751))) joint_update_connection_121_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_121_straight : straight_statements joint_update_connection_121_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_121_mid_safe : formal_typed_suffix_safe flat_memories 121 joint_update_connection_121_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_121_tail_safe : formal_typed_suffix_safe flat_memories 121 joint_update_connection_121_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_121_nonregister : has_register 121 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_121_output invalid old current result :
 (exists ground bits, VM.find 7751 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 121 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 98 flat_statements joint_update_connection_121_decl joint_update_connection_121_mid joint_update_connection_121_tail
 121 7751 32 ground bits invalid flat_memories old current result
 joint_update_connection_121_position joint_update_connection_121_split joint_update_connection_121_straight joint_update_connection_121_mid_safe joint_update_connection_121_tail_safe
 joint_update_connection_121_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_122_decl := match straight_drop 100 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_122_tail := match straight_drop 8790 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_122_mid := take_statements 8689 joint_update_connection_122_decl.
Lemma joint_update_connection_122_position : straight_drop 99 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 122 (Gtyp (Fuint 32))) joint_update_connection_122_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_122_split : joint_update_connection_122_decl = statement_append joint_update_connection_122_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 122) (@Eref VarOrder.T (@Eid VarOrder.T 7752))) joint_update_connection_122_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_122_straight : straight_statements joint_update_connection_122_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_122_mid_safe : formal_typed_suffix_safe flat_memories 122 joint_update_connection_122_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_122_tail_safe : formal_typed_suffix_safe flat_memories 122 joint_update_connection_122_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_122_nonregister : has_register 122 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_122_output invalid old current result :
 (exists ground bits, VM.find 7752 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 122 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 99 flat_statements joint_update_connection_122_decl joint_update_connection_122_mid joint_update_connection_122_tail
 122 7752 32 ground bits invalid flat_memories old current result
 joint_update_connection_122_position joint_update_connection_122_split joint_update_connection_122_straight joint_update_connection_122_mid_safe joint_update_connection_122_tail_safe
 joint_update_connection_122_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_123_decl := match straight_drop 101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_123_tail := match straight_drop 8791 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_123_mid := take_statements 8689 joint_update_connection_123_decl.
Lemma joint_update_connection_123_position : straight_drop 100 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 123 (Gtyp (Fuint 32))) joint_update_connection_123_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_123_split : joint_update_connection_123_decl = statement_append joint_update_connection_123_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 123) (@Eref VarOrder.T (@Eid VarOrder.T 7750))) joint_update_connection_123_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_123_straight : straight_statements joint_update_connection_123_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_123_mid_safe : formal_typed_suffix_safe flat_memories 123 joint_update_connection_123_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_123_tail_safe : formal_typed_suffix_safe flat_memories 123 joint_update_connection_123_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_123_nonregister : has_register 123 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_123_output invalid old current result :
 (exists ground bits, VM.find 7750 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 123 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 100 flat_statements joint_update_connection_123_decl joint_update_connection_123_mid joint_update_connection_123_tail
 123 7750 32 ground bits invalid flat_memories old current result
 joint_update_connection_123_position joint_update_connection_123_split joint_update_connection_123_straight joint_update_connection_123_mid_safe joint_update_connection_123_tail_safe
 joint_update_connection_123_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_124_decl := match straight_drop 102 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_124_tail := match straight_drop 8792 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_124_mid := take_statements 8689 joint_update_connection_124_decl.
Lemma joint_update_connection_124_position : straight_drop 101 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 124 (Gtyp (Fuint 1))) joint_update_connection_124_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_124_split : joint_update_connection_124_decl = statement_append joint_update_connection_124_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 124) (@Eref VarOrder.T (@Eid VarOrder.T 7759))) joint_update_connection_124_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_124_straight : straight_statements joint_update_connection_124_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_124_mid_safe : formal_typed_suffix_safe flat_memories 124 joint_update_connection_124_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_124_tail_safe : formal_typed_suffix_safe flat_memories 124 joint_update_connection_124_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_124_nonregister : has_register 124 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_124_output invalid old current result :
 (exists ground bits, VM.find 7759 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 124 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 101 flat_statements joint_update_connection_124_decl joint_update_connection_124_mid joint_update_connection_124_tail
 124 7759 1 ground bits invalid flat_memories old current result
 joint_update_connection_124_position joint_update_connection_124_split joint_update_connection_124_straight joint_update_connection_124_mid_safe joint_update_connection_124_tail_safe
 joint_update_connection_124_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_125_decl := match straight_drop 103 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_125_tail := match straight_drop 8793 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_125_mid := take_statements 8689 joint_update_connection_125_decl.
Lemma joint_update_connection_125_position : straight_drop 102 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 125 (Gtyp (Fuint 2))) joint_update_connection_125_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_125_split : joint_update_connection_125_decl = statement_append joint_update_connection_125_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 125) (@Eref VarOrder.T (@Eid VarOrder.T 7754))) joint_update_connection_125_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_125_straight : straight_statements joint_update_connection_125_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_125_mid_safe : formal_typed_suffix_safe flat_memories 125 joint_update_connection_125_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_125_tail_safe : formal_typed_suffix_safe flat_memories 125 joint_update_connection_125_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_125_nonregister : has_register 125 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_125_output invalid old current result :
 (exists ground bits, VM.find 7754 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 125 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 102 flat_statements joint_update_connection_125_decl joint_update_connection_125_mid joint_update_connection_125_tail
 125 7754 2 ground bits invalid flat_memories old current result
 joint_update_connection_125_position joint_update_connection_125_split joint_update_connection_125_straight joint_update_connection_125_mid_safe joint_update_connection_125_tail_safe
 joint_update_connection_125_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_126_decl := match straight_drop 104 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_126_tail := match straight_drop 8794 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_126_mid := take_statements 8689 joint_update_connection_126_decl.
Lemma joint_update_connection_126_position : straight_drop 103 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 126 (Gtyp (Fuint 3))) joint_update_connection_126_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_126_split : joint_update_connection_126_decl = statement_append joint_update_connection_126_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 126) (@Eref VarOrder.T (@Eid VarOrder.T 7755))) joint_update_connection_126_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_126_straight : straight_statements joint_update_connection_126_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_126_mid_safe : formal_typed_suffix_safe flat_memories 126 joint_update_connection_126_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_126_tail_safe : formal_typed_suffix_safe flat_memories 126 joint_update_connection_126_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_126_nonregister : has_register 126 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_126_output invalid old current result :
 (exists ground bits, VM.find 7755 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 126 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 103 flat_statements joint_update_connection_126_decl joint_update_connection_126_mid joint_update_connection_126_tail
 126 7755 3 ground bits invalid flat_memories old current result
 joint_update_connection_126_position joint_update_connection_126_split joint_update_connection_126_straight joint_update_connection_126_mid_safe joint_update_connection_126_tail_safe
 joint_update_connection_126_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_127_decl := match straight_drop 105 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_127_tail := match straight_drop 8795 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_127_mid := take_statements 8689 joint_update_connection_127_decl.
Lemma joint_update_connection_127_position : straight_drop 104 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 127 (Gtyp (Fuint 1))) joint_update_connection_127_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_127_split : joint_update_connection_127_decl = statement_append joint_update_connection_127_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 127) (@Eref VarOrder.T (@Eid VarOrder.T 7760))) joint_update_connection_127_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_127_straight : straight_statements joint_update_connection_127_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_127_mid_safe : formal_typed_suffix_safe flat_memories 127 joint_update_connection_127_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_127_tail_safe : formal_typed_suffix_safe flat_memories 127 joint_update_connection_127_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_127_nonregister : has_register 127 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_127_output invalid old current result :
 (exists ground bits, VM.find 7760 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 127 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 104 flat_statements joint_update_connection_127_decl joint_update_connection_127_mid joint_update_connection_127_tail
 127 7760 1 ground bits invalid flat_memories old current result
 joint_update_connection_127_position joint_update_connection_127_split joint_update_connection_127_straight joint_update_connection_127_mid_safe joint_update_connection_127_tail_safe
 joint_update_connection_127_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_130_decl := match straight_drop 108 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_130_tail := match straight_drop 759 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_130_mid := take_statements 650 joint_update_connection_130_decl.
Lemma joint_update_connection_130_position : straight_drop 107 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 130 (Gtyp (Fuint 32))) joint_update_connection_130_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_130_split : joint_update_connection_130_decl = statement_append joint_update_connection_130_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 130) (@Eref VarOrder.T (@Eid VarOrder.T 189))) joint_update_connection_130_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_130_straight : straight_statements joint_update_connection_130_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_130_mid_safe : formal_typed_suffix_safe flat_memories 130 joint_update_connection_130_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_130_tail_safe : formal_typed_suffix_safe flat_memories 130 joint_update_connection_130_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_130_nonregister : has_register 130 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_130_output invalid old current result :
 (exists ground bits, VM.find 189 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 130 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 107 flat_statements joint_update_connection_130_decl joint_update_connection_130_mid joint_update_connection_130_tail
 130 189 32 ground bits invalid flat_memories old current result
 joint_update_connection_130_position joint_update_connection_130_split joint_update_connection_130_straight joint_update_connection_130_mid_safe joint_update_connection_130_tail_safe
 joint_update_connection_130_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_65_decl := match straight_drop 43 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_65_tail := match straight_drop 9984 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_65_mid := take_statements 9940 joint_update_connection_65_decl.
Lemma joint_update_connection_65_position : straight_drop 42 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 65 (Gtyp (Fuint 1))) joint_update_connection_65_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_65_split : joint_update_connection_65_decl = statement_append joint_update_connection_65_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 65) (@Eref VarOrder.T (@Eid VarOrder.T 24))) joint_update_connection_65_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_65_straight : straight_statements joint_update_connection_65_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_65_mid_safe : formal_typed_suffix_safe flat_memories 65 joint_update_connection_65_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_65_tail_safe : formal_typed_suffix_safe flat_memories 65 joint_update_connection_65_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_65_nonregister : has_register 65 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_65_output invalid old current result :
 (exists ground bits, VM.find 24 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 65 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 42 flat_statements joint_update_connection_65_decl joint_update_connection_65_mid joint_update_connection_65_tail
 65 24 1 ground bits invalid flat_memories old current result
 joint_update_connection_65_position joint_update_connection_65_split joint_update_connection_65_straight joint_update_connection_65_mid_safe joint_update_connection_65_tail_safe
 joint_update_connection_65_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_66_decl := match straight_drop 44 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_66_tail := match straight_drop 9985 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_66_mid := take_statements 9940 joint_update_connection_66_decl.
Lemma joint_update_connection_66_position : straight_drop 43 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 66 (Gtyp (Fuint 1))) joint_update_connection_66_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_66_split : joint_update_connection_66_decl = statement_append joint_update_connection_66_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 66) (@Eref VarOrder.T (@Eid VarOrder.T 25))) joint_update_connection_66_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_66_straight : straight_statements joint_update_connection_66_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_66_mid_safe : formal_typed_suffix_safe flat_memories 66 joint_update_connection_66_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_66_tail_safe : formal_typed_suffix_safe flat_memories 66 joint_update_connection_66_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_66_nonregister : has_register 66 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_66_output invalid old current result :
 (exists ground bits, VM.find 25 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 66 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 43 flat_statements joint_update_connection_66_decl joint_update_connection_66_mid joint_update_connection_66_tail
 66 25 1 ground bits invalid flat_memories old current result
 joint_update_connection_66_position joint_update_connection_66_split joint_update_connection_66_straight joint_update_connection_66_mid_safe joint_update_connection_66_tail_safe
 joint_update_connection_66_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_67_decl := match straight_drop 45 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_67_tail := match straight_drop 9986 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_67_mid := take_statements 9940 joint_update_connection_67_decl.
Lemma joint_update_connection_67_position : straight_drop 44 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 67 (Gtyp (Fuint 32))) joint_update_connection_67_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_67_split : joint_update_connection_67_decl = statement_append joint_update_connection_67_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 67) (@Eref VarOrder.T (@Eid VarOrder.T 26))) joint_update_connection_67_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_67_straight : straight_statements joint_update_connection_67_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_67_mid_safe : formal_typed_suffix_safe flat_memories 67 joint_update_connection_67_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_67_tail_safe : formal_typed_suffix_safe flat_memories 67 joint_update_connection_67_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_67_nonregister : has_register 67 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_67_output invalid old current result :
 (exists ground bits, VM.find 26 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 67 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 44 flat_statements joint_update_connection_67_decl joint_update_connection_67_mid joint_update_connection_67_tail
 67 26 32 ground bits invalid flat_memories old current result
 joint_update_connection_67_position joint_update_connection_67_split joint_update_connection_67_straight joint_update_connection_67_mid_safe joint_update_connection_67_tail_safe
 joint_update_connection_67_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_75_decl := match straight_drop 53 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_75_tail := match straight_drop 9988 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_75_mid := take_statements 9934 joint_update_connection_75_decl.
Lemma joint_update_connection_75_position : straight_drop 52 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 75 (Gtyp (Fuint 32))) joint_update_connection_75_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_75_split : joint_update_connection_75_decl = statement_append joint_update_connection_75_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 75) (@Eref VarOrder.T (@Eid VarOrder.T 34))) joint_update_connection_75_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_75_straight : straight_statements joint_update_connection_75_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_75_mid_safe : formal_typed_suffix_safe flat_memories 75 joint_update_connection_75_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_75_tail_safe : formal_typed_suffix_safe flat_memories 75 joint_update_connection_75_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_75_nonregister : has_register 75 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_75_output invalid old current result :
 (exists ground bits, VM.find 34 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 75 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 52 flat_statements joint_update_connection_75_decl joint_update_connection_75_mid joint_update_connection_75_tail
 75 34 32 ground bits invalid flat_memories old current result
 joint_update_connection_75_position joint_update_connection_75_split joint_update_connection_75_straight joint_update_connection_75_mid_safe joint_update_connection_75_tail_safe
 joint_update_connection_75_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_82_decl := match straight_drop 60 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_82_tail := match straight_drop 9990 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_82_mid := take_statements 9929 joint_update_connection_82_decl.
Lemma joint_update_connection_82_position : straight_drop 59 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 82 (Gtyp (Fuint 32))) joint_update_connection_82_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_82_split : joint_update_connection_82_decl = statement_append joint_update_connection_82_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 82) (@Eref VarOrder.T (@Eid VarOrder.T 41))) joint_update_connection_82_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_82_straight : straight_statements joint_update_connection_82_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_82_mid_safe : formal_typed_suffix_safe flat_memories 82 joint_update_connection_82_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_82_tail_safe : formal_typed_suffix_safe flat_memories 82 joint_update_connection_82_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_82_nonregister : has_register 82 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_82_output invalid old current result :
 (exists ground bits, VM.find 41 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 82 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 59 flat_statements joint_update_connection_82_decl joint_update_connection_82_mid joint_update_connection_82_tail
 82 41 32 ground bits invalid flat_memories old current result
 joint_update_connection_82_position joint_update_connection_82_split joint_update_connection_82_straight joint_update_connection_82_mid_safe joint_update_connection_82_tail_safe
 joint_update_connection_82_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_785_decl := match straight_drop 795 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_785_tail := match straight_drop 8803 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_785_mid := take_statements 8007 joint_update_connection_785_decl.
Lemma joint_update_connection_785_position : straight_drop 794 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 785 (Gtyp (Fuint 5))) joint_update_connection_785_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_785_split : joint_update_connection_785_decl = statement_append joint_update_connection_785_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 785) (@Eref VarOrder.T (@Eid VarOrder.T 7805))) joint_update_connection_785_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_785_straight : straight_statements joint_update_connection_785_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_785_mid_safe : formal_typed_suffix_safe flat_memories 785 joint_update_connection_785_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_785_tail_safe : formal_typed_suffix_safe flat_memories 785 joint_update_connection_785_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_785_nonregister : has_register 785 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_785_output invalid old current result :
 (exists ground bits, VM.find 7805 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 785 result = Some (Gval (Fuint 5) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 794 flat_statements joint_update_connection_785_decl joint_update_connection_785_mid joint_update_connection_785_tail
 785 7805 5 ground bits invalid flat_memories old current result
 joint_update_connection_785_position joint_update_connection_785_split joint_update_connection_785_straight joint_update_connection_785_mid_safe joint_update_connection_785_tail_safe
 joint_update_connection_785_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_116_decl := match straight_drop 94 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_116_tail := match straight_drop 8785 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_116_mid := take_statements 8690 joint_update_connection_116_decl.
Lemma joint_update_connection_116_position : straight_drop 93 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 116 (Gtyp (Fuint 1))) joint_update_connection_116_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_116_split : joint_update_connection_116_decl = statement_append joint_update_connection_116_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 116) (@Eref VarOrder.T (@Eid VarOrder.T 65))) joint_update_connection_116_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_116_straight : straight_statements joint_update_connection_116_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_116_mid_safe : formal_typed_suffix_safe flat_memories 116 joint_update_connection_116_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_116_tail_safe : formal_typed_suffix_safe flat_memories 116 joint_update_connection_116_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_116_nonregister : has_register 116 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_116_output invalid old current result :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 116 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 93 flat_statements joint_update_connection_116_decl joint_update_connection_116_mid joint_update_connection_116_tail
 116 65 1 ground bits invalid flat_memories old current result
 joint_update_connection_116_position joint_update_connection_116_split joint_update_connection_116_straight joint_update_connection_116_mid_safe joint_update_connection_116_tail_safe
 joint_update_connection_116_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_131_decl := match straight_drop 109 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_131_tail := match straight_drop 8796 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_131_mid := take_statements 8686 joint_update_connection_131_decl.
Lemma joint_update_connection_131_position : straight_drop 108 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 131 (Gtyp (Fuint 1))) joint_update_connection_131_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_131_split : joint_update_connection_131_decl = statement_append joint_update_connection_131_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 131) (@Eref VarOrder.T (@Eid VarOrder.T 66))) joint_update_connection_131_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_131_straight : straight_statements joint_update_connection_131_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_131_mid_safe : formal_typed_suffix_safe flat_memories 131 joint_update_connection_131_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_131_tail_safe : formal_typed_suffix_safe flat_memories 131 joint_update_connection_131_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_131_nonregister : has_register 131 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_131_output invalid old current result :
 (exists ground bits, VM.find 66 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 131 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 108 flat_statements joint_update_connection_131_decl joint_update_connection_131_mid joint_update_connection_131_tail
 131 66 1 ground bits invalid flat_memories old current result
 joint_update_connection_131_position joint_update_connection_131_split joint_update_connection_131_straight joint_update_connection_131_mid_safe joint_update_connection_131_tail_safe
 joint_update_connection_131_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_132_decl := match straight_drop 110 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_132_tail := match straight_drop 8797 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_132_mid := take_statements 8686 joint_update_connection_132_decl.
Lemma joint_update_connection_132_position : straight_drop 109 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 132 (Gtyp (Fuint 32))) joint_update_connection_132_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_132_split : joint_update_connection_132_decl = statement_append joint_update_connection_132_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 132) (@Eref VarOrder.T (@Eid VarOrder.T 67))) joint_update_connection_132_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_132_straight : straight_statements joint_update_connection_132_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_132_mid_safe : formal_typed_suffix_safe flat_memories 132 joint_update_connection_132_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_132_tail_safe : formal_typed_suffix_safe flat_memories 132 joint_update_connection_132_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_132_nonregister : has_register 132 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_132_output invalid old current result :
 (exists ground bits, VM.find 67 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 132 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 109 flat_statements joint_update_connection_132_decl joint_update_connection_132_mid joint_update_connection_132_tail
 132 67 32 ground bits invalid flat_memories old current result
 joint_update_connection_132_position joint_update_connection_132_split joint_update_connection_132_straight joint_update_connection_132_mid_safe joint_update_connection_132_tail_safe
 joint_update_connection_132_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_779_decl := match straight_drop 789 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_779_tail := match straight_drop 8799 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_779_mid := take_statements 8009 joint_update_connection_779_decl.
Lemma joint_update_connection_779_position : straight_drop 788 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 779 (Gtyp (Fuint 1))) joint_update_connection_779_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_779_split : joint_update_connection_779_decl = statement_append joint_update_connection_779_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 779) (@Eref VarOrder.T (@Eid VarOrder.T 65))) joint_update_connection_779_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_779_straight : straight_statements joint_update_connection_779_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_779_mid_safe : formal_typed_suffix_safe flat_memories 779 joint_update_connection_779_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_779_tail_safe : formal_typed_suffix_safe flat_memories 779 joint_update_connection_779_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_779_nonregister : has_register 779 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_779_output invalid old current result :
 (exists ground bits, VM.find 65 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 779 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 788 flat_statements joint_update_connection_779_decl joint_update_connection_779_mid joint_update_connection_779_tail
 779 65 1 ground bits invalid flat_memories old current result
 joint_update_connection_779_position joint_update_connection_779_split joint_update_connection_779_straight joint_update_connection_779_mid_safe joint_update_connection_779_tail_safe
 joint_update_connection_779_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_787_decl := match straight_drop 797 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_787_tail := match straight_drop 8805 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_787_mid := take_statements 8007 joint_update_connection_787_decl.
Lemma joint_update_connection_787_position : straight_drop 796 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 787 (Gtyp (Fuint 32))) joint_update_connection_787_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_787_split : joint_update_connection_787_decl = statement_append joint_update_connection_787_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 787) (@Eref VarOrder.T (@Eid VarOrder.T 8090))) joint_update_connection_787_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_787_straight : straight_statements joint_update_connection_787_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_787_mid_safe : formal_typed_suffix_safe flat_memories 787 joint_update_connection_787_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_787_tail_safe : formal_typed_suffix_safe flat_memories 787 joint_update_connection_787_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_787_nonregister : has_register 787 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_787_output invalid old current result :
 (exists ground bits, VM.find 8090 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 787 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 796 flat_statements joint_update_connection_787_decl joint_update_connection_787_mid joint_update_connection_787_tail
 787 8090 32 ground bits invalid flat_memories old current result
 joint_update_connection_787_position joint_update_connection_787_split joint_update_connection_787_straight joint_update_connection_787_mid_safe joint_update_connection_787_tail_safe
 joint_update_connection_787_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_788_decl := match straight_drop 798 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_788_tail := match straight_drop 8806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_788_mid := take_statements 8007 joint_update_connection_788_decl.
Lemma joint_update_connection_788_position : straight_drop 797 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 788 (Gtyp (Fuint 32))) joint_update_connection_788_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_788_split : joint_update_connection_788_decl = statement_append joint_update_connection_788_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 788) (@Eref VarOrder.T (@Eid VarOrder.T 8092))) joint_update_connection_788_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_788_straight : straight_statements joint_update_connection_788_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_788_mid_safe : formal_typed_suffix_safe flat_memories 788 joint_update_connection_788_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_788_tail_safe : formal_typed_suffix_safe flat_memories 788 joint_update_connection_788_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_788_nonregister : has_register 788 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_788_output invalid old current result :
 (exists ground bits, VM.find 8092 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 788 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 797 flat_statements joint_update_connection_788_decl joint_update_connection_788_mid joint_update_connection_788_tail
 788 8092 32 ground bits invalid flat_memories old current result
 joint_update_connection_788_position joint_update_connection_788_split joint_update_connection_788_straight joint_update_connection_788_mid_safe joint_update_connection_788_tail_safe
 joint_update_connection_788_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_789_decl := match straight_drop 799 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_789_tail := match straight_drop 8807 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_789_mid := take_statements 8007 joint_update_connection_789_decl.
Lemma joint_update_connection_789_position : straight_drop 798 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 789 (Gtyp (Fuint 32))) joint_update_connection_789_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_789_split : joint_update_connection_789_decl = statement_append joint_update_connection_789_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 789) (@Eref VarOrder.T (@Eid VarOrder.T 8094))) joint_update_connection_789_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_789_straight : straight_statements joint_update_connection_789_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_789_mid_safe : formal_typed_suffix_safe flat_memories 789 joint_update_connection_789_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_789_tail_safe : formal_typed_suffix_safe flat_memories 789 joint_update_connection_789_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_789_nonregister : has_register 789 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_789_output invalid old current result :
 (exists ground bits, VM.find 8094 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 789 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 798 flat_statements joint_update_connection_789_decl joint_update_connection_789_mid joint_update_connection_789_tail
 789 8094 32 ground bits invalid flat_memories old current result
 joint_update_connection_789_position joint_update_connection_789_split joint_update_connection_789_straight joint_update_connection_789_mid_safe joint_update_connection_789_tail_safe
 joint_update_connection_789_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_790_decl := match straight_drop 800 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_790_tail := match straight_drop 8808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_790_mid := take_statements 8007 joint_update_connection_790_decl.
Lemma joint_update_connection_790_position : straight_drop 799 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 790 (Gtyp (Fuint 32))) joint_update_connection_790_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_790_split : joint_update_connection_790_decl = statement_append joint_update_connection_790_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 790) (@Eref VarOrder.T (@Eid VarOrder.T 8096))) joint_update_connection_790_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_790_straight : straight_statements joint_update_connection_790_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_790_mid_safe : formal_typed_suffix_safe flat_memories 790 joint_update_connection_790_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_790_tail_safe : formal_typed_suffix_safe flat_memories 790 joint_update_connection_790_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_790_nonregister : has_register 790 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_790_output invalid old current result :
 (exists ground bits, VM.find 8096 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 790 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 799 flat_statements joint_update_connection_790_decl joint_update_connection_790_mid joint_update_connection_790_tail
 790 8096 32 ground bits invalid flat_memories old current result
 joint_update_connection_790_position joint_update_connection_790_split joint_update_connection_790_straight joint_update_connection_790_mid_safe joint_update_connection_790_tail_safe
 joint_update_connection_790_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_791_decl := match straight_drop 801 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_791_tail := match straight_drop 8809 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_791_mid := take_statements 8007 joint_update_connection_791_decl.
Lemma joint_update_connection_791_position : straight_drop 800 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 791 (Gtyp (Fuint 32))) joint_update_connection_791_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_791_split : joint_update_connection_791_decl = statement_append joint_update_connection_791_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 791) (@Eref VarOrder.T (@Eid VarOrder.T 8098))) joint_update_connection_791_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_791_straight : straight_statements joint_update_connection_791_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_791_mid_safe : formal_typed_suffix_safe flat_memories 791 joint_update_connection_791_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_791_tail_safe : formal_typed_suffix_safe flat_memories 791 joint_update_connection_791_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_791_nonregister : has_register 791 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_791_output invalid old current result :
 (exists ground bits, VM.find 8098 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 791 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 800 flat_statements joint_update_connection_791_decl joint_update_connection_791_mid joint_update_connection_791_tail
 791 8098 32 ground bits invalid flat_memories old current result
 joint_update_connection_791_position joint_update_connection_791_split joint_update_connection_791_straight joint_update_connection_791_mid_safe joint_update_connection_791_tail_safe
 joint_update_connection_791_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_792_decl := match straight_drop 802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_792_tail := match straight_drop 8810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_792_mid := take_statements 8007 joint_update_connection_792_decl.
Lemma joint_update_connection_792_position : straight_drop 801 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 792 (Gtyp (Fuint 32))) joint_update_connection_792_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_792_split : joint_update_connection_792_decl = statement_append joint_update_connection_792_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 792) (@Eref VarOrder.T (@Eid VarOrder.T 8100))) joint_update_connection_792_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_792_straight : straight_statements joint_update_connection_792_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_792_mid_safe : formal_typed_suffix_safe flat_memories 792 joint_update_connection_792_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_792_tail_safe : formal_typed_suffix_safe flat_memories 792 joint_update_connection_792_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_792_nonregister : has_register 792 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_792_output invalid old current result :
 (exists ground bits, VM.find 8100 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 792 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 801 flat_statements joint_update_connection_792_decl joint_update_connection_792_mid joint_update_connection_792_tail
 792 8100 32 ground bits invalid flat_memories old current result
 joint_update_connection_792_position joint_update_connection_792_split joint_update_connection_792_straight joint_update_connection_792_mid_safe joint_update_connection_792_tail_safe
 joint_update_connection_792_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_793_decl := match straight_drop 803 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_793_tail := match straight_drop 8811 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_793_mid := take_statements 8007 joint_update_connection_793_decl.
Lemma joint_update_connection_793_position : straight_drop 802 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 793 (Gtyp (Fuint 32))) joint_update_connection_793_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_793_split : joint_update_connection_793_decl = statement_append joint_update_connection_793_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 793) (@Eref VarOrder.T (@Eid VarOrder.T 8102))) joint_update_connection_793_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_793_straight : straight_statements joint_update_connection_793_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_793_mid_safe : formal_typed_suffix_safe flat_memories 793 joint_update_connection_793_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_793_tail_safe : formal_typed_suffix_safe flat_memories 793 joint_update_connection_793_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_793_nonregister : has_register 793 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_793_output invalid old current result :
 (exists ground bits, VM.find 8102 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 793 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 802 flat_statements joint_update_connection_793_decl joint_update_connection_793_mid joint_update_connection_793_tail
 793 8102 32 ground bits invalid flat_memories old current result
 joint_update_connection_793_position joint_update_connection_793_split joint_update_connection_793_straight joint_update_connection_793_mid_safe joint_update_connection_793_tail_safe
 joint_update_connection_793_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_794_decl := match straight_drop 804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_794_tail := match straight_drop 8812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_794_mid := take_statements 8007 joint_update_connection_794_decl.
Lemma joint_update_connection_794_position : straight_drop 803 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 794 (Gtyp (Fuint 32))) joint_update_connection_794_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_794_split : joint_update_connection_794_decl = statement_append joint_update_connection_794_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 794) (@Eref VarOrder.T (@Eid VarOrder.T 8104))) joint_update_connection_794_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_794_straight : straight_statements joint_update_connection_794_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_794_mid_safe : formal_typed_suffix_safe flat_memories 794 joint_update_connection_794_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_794_tail_safe : formal_typed_suffix_safe flat_memories 794 joint_update_connection_794_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_794_nonregister : has_register 794 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_794_output invalid old current result :
 (exists ground bits, VM.find 8104 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 794 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 803 flat_statements joint_update_connection_794_decl joint_update_connection_794_mid joint_update_connection_794_tail
 794 8104 32 ground bits invalid flat_memories old current result
 joint_update_connection_794_position joint_update_connection_794_split joint_update_connection_794_straight joint_update_connection_794_mid_safe joint_update_connection_794_tail_safe
 joint_update_connection_794_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_795_decl := match straight_drop 805 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_795_tail := match straight_drop 8813 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_795_mid := take_statements 8007 joint_update_connection_795_decl.
Lemma joint_update_connection_795_position : straight_drop 804 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 795 (Gtyp (Fuint 32))) joint_update_connection_795_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_795_split : joint_update_connection_795_decl = statement_append joint_update_connection_795_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 795) (@Eref VarOrder.T (@Eid VarOrder.T 8106))) joint_update_connection_795_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_795_straight : straight_statements joint_update_connection_795_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_795_mid_safe : formal_typed_suffix_safe flat_memories 795 joint_update_connection_795_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_795_tail_safe : formal_typed_suffix_safe flat_memories 795 joint_update_connection_795_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_795_nonregister : has_register 795 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_795_output invalid old current result :
 (exists ground bits, VM.find 8106 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 795 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 804 flat_statements joint_update_connection_795_decl joint_update_connection_795_mid joint_update_connection_795_tail
 795 8106 32 ground bits invalid flat_memories old current result
 joint_update_connection_795_position joint_update_connection_795_split joint_update_connection_795_straight joint_update_connection_795_mid_safe joint_update_connection_795_tail_safe
 joint_update_connection_795_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_796_decl := match straight_drop 806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_796_tail := match straight_drop 8814 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_796_mid := take_statements 8007 joint_update_connection_796_decl.
Lemma joint_update_connection_796_position : straight_drop 805 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 796 (Gtyp (Fuint 32))) joint_update_connection_796_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_796_split : joint_update_connection_796_decl = statement_append joint_update_connection_796_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 796) (@Eref VarOrder.T (@Eid VarOrder.T 8108))) joint_update_connection_796_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_796_straight : straight_statements joint_update_connection_796_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_796_mid_safe : formal_typed_suffix_safe flat_memories 796 joint_update_connection_796_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_796_tail_safe : formal_typed_suffix_safe flat_memories 796 joint_update_connection_796_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_796_nonregister : has_register 796 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_796_output invalid old current result :
 (exists ground bits, VM.find 8108 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 796 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 805 flat_statements joint_update_connection_796_decl joint_update_connection_796_mid joint_update_connection_796_tail
 796 8108 32 ground bits invalid flat_memories old current result
 joint_update_connection_796_position joint_update_connection_796_split joint_update_connection_796_straight joint_update_connection_796_mid_safe joint_update_connection_796_tail_safe
 joint_update_connection_796_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_797_decl := match straight_drop 807 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_797_tail := match straight_drop 8815 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_797_mid := take_statements 8007 joint_update_connection_797_decl.
Lemma joint_update_connection_797_position : straight_drop 806 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 797 (Gtyp (Fuint 32))) joint_update_connection_797_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_797_split : joint_update_connection_797_decl = statement_append joint_update_connection_797_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 797) (@Eref VarOrder.T (@Eid VarOrder.T 8110))) joint_update_connection_797_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_797_straight : straight_statements joint_update_connection_797_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_797_mid_safe : formal_typed_suffix_safe flat_memories 797 joint_update_connection_797_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_797_tail_safe : formal_typed_suffix_safe flat_memories 797 joint_update_connection_797_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_797_nonregister : has_register 797 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_797_output invalid old current result :
 (exists ground bits, VM.find 8110 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 797 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 806 flat_statements joint_update_connection_797_decl joint_update_connection_797_mid joint_update_connection_797_tail
 797 8110 32 ground bits invalid flat_memories old current result
 joint_update_connection_797_position joint_update_connection_797_split joint_update_connection_797_straight joint_update_connection_797_mid_safe joint_update_connection_797_tail_safe
 joint_update_connection_797_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_798_decl := match straight_drop 808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_798_tail := match straight_drop 8816 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_798_mid := take_statements 8007 joint_update_connection_798_decl.
Lemma joint_update_connection_798_position : straight_drop 807 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 798 (Gtyp (Fuint 32))) joint_update_connection_798_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_798_split : joint_update_connection_798_decl = statement_append joint_update_connection_798_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 798) (@Eref VarOrder.T (@Eid VarOrder.T 8112))) joint_update_connection_798_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_798_straight : straight_statements joint_update_connection_798_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_798_mid_safe : formal_typed_suffix_safe flat_memories 798 joint_update_connection_798_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_798_tail_safe : formal_typed_suffix_safe flat_memories 798 joint_update_connection_798_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_798_nonregister : has_register 798 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_798_output invalid old current result :
 (exists ground bits, VM.find 8112 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 798 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 807 flat_statements joint_update_connection_798_decl joint_update_connection_798_mid joint_update_connection_798_tail
 798 8112 32 ground bits invalid flat_memories old current result
 joint_update_connection_798_position joint_update_connection_798_split joint_update_connection_798_straight joint_update_connection_798_mid_safe joint_update_connection_798_tail_safe
 joint_update_connection_798_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_799_decl := match straight_drop 809 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_799_tail := match straight_drop 8817 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_799_mid := take_statements 8007 joint_update_connection_799_decl.
Lemma joint_update_connection_799_position : straight_drop 808 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 799 (Gtyp (Fuint 32))) joint_update_connection_799_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_799_split : joint_update_connection_799_decl = statement_append joint_update_connection_799_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 799) (@Eref VarOrder.T (@Eid VarOrder.T 8114))) joint_update_connection_799_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_799_straight : straight_statements joint_update_connection_799_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_799_mid_safe : formal_typed_suffix_safe flat_memories 799 joint_update_connection_799_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_799_tail_safe : formal_typed_suffix_safe flat_memories 799 joint_update_connection_799_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_799_nonregister : has_register 799 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_799_output invalid old current result :
 (exists ground bits, VM.find 8114 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 799 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 808 flat_statements joint_update_connection_799_decl joint_update_connection_799_mid joint_update_connection_799_tail
 799 8114 32 ground bits invalid flat_memories old current result
 joint_update_connection_799_position joint_update_connection_799_split joint_update_connection_799_straight joint_update_connection_799_mid_safe joint_update_connection_799_tail_safe
 joint_update_connection_799_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_800_decl := match straight_drop 810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_800_tail := match straight_drop 8818 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_800_mid := take_statements 8007 joint_update_connection_800_decl.
Lemma joint_update_connection_800_position : straight_drop 809 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 800 (Gtyp (Fuint 32))) joint_update_connection_800_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_800_split : joint_update_connection_800_decl = statement_append joint_update_connection_800_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 800) (@Eref VarOrder.T (@Eid VarOrder.T 8116))) joint_update_connection_800_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_800_straight : straight_statements joint_update_connection_800_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_800_mid_safe : formal_typed_suffix_safe flat_memories 800 joint_update_connection_800_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_800_tail_safe : formal_typed_suffix_safe flat_memories 800 joint_update_connection_800_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_800_nonregister : has_register 800 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_800_output invalid old current result :
 (exists ground bits, VM.find 8116 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 800 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 809 flat_statements joint_update_connection_800_decl joint_update_connection_800_mid joint_update_connection_800_tail
 800 8116 32 ground bits invalid flat_memories old current result
 joint_update_connection_800_position joint_update_connection_800_split joint_update_connection_800_straight joint_update_connection_800_mid_safe joint_update_connection_800_tail_safe
 joint_update_connection_800_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_801_decl := match straight_drop 811 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_801_tail := match straight_drop 8819 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_801_mid := take_statements 8007 joint_update_connection_801_decl.
Lemma joint_update_connection_801_position : straight_drop 810 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 801 (Gtyp (Fuint 32))) joint_update_connection_801_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_801_split : joint_update_connection_801_decl = statement_append joint_update_connection_801_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 801) (@Eref VarOrder.T (@Eid VarOrder.T 8118))) joint_update_connection_801_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_801_straight : straight_statements joint_update_connection_801_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_801_mid_safe : formal_typed_suffix_safe flat_memories 801 joint_update_connection_801_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_801_tail_safe : formal_typed_suffix_safe flat_memories 801 joint_update_connection_801_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_801_nonregister : has_register 801 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_801_output invalid old current result :
 (exists ground bits, VM.find 8118 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 801 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 810 flat_statements joint_update_connection_801_decl joint_update_connection_801_mid joint_update_connection_801_tail
 801 8118 32 ground bits invalid flat_memories old current result
 joint_update_connection_801_position joint_update_connection_801_split joint_update_connection_801_straight joint_update_connection_801_mid_safe joint_update_connection_801_tail_safe
 joint_update_connection_801_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_802_decl := match straight_drop 812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_802_tail := match straight_drop 8820 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_802_mid := take_statements 8007 joint_update_connection_802_decl.
Lemma joint_update_connection_802_position : straight_drop 811 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 802 (Gtyp (Fuint 32))) joint_update_connection_802_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_802_split : joint_update_connection_802_decl = statement_append joint_update_connection_802_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 802) (@Eref VarOrder.T (@Eid VarOrder.T 8120))) joint_update_connection_802_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_802_straight : straight_statements joint_update_connection_802_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_802_mid_safe : formal_typed_suffix_safe flat_memories 802 joint_update_connection_802_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_802_tail_safe : formal_typed_suffix_safe flat_memories 802 joint_update_connection_802_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_802_nonregister : has_register 802 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_802_output invalid old current result :
 (exists ground bits, VM.find 8120 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 802 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 811 flat_statements joint_update_connection_802_decl joint_update_connection_802_mid joint_update_connection_802_tail
 802 8120 32 ground bits invalid flat_memories old current result
 joint_update_connection_802_position joint_update_connection_802_split joint_update_connection_802_straight joint_update_connection_802_mid_safe joint_update_connection_802_tail_safe
 joint_update_connection_802_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_803_decl := match straight_drop 813 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_803_tail := match straight_drop 8821 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_803_mid := take_statements 8007 joint_update_connection_803_decl.
Lemma joint_update_connection_803_position : straight_drop 812 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 803 (Gtyp (Fuint 32))) joint_update_connection_803_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_803_split : joint_update_connection_803_decl = statement_append joint_update_connection_803_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 803) (@Eref VarOrder.T (@Eid VarOrder.T 8122))) joint_update_connection_803_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_803_straight : straight_statements joint_update_connection_803_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_803_mid_safe : formal_typed_suffix_safe flat_memories 803 joint_update_connection_803_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_803_tail_safe : formal_typed_suffix_safe flat_memories 803 joint_update_connection_803_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_803_nonregister : has_register 803 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_803_output invalid old current result :
 (exists ground bits, VM.find 8122 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 803 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 812 flat_statements joint_update_connection_803_decl joint_update_connection_803_mid joint_update_connection_803_tail
 803 8122 32 ground bits invalid flat_memories old current result
 joint_update_connection_803_position joint_update_connection_803_split joint_update_connection_803_straight joint_update_connection_803_mid_safe joint_update_connection_803_tail_safe
 joint_update_connection_803_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_804_decl := match straight_drop 814 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_804_tail := match straight_drop 8822 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_804_mid := take_statements 8007 joint_update_connection_804_decl.
Lemma joint_update_connection_804_position : straight_drop 813 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 804 (Gtyp (Fuint 32))) joint_update_connection_804_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_804_split : joint_update_connection_804_decl = statement_append joint_update_connection_804_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 804) (@Eref VarOrder.T (@Eid VarOrder.T 8124))) joint_update_connection_804_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_804_straight : straight_statements joint_update_connection_804_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_804_mid_safe : formal_typed_suffix_safe flat_memories 804 joint_update_connection_804_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_804_tail_safe : formal_typed_suffix_safe flat_memories 804 joint_update_connection_804_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_804_nonregister : has_register 804 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_804_output invalid old current result :
 (exists ground bits, VM.find 8124 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 804 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 813 flat_statements joint_update_connection_804_decl joint_update_connection_804_mid joint_update_connection_804_tail
 804 8124 32 ground bits invalid flat_memories old current result
 joint_update_connection_804_position joint_update_connection_804_split joint_update_connection_804_straight joint_update_connection_804_mid_safe joint_update_connection_804_tail_safe
 joint_update_connection_804_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_805_decl := match straight_drop 815 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_805_tail := match straight_drop 8823 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_805_mid := take_statements 8007 joint_update_connection_805_decl.
Lemma joint_update_connection_805_position : straight_drop 814 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 805 (Gtyp (Fuint 32))) joint_update_connection_805_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_805_split : joint_update_connection_805_decl = statement_append joint_update_connection_805_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 805) (@Eref VarOrder.T (@Eid VarOrder.T 8126))) joint_update_connection_805_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_805_straight : straight_statements joint_update_connection_805_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_805_mid_safe : formal_typed_suffix_safe flat_memories 805 joint_update_connection_805_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_805_tail_safe : formal_typed_suffix_safe flat_memories 805 joint_update_connection_805_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_805_nonregister : has_register 805 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_805_output invalid old current result :
 (exists ground bits, VM.find 8126 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 805 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 814 flat_statements joint_update_connection_805_decl joint_update_connection_805_mid joint_update_connection_805_tail
 805 8126 32 ground bits invalid flat_memories old current result
 joint_update_connection_805_position joint_update_connection_805_split joint_update_connection_805_straight joint_update_connection_805_mid_safe joint_update_connection_805_tail_safe
 joint_update_connection_805_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_806_decl := match straight_drop 816 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_806_tail := match straight_drop 8824 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_806_mid := take_statements 8007 joint_update_connection_806_decl.
Lemma joint_update_connection_806_position : straight_drop 815 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 806 (Gtyp (Fuint 32))) joint_update_connection_806_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_806_split : joint_update_connection_806_decl = statement_append joint_update_connection_806_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 806) (@Eref VarOrder.T (@Eid VarOrder.T 8128))) joint_update_connection_806_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_806_straight : straight_statements joint_update_connection_806_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_806_mid_safe : formal_typed_suffix_safe flat_memories 806 joint_update_connection_806_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_806_tail_safe : formal_typed_suffix_safe flat_memories 806 joint_update_connection_806_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_806_nonregister : has_register 806 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_806_output invalid old current result :
 (exists ground bits, VM.find 8128 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 806 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 815 flat_statements joint_update_connection_806_decl joint_update_connection_806_mid joint_update_connection_806_tail
 806 8128 32 ground bits invalid flat_memories old current result
 joint_update_connection_806_position joint_update_connection_806_split joint_update_connection_806_straight joint_update_connection_806_mid_safe joint_update_connection_806_tail_safe
 joint_update_connection_806_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_807_decl := match straight_drop 817 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_807_tail := match straight_drop 8825 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_807_mid := take_statements 8007 joint_update_connection_807_decl.
Lemma joint_update_connection_807_position : straight_drop 816 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 807 (Gtyp (Fuint 32))) joint_update_connection_807_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_807_split : joint_update_connection_807_decl = statement_append joint_update_connection_807_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 807) (@Eref VarOrder.T (@Eid VarOrder.T 8130))) joint_update_connection_807_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_807_straight : straight_statements joint_update_connection_807_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_807_mid_safe : formal_typed_suffix_safe flat_memories 807 joint_update_connection_807_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_807_tail_safe : formal_typed_suffix_safe flat_memories 807 joint_update_connection_807_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_807_nonregister : has_register 807 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_807_output invalid old current result :
 (exists ground bits, VM.find 8130 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 807 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 816 flat_statements joint_update_connection_807_decl joint_update_connection_807_mid joint_update_connection_807_tail
 807 8130 32 ground bits invalid flat_memories old current result
 joint_update_connection_807_position joint_update_connection_807_split joint_update_connection_807_straight joint_update_connection_807_mid_safe joint_update_connection_807_tail_safe
 joint_update_connection_807_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_808_decl := match straight_drop 818 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_808_tail := match straight_drop 8826 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_808_mid := take_statements 8007 joint_update_connection_808_decl.
Lemma joint_update_connection_808_position : straight_drop 817 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 808 (Gtyp (Fuint 32))) joint_update_connection_808_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_808_split : joint_update_connection_808_decl = statement_append joint_update_connection_808_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 808) (@Eref VarOrder.T (@Eid VarOrder.T 8132))) joint_update_connection_808_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_808_straight : straight_statements joint_update_connection_808_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_808_mid_safe : formal_typed_suffix_safe flat_memories 808 joint_update_connection_808_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_808_tail_safe : formal_typed_suffix_safe flat_memories 808 joint_update_connection_808_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_808_nonregister : has_register 808 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_808_output invalid old current result :
 (exists ground bits, VM.find 8132 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 808 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 817 flat_statements joint_update_connection_808_decl joint_update_connection_808_mid joint_update_connection_808_tail
 808 8132 32 ground bits invalid flat_memories old current result
 joint_update_connection_808_position joint_update_connection_808_split joint_update_connection_808_straight joint_update_connection_808_mid_safe joint_update_connection_808_tail_safe
 joint_update_connection_808_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_809_decl := match straight_drop 819 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_809_tail := match straight_drop 8827 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_809_mid := take_statements 8007 joint_update_connection_809_decl.
Lemma joint_update_connection_809_position : straight_drop 818 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 809 (Gtyp (Fuint 32))) joint_update_connection_809_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_809_split : joint_update_connection_809_decl = statement_append joint_update_connection_809_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 809) (@Eref VarOrder.T (@Eid VarOrder.T 8134))) joint_update_connection_809_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_809_straight : straight_statements joint_update_connection_809_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_809_mid_safe : formal_typed_suffix_safe flat_memories 809 joint_update_connection_809_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_809_tail_safe : formal_typed_suffix_safe flat_memories 809 joint_update_connection_809_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_809_nonregister : has_register 809 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_809_output invalid old current result :
 (exists ground bits, VM.find 8134 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 809 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 818 flat_statements joint_update_connection_809_decl joint_update_connection_809_mid joint_update_connection_809_tail
 809 8134 32 ground bits invalid flat_memories old current result
 joint_update_connection_809_position joint_update_connection_809_split joint_update_connection_809_straight joint_update_connection_809_mid_safe joint_update_connection_809_tail_safe
 joint_update_connection_809_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_810_decl := match straight_drop 820 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_810_tail := match straight_drop 8828 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_810_mid := take_statements 8007 joint_update_connection_810_decl.
Lemma joint_update_connection_810_position : straight_drop 819 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 810 (Gtyp (Fuint 32))) joint_update_connection_810_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_810_split : joint_update_connection_810_decl = statement_append joint_update_connection_810_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 810) (@Eref VarOrder.T (@Eid VarOrder.T 8136))) joint_update_connection_810_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_810_straight : straight_statements joint_update_connection_810_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_810_mid_safe : formal_typed_suffix_safe flat_memories 810 joint_update_connection_810_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_810_tail_safe : formal_typed_suffix_safe flat_memories 810 joint_update_connection_810_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_810_nonregister : has_register 810 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_810_output invalid old current result :
 (exists ground bits, VM.find 8136 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 810 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 819 flat_statements joint_update_connection_810_decl joint_update_connection_810_mid joint_update_connection_810_tail
 810 8136 32 ground bits invalid flat_memories old current result
 joint_update_connection_810_position joint_update_connection_810_split joint_update_connection_810_straight joint_update_connection_810_mid_safe joint_update_connection_810_tail_safe
 joint_update_connection_810_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_811_decl := match straight_drop 821 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_811_tail := match straight_drop 8829 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_811_mid := take_statements 8007 joint_update_connection_811_decl.
Lemma joint_update_connection_811_position : straight_drop 820 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 811 (Gtyp (Fuint 32))) joint_update_connection_811_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_811_split : joint_update_connection_811_decl = statement_append joint_update_connection_811_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 811) (@Eref VarOrder.T (@Eid VarOrder.T 8138))) joint_update_connection_811_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_811_straight : straight_statements joint_update_connection_811_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_811_mid_safe : formal_typed_suffix_safe flat_memories 811 joint_update_connection_811_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_811_tail_safe : formal_typed_suffix_safe flat_memories 811 joint_update_connection_811_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_811_nonregister : has_register 811 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_811_output invalid old current result :
 (exists ground bits, VM.find 8138 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 811 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 820 flat_statements joint_update_connection_811_decl joint_update_connection_811_mid joint_update_connection_811_tail
 811 8138 32 ground bits invalid flat_memories old current result
 joint_update_connection_811_position joint_update_connection_811_split joint_update_connection_811_straight joint_update_connection_811_mid_safe joint_update_connection_811_tail_safe
 joint_update_connection_811_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_812_decl := match straight_drop 822 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_812_tail := match straight_drop 8830 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_812_mid := take_statements 8007 joint_update_connection_812_decl.
Lemma joint_update_connection_812_position : straight_drop 821 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 812 (Gtyp (Fuint 32))) joint_update_connection_812_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_812_split : joint_update_connection_812_decl = statement_append joint_update_connection_812_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 812) (@Eref VarOrder.T (@Eid VarOrder.T 8140))) joint_update_connection_812_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_812_straight : straight_statements joint_update_connection_812_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_812_mid_safe : formal_typed_suffix_safe flat_memories 812 joint_update_connection_812_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_812_tail_safe : formal_typed_suffix_safe flat_memories 812 joint_update_connection_812_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_812_nonregister : has_register 812 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_812_output invalid old current result :
 (exists ground bits, VM.find 8140 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 812 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 821 flat_statements joint_update_connection_812_decl joint_update_connection_812_mid joint_update_connection_812_tail
 812 8140 32 ground bits invalid flat_memories old current result
 joint_update_connection_812_position joint_update_connection_812_split joint_update_connection_812_straight joint_update_connection_812_mid_safe joint_update_connection_812_tail_safe
 joint_update_connection_812_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_813_decl := match straight_drop 823 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_813_tail := match straight_drop 8831 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_813_mid := take_statements 8007 joint_update_connection_813_decl.
Lemma joint_update_connection_813_position : straight_drop 822 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 813 (Gtyp (Fuint 32))) joint_update_connection_813_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_813_split : joint_update_connection_813_decl = statement_append joint_update_connection_813_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 813) (@Eref VarOrder.T (@Eid VarOrder.T 8142))) joint_update_connection_813_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_813_straight : straight_statements joint_update_connection_813_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_813_mid_safe : formal_typed_suffix_safe flat_memories 813 joint_update_connection_813_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_813_tail_safe : formal_typed_suffix_safe flat_memories 813 joint_update_connection_813_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_813_nonregister : has_register 813 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_813_output invalid old current result :
 (exists ground bits, VM.find 8142 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 813 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 822 flat_statements joint_update_connection_813_decl joint_update_connection_813_mid joint_update_connection_813_tail
 813 8142 32 ground bits invalid flat_memories old current result
 joint_update_connection_813_position joint_update_connection_813_split joint_update_connection_813_straight joint_update_connection_813_mid_safe joint_update_connection_813_tail_safe
 joint_update_connection_813_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_814_decl := match straight_drop 824 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_814_tail := match straight_drop 8832 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_814_mid := take_statements 8007 joint_update_connection_814_decl.
Lemma joint_update_connection_814_position : straight_drop 823 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 814 (Gtyp (Fuint 32))) joint_update_connection_814_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_814_split : joint_update_connection_814_decl = statement_append joint_update_connection_814_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 814) (@Eref VarOrder.T (@Eid VarOrder.T 8144))) joint_update_connection_814_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_814_straight : straight_statements joint_update_connection_814_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_814_mid_safe : formal_typed_suffix_safe flat_memories 814 joint_update_connection_814_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_814_tail_safe : formal_typed_suffix_safe flat_memories 814 joint_update_connection_814_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_814_nonregister : has_register 814 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_814_output invalid old current result :
 (exists ground bits, VM.find 8144 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 814 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 823 flat_statements joint_update_connection_814_decl joint_update_connection_814_mid joint_update_connection_814_tail
 814 8144 32 ground bits invalid flat_memories old current result
 joint_update_connection_814_position joint_update_connection_814_split joint_update_connection_814_straight joint_update_connection_814_mid_safe joint_update_connection_814_tail_safe
 joint_update_connection_814_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_815_decl := match straight_drop 825 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_815_tail := match straight_drop 8833 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_815_mid := take_statements 8007 joint_update_connection_815_decl.
Lemma joint_update_connection_815_position : straight_drop 824 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 815 (Gtyp (Fuint 32))) joint_update_connection_815_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_815_split : joint_update_connection_815_decl = statement_append joint_update_connection_815_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 815) (@Eref VarOrder.T (@Eid VarOrder.T 8146))) joint_update_connection_815_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_815_straight : straight_statements joint_update_connection_815_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_815_mid_safe : formal_typed_suffix_safe flat_memories 815 joint_update_connection_815_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_815_tail_safe : formal_typed_suffix_safe flat_memories 815 joint_update_connection_815_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_815_nonregister : has_register 815 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_815_output invalid old current result :
 (exists ground bits, VM.find 8146 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 815 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 824 flat_statements joint_update_connection_815_decl joint_update_connection_815_mid joint_update_connection_815_tail
 815 8146 32 ground bits invalid flat_memories old current result
 joint_update_connection_815_position joint_update_connection_815_split joint_update_connection_815_straight joint_update_connection_815_mid_safe joint_update_connection_815_tail_safe
 joint_update_connection_815_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_816_decl := match straight_drop 826 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_816_tail := match straight_drop 8834 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_816_mid := take_statements 8007 joint_update_connection_816_decl.
Lemma joint_update_connection_816_position : straight_drop 825 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 816 (Gtyp (Fuint 32))) joint_update_connection_816_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_816_split : joint_update_connection_816_decl = statement_append joint_update_connection_816_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 816) (@Eref VarOrder.T (@Eid VarOrder.T 8148))) joint_update_connection_816_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_816_straight : straight_statements joint_update_connection_816_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_816_mid_safe : formal_typed_suffix_safe flat_memories 816 joint_update_connection_816_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_816_tail_safe : formal_typed_suffix_safe flat_memories 816 joint_update_connection_816_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_816_nonregister : has_register 816 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_816_output invalid old current result :
 (exists ground bits, VM.find 8148 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 816 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 825 flat_statements joint_update_connection_816_decl joint_update_connection_816_mid joint_update_connection_816_tail
 816 8148 32 ground bits invalid flat_memories old current result
 joint_update_connection_816_position joint_update_connection_816_split joint_update_connection_816_straight joint_update_connection_816_mid_safe joint_update_connection_816_tail_safe
 joint_update_connection_816_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_817_decl := match straight_drop 827 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_817_tail := match straight_drop 8835 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_817_mid := take_statements 8007 joint_update_connection_817_decl.
Lemma joint_update_connection_817_position : straight_drop 826 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 817 (Gtyp (Fuint 32))) joint_update_connection_817_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_817_split : joint_update_connection_817_decl = statement_append joint_update_connection_817_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 817) (@Eref VarOrder.T (@Eid VarOrder.T 8150))) joint_update_connection_817_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_817_straight : straight_statements joint_update_connection_817_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_817_mid_safe : formal_typed_suffix_safe flat_memories 817 joint_update_connection_817_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_817_tail_safe : formal_typed_suffix_safe flat_memories 817 joint_update_connection_817_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_817_nonregister : has_register 817 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_817_output invalid old current result :
 (exists ground bits, VM.find 8150 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 817 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 826 flat_statements joint_update_connection_817_decl joint_update_connection_817_mid joint_update_connection_817_tail
 817 8150 32 ground bits invalid flat_memories old current result
 joint_update_connection_817_position joint_update_connection_817_split joint_update_connection_817_straight joint_update_connection_817_mid_safe joint_update_connection_817_tail_safe
 joint_update_connection_817_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_818_decl := match straight_drop 828 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_818_tail := match straight_drop 8836 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_818_mid := take_statements 8007 joint_update_connection_818_decl.
Lemma joint_update_connection_818_position : straight_drop 827 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 818 (Gtyp (Fuint 32))) joint_update_connection_818_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_818_split : joint_update_connection_818_decl = statement_append joint_update_connection_818_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 818) (@Eref VarOrder.T (@Eid VarOrder.T 8152))) joint_update_connection_818_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_818_straight : straight_statements joint_update_connection_818_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_818_mid_safe : formal_typed_suffix_safe flat_memories 818 joint_update_connection_818_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_818_tail_safe : formal_typed_suffix_safe flat_memories 818 joint_update_connection_818_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_818_nonregister : has_register 818 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_818_output invalid old current result :
 (exists ground bits, VM.find 8152 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 818 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 827 flat_statements joint_update_connection_818_decl joint_update_connection_818_mid joint_update_connection_818_tail
 818 8152 32 ground bits invalid flat_memories old current result
 joint_update_connection_818_position joint_update_connection_818_split joint_update_connection_818_straight joint_update_connection_818_mid_safe joint_update_connection_818_tail_safe
 joint_update_connection_818_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_129_decl := match straight_drop 107 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_129_tail := match straight_drop 758 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_129_mid := take_statements 650 joint_update_connection_129_decl.
Lemma joint_update_connection_129_position : straight_drop 106 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 129 (Gtyp (Fuint 32))) joint_update_connection_129_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_129_split : joint_update_connection_129_decl = statement_append joint_update_connection_129_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 129) (@Eref VarOrder.T (@Eid VarOrder.T 445))) joint_update_connection_129_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_129_straight : straight_statements joint_update_connection_129_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_129_mid_safe : formal_typed_suffix_safe flat_memories 129 joint_update_connection_129_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_129_tail_safe : formal_typed_suffix_safe flat_memories 129 joint_update_connection_129_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_129_nonregister : has_register 129 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_129_output invalid old current result :
 (exists ground bits, VM.find 445 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 129 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 106 flat_statements joint_update_connection_129_decl joint_update_connection_129_mid joint_update_connection_129_tail
 129 445 32 ground bits invalid flat_memories old current result
 joint_update_connection_129_position joint_update_connection_129_split joint_update_connection_129_straight joint_update_connection_129_mid_safe joint_update_connection_129_tail_safe
 joint_update_connection_129_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_117_decl := match straight_drop 95 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_117_tail := match straight_drop 8786 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_117_mid := take_statements 8690 joint_update_connection_117_decl.
Lemma joint_update_connection_117_position : straight_drop 94 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 117 (Gtyp (Fuint 1))) joint_update_connection_117_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_117_split : joint_update_connection_117_decl = statement_append joint_update_connection_117_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 117) (@Eref VarOrder.T (@Eid VarOrder.T 7765))) joint_update_connection_117_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_117_straight : straight_statements joint_update_connection_117_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_117_mid_safe : formal_typed_suffix_safe flat_memories 117 joint_update_connection_117_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_117_tail_safe : formal_typed_suffix_safe flat_memories 117 joint_update_connection_117_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_117_nonregister : has_register 117 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_117_output invalid old current result :
 (exists ground bits, VM.find 7765 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 117 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 94 flat_statements joint_update_connection_117_decl joint_update_connection_117_mid joint_update_connection_117_tail
 117 7765 1 ground bits invalid flat_memories old current result
 joint_update_connection_117_position joint_update_connection_117_split joint_update_connection_117_straight joint_update_connection_117_mid_safe joint_update_connection_117_tail_safe
 joint_update_connection_117_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_120_decl := match straight_drop 98 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_120_tail := match straight_drop 756 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_120_mid := take_statements 657 joint_update_connection_120_decl.
Lemma joint_update_connection_120_position : straight_drop 97 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 120 (Gtyp (Fuint 32))) joint_update_connection_120_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_120_split : joint_update_connection_120_decl = statement_append joint_update_connection_120_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 120) (@Eref VarOrder.T (@Eid VarOrder.T 281))) joint_update_connection_120_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_120_straight : straight_statements joint_update_connection_120_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_120_mid_safe : formal_typed_suffix_safe flat_memories 120 joint_update_connection_120_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_120_tail_safe : formal_typed_suffix_safe flat_memories 120 joint_update_connection_120_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_120_nonregister : has_register 120 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_120_output invalid old current result :
 (exists ground bits, VM.find 281 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 120 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 97 flat_statements joint_update_connection_120_decl joint_update_connection_120_mid joint_update_connection_120_tail
 120 281 32 ground bits invalid flat_memories old current result
 joint_update_connection_120_position joint_update_connection_120_split joint_update_connection_120_straight joint_update_connection_120_mid_safe joint_update_connection_120_tail_safe
 joint_update_connection_120_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_786_decl := match straight_drop 796 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_786_tail := match straight_drop 8804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_786_mid := take_statements 8007 joint_update_connection_786_decl.
Lemma joint_update_connection_786_position : straight_drop 795 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 786 (Gtyp (Fuint 32))) joint_update_connection_786_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_786_split : joint_update_connection_786_decl = statement_append joint_update_connection_786_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 786) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7937)))) joint_update_connection_786_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_786_straight : straight_statements joint_update_connection_786_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_786_mid_safe : formal_typed_suffix_safe flat_memories 786 joint_update_connection_786_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_786_tail_safe : formal_typed_suffix_safe flat_memories 786 joint_update_connection_786_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_786_nonregister : has_register 786 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_786_output invalid old current result :
 (exists ground bits, VM.find 7937 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 786 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_unary_connection_concrete 795 flat_statements joint_update_connection_786_decl joint_update_connection_786_mid joint_update_connection_786_tail
 786 7937 (Uextr 31 0) 32 ground bits invalid flat_memories old current result
 joint_update_connection_786_position joint_update_connection_786_split joint_update_connection_786_straight joint_update_connection_786_mid_safe joint_update_connection_786_tail_safe
 joint_update_connection_786_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_1357_decl := match straight_drop 1436 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1357_tail := match straight_drop 8848 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1357_mid := take_statements 7411 joint_update_connection_1357_decl.
Lemma joint_update_connection_1357_position : straight_drop 1435 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1357 (Gtyp (Fuint 32))) joint_update_connection_1357_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1357_split : joint_update_connection_1357_decl = statement_append joint_update_connection_1357_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1357) (@Eref VarOrder.T (@Eid VarOrder.T 7816))) joint_update_connection_1357_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1357_straight : straight_statements joint_update_connection_1357_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_1357_mid_safe : formal_typed_suffix_safe flat_memories 1357 joint_update_connection_1357_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1357_tail_safe : formal_typed_suffix_safe flat_memories 1357 joint_update_connection_1357_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1357_nonregister : has_register 1357 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_1357_output invalid old current result :
 (exists ground bits, VM.find 7816 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1357 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1435 flat_statements joint_update_connection_1357_decl joint_update_connection_1357_mid joint_update_connection_1357_tail
 1357 7816 32 ground bits invalid flat_memories old current result
 joint_update_connection_1357_position joint_update_connection_1357_split joint_update_connection_1357_straight joint_update_connection_1357_mid_safe joint_update_connection_1357_tail_safe
 joint_update_connection_1357_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_1358_decl := match straight_drop 1437 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1358_tail := match straight_drop 8849 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1358_mid := take_statements 7411 joint_update_connection_1358_decl.
Lemma joint_update_connection_1358_position : straight_drop 1436 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1358 (Gtyp (Fuint 32))) joint_update_connection_1358_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1358_split : joint_update_connection_1358_decl = statement_append joint_update_connection_1358_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1358) (@Eref VarOrder.T (@Eid VarOrder.T 7819))) joint_update_connection_1358_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1358_straight : straight_statements joint_update_connection_1358_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_1358_mid_safe : formal_typed_suffix_safe flat_memories 1358 joint_update_connection_1358_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1358_tail_safe : formal_typed_suffix_safe flat_memories 1358 joint_update_connection_1358_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1358_nonregister : has_register 1358 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_1358_output invalid old current result :
 (exists ground bits, VM.find 7819 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1358 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1436 flat_statements joint_update_connection_1358_decl joint_update_connection_1358_mid joint_update_connection_1358_tail
 1358 7819 32 ground bits invalid flat_memories old current result
 joint_update_connection_1358_position joint_update_connection_1358_split joint_update_connection_1358_straight joint_update_connection_1358_mid_safe joint_update_connection_1358_tail_safe
 joint_update_connection_1358_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_128_decl := match straight_drop 106 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_128_tail := match straight_drop 757 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_128_mid := take_statements 650 joint_update_connection_128_decl.
Lemma joint_update_connection_128_position : straight_drop 105 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 128 (Gtyp (Fuint 1))) joint_update_connection_128_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_128_split : joint_update_connection_128_decl = statement_append joint_update_connection_128_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 128) (@Eref VarOrder.T (@Eid VarOrder.T 442))) joint_update_connection_128_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_128_straight : straight_statements joint_update_connection_128_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_128_mid_safe : formal_typed_suffix_safe flat_memories 128 joint_update_connection_128_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_128_tail_safe : formal_typed_suffix_safe flat_memories 128 joint_update_connection_128_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_128_nonregister : has_register 128 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_128_output invalid old current result :
 (exists ground bits, VM.find 442 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 128 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 105 flat_statements joint_update_connection_128_decl joint_update_connection_128_mid joint_update_connection_128_tail
 128 442 1 ground bits invalid flat_memories old current result
 joint_update_connection_128_position joint_update_connection_128_split joint_update_connection_128_straight joint_update_connection_128_mid_safe joint_update_connection_128_tail_safe
 joint_update_connection_128_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_784_decl := match straight_drop 794 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_784_tail := match straight_drop 8802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_784_mid := take_statements 8007 joint_update_connection_784_decl.
Lemma joint_update_connection_784_position : straight_drop 793 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 784 (Gtyp (Fuint 1))) joint_update_connection_784_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_784_split : joint_update_connection_784_decl = statement_append joint_update_connection_784_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 784) (@Eref VarOrder.T (@Eid VarOrder.T 7941))) joint_update_connection_784_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_784_straight : straight_statements joint_update_connection_784_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_784_mid_safe : formal_typed_suffix_safe flat_memories 784 joint_update_connection_784_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_784_tail_safe : formal_typed_suffix_safe flat_memories 784 joint_update_connection_784_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_784_nonregister : has_register 784 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_784_output invalid old current result :
 (exists ground bits, VM.find 7941 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 784 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 793 flat_statements joint_update_connection_784_decl joint_update_connection_784_mid joint_update_connection_784_tail
 784 7941 1 ground bits invalid flat_memories old current result
 joint_update_connection_784_position joint_update_connection_784_split joint_update_connection_784_straight joint_update_connection_784_mid_safe joint_update_connection_784_tail_safe
 joint_update_connection_784_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8250_decl := match straight_drop 9011 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8250_tail := match straight_drop 9761 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8250_mid := take_statements 749 joint_update_connection_8250_decl.
Lemma joint_update_connection_8250_position : straight_drop 9010 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8250 (Gtyp (Fuint 2))) joint_update_connection_8250_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8250_split : joint_update_connection_8250_decl = statement_append joint_update_connection_8250_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8250) (@Eref VarOrder.T (@Eid VarOrder.T 8409))) joint_update_connection_8250_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8250_straight : straight_statements joint_update_connection_8250_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8250_mid_safe : formal_typed_suffix_safe flat_memories 8250 joint_update_connection_8250_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8250_tail_safe : formal_typed_suffix_safe flat_memories 8250 joint_update_connection_8250_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8250_nonregister : has_register 8250 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8250_output invalid old current result :
 (exists ground bits, VM.find 8409 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8250 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9010 flat_statements joint_update_connection_8250_decl joint_update_connection_8250_mid joint_update_connection_8250_tail
 8250 8409 2 ground bits invalid flat_memories old current result
 joint_update_connection_8250_position joint_update_connection_8250_split joint_update_connection_8250_straight joint_update_connection_8250_mid_safe joint_update_connection_8250_tail_safe
 joint_update_connection_8250_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8256_decl := match straight_drop 9017 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8256_tail := match straight_drop 9767 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8256_mid := take_statements 749 joint_update_connection_8256_decl.
Lemma joint_update_connection_8256_position : straight_drop 9016 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8256 (Gtyp (Fuint 3))) joint_update_connection_8256_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8256_split : joint_update_connection_8256_decl = statement_append joint_update_connection_8256_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8256) (@Eref VarOrder.T (@Eid VarOrder.T 8654))) joint_update_connection_8256_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8256_straight : straight_statements joint_update_connection_8256_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8256_mid_safe : formal_typed_suffix_safe flat_memories 8256 joint_update_connection_8256_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8256_tail_safe : formal_typed_suffix_safe flat_memories 8256 joint_update_connection_8256_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8256_nonregister : has_register 8256 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8256_output invalid old current result :
 (exists ground bits, VM.find 8654 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8256 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9016 flat_statements joint_update_connection_8256_decl joint_update_connection_8256_mid joint_update_connection_8256_tail
 8256 8654 3 ground bits invalid flat_memories old current result
 joint_update_connection_8256_position joint_update_connection_8256_split joint_update_connection_8256_straight joint_update_connection_8256_mid_safe joint_update_connection_8256_tail_safe
 joint_update_connection_8256_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8259_decl := match straight_drop 9020 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8259_tail := match straight_drop 9770 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8259_mid := take_statements 749 joint_update_connection_8259_decl.
Lemma joint_update_connection_8259_position : straight_drop 9019 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8259 (Gtyp (Fuint 2))) joint_update_connection_8259_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8259_split : joint_update_connection_8259_decl = statement_append joint_update_connection_8259_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8259) (@Eref VarOrder.T (@Eid VarOrder.T 8850))) joint_update_connection_8259_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8259_straight : straight_statements joint_update_connection_8259_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8259_mid_safe : formal_typed_suffix_safe flat_memories 8259 joint_update_connection_8259_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8259_tail_safe : formal_typed_suffix_safe flat_memories 8259 joint_update_connection_8259_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8259_nonregister : has_register 8259 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8259_output invalid old current result :
 (exists ground bits, VM.find 8850 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8259 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9019 flat_statements joint_update_connection_8259_decl joint_update_connection_8259_mid joint_update_connection_8259_tail
 8259 8850 2 ground bits invalid flat_memories old current result
 joint_update_connection_8259_position joint_update_connection_8259_split joint_update_connection_8259_straight joint_update_connection_8259_mid_safe joint_update_connection_8259_tail_safe
 joint_update_connection_8259_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8261_decl := match straight_drop 9022 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8261_tail := match straight_drop 9772 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8261_mid := take_statements 749 joint_update_connection_8261_decl.
Lemma joint_update_connection_8261_position : straight_drop 9021 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8261 (Gtyp (Fuint 3))) joint_update_connection_8261_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8261_split : joint_update_connection_8261_decl = statement_append joint_update_connection_8261_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8261) (@Eref VarOrder.T (@Eid VarOrder.T 8948))) joint_update_connection_8261_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8261_straight : straight_statements joint_update_connection_8261_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8261_mid_safe : formal_typed_suffix_safe flat_memories 8261 joint_update_connection_8261_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8261_tail_safe : formal_typed_suffix_safe flat_memories 8261 joint_update_connection_8261_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8261_nonregister : has_register 8261 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8261_output invalid old current result :
 (exists ground bits, VM.find 8948 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8261 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9021 flat_statements joint_update_connection_8261_decl joint_update_connection_8261_mid joint_update_connection_8261_tail
 8261 8948 3 ground bits invalid flat_memories old current result
 joint_update_connection_8261_position joint_update_connection_8261_split joint_update_connection_8261_straight joint_update_connection_8261_mid_safe joint_update_connection_8261_tail_safe
 joint_update_connection_8261_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8262_decl := match straight_drop 9023 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8262_tail := match straight_drop 9773 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8262_mid := take_statements 749 joint_update_connection_8262_decl.
Lemma joint_update_connection_8262_position : straight_drop 9022 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8262 (Gtyp (Fuint 1))) joint_update_connection_8262_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8262_split : joint_update_connection_8262_decl = statement_append joint_update_connection_8262_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8262) (@Eref VarOrder.T (@Eid VarOrder.T 8997))) joint_update_connection_8262_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8262_straight : straight_statements joint_update_connection_8262_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8262_mid_safe : formal_typed_suffix_safe flat_memories 8262 joint_update_connection_8262_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8262_tail_safe : formal_typed_suffix_safe flat_memories 8262 joint_update_connection_8262_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8262_nonregister : has_register 8262 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8262_output invalid old current result :
 (exists ground bits, VM.find 8997 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8262 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9022 flat_statements joint_update_connection_8262_decl joint_update_connection_8262_mid joint_update_connection_8262_tail
 8262 8997 1 ground bits invalid flat_memories old current result
 joint_update_connection_8262_position joint_update_connection_8262_split joint_update_connection_8262_straight joint_update_connection_8262_mid_safe joint_update_connection_8262_tail_safe
 joint_update_connection_8262_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_84_decl := match straight_drop 62 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_84_tail := match straight_drop 9991 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_84_mid := take_statements 9928 joint_update_connection_84_decl.
Lemma joint_update_connection_84_position : straight_drop 61 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 84 (Gtyp (Fuint 2))) joint_update_connection_84_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_84_split : joint_update_connection_84_decl = statement_append joint_update_connection_84_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 84) (@Eref VarOrder.T (@Eid VarOrder.T 8250))) joint_update_connection_84_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_84_straight : straight_statements joint_update_connection_84_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_84_mid_safe : formal_typed_suffix_safe flat_memories 84 joint_update_connection_84_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_84_tail_safe : formal_typed_suffix_safe flat_memories 84 joint_update_connection_84_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_84_nonregister : has_register 84 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_84_output invalid old current result :
 (exists ground bits, VM.find 8250 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 84 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 61 flat_statements joint_update_connection_84_decl joint_update_connection_84_mid joint_update_connection_84_tail
 84 8250 2 ground bits invalid flat_memories old current result
 joint_update_connection_84_position joint_update_connection_84_split joint_update_connection_84_straight joint_update_connection_84_mid_safe joint_update_connection_84_tail_safe
 joint_update_connection_84_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_90_decl := match straight_drop 68 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_90_tail := match straight_drop 9997 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_90_mid := take_statements 9928 joint_update_connection_90_decl.
Lemma joint_update_connection_90_position : straight_drop 67 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 90 (Gtyp (Fuint 3))) joint_update_connection_90_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_90_split : joint_update_connection_90_decl = statement_append joint_update_connection_90_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 90) (@Eref VarOrder.T (@Eid VarOrder.T 8256))) joint_update_connection_90_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_90_straight : straight_statements joint_update_connection_90_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_90_mid_safe : formal_typed_suffix_safe flat_memories 90 joint_update_connection_90_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_90_tail_safe : formal_typed_suffix_safe flat_memories 90 joint_update_connection_90_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_90_nonregister : has_register 90 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_90_output invalid old current result :
 (exists ground bits, VM.find 8256 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 90 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 67 flat_statements joint_update_connection_90_decl joint_update_connection_90_mid joint_update_connection_90_tail
 90 8256 3 ground bits invalid flat_memories old current result
 joint_update_connection_90_position joint_update_connection_90_split joint_update_connection_90_straight joint_update_connection_90_mid_safe joint_update_connection_90_tail_safe
 joint_update_connection_90_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_93_decl := match straight_drop 71 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_93_tail := match straight_drop 10000 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_93_mid := take_statements 9928 joint_update_connection_93_decl.
Lemma joint_update_connection_93_position : straight_drop 70 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 93 (Gtyp (Fuint 2))) joint_update_connection_93_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_93_split : joint_update_connection_93_decl = statement_append joint_update_connection_93_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 93) (@Eref VarOrder.T (@Eid VarOrder.T 8259))) joint_update_connection_93_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_93_straight : straight_statements joint_update_connection_93_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_93_mid_safe : formal_typed_suffix_safe flat_memories 93 joint_update_connection_93_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_93_tail_safe : formal_typed_suffix_safe flat_memories 93 joint_update_connection_93_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_93_nonregister : has_register 93 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_93_output invalid old current result :
 (exists ground bits, VM.find 8259 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 93 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 70 flat_statements joint_update_connection_93_decl joint_update_connection_93_mid joint_update_connection_93_tail
 93 8259 2 ground bits invalid flat_memories old current result
 joint_update_connection_93_position joint_update_connection_93_split joint_update_connection_93_straight joint_update_connection_93_mid_safe joint_update_connection_93_tail_safe
 joint_update_connection_93_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_95_decl := match straight_drop 73 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_95_tail := match straight_drop 10002 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_95_mid := take_statements 9928 joint_update_connection_95_decl.
Lemma joint_update_connection_95_position : straight_drop 72 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 95 (Gtyp (Fuint 3))) joint_update_connection_95_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_95_split : joint_update_connection_95_decl = statement_append joint_update_connection_95_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 95) (@Eref VarOrder.T (@Eid VarOrder.T 8261))) joint_update_connection_95_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_95_straight : straight_statements joint_update_connection_95_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_95_mid_safe : formal_typed_suffix_safe flat_memories 95 joint_update_connection_95_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_95_tail_safe : formal_typed_suffix_safe flat_memories 95 joint_update_connection_95_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_95_nonregister : has_register 95 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_95_output invalid old current result :
 (exists ground bits, VM.find 8261 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 95 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 72 flat_statements joint_update_connection_95_decl joint_update_connection_95_mid joint_update_connection_95_tail
 95 8261 3 ground bits invalid flat_memories old current result
 joint_update_connection_95_position joint_update_connection_95_split joint_update_connection_95_straight joint_update_connection_95_mid_safe joint_update_connection_95_tail_safe
 joint_update_connection_95_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_96_decl := match straight_drop 74 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_96_tail := match straight_drop 10003 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_96_mid := take_statements 9928 joint_update_connection_96_decl.
Lemma joint_update_connection_96_position : straight_drop 73 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 96 (Gtyp (Fuint 1))) joint_update_connection_96_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_96_split : joint_update_connection_96_decl = statement_append joint_update_connection_96_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 96) (@Eref VarOrder.T (@Eid VarOrder.T 8262))) joint_update_connection_96_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_96_straight : straight_statements joint_update_connection_96_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_96_mid_safe : formal_typed_suffix_safe flat_memories 96 joint_update_connection_96_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_96_tail_safe : formal_typed_suffix_safe flat_memories 96 joint_update_connection_96_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_96_nonregister : has_register 96 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_96_output invalid old current result :
 (exists ground bits, VM.find 8262 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 96 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 73 flat_statements joint_update_connection_96_decl joint_update_connection_96_mid joint_update_connection_96_tail
 96 8262 1 ground bits invalid flat_memories old current result
 joint_update_connection_96_position joint_update_connection_96_split joint_update_connection_96_straight joint_update_connection_96_mid_safe joint_update_connection_96_tail_safe
 joint_update_connection_96_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8251_decl := match straight_drop 9012 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8251_tail := match straight_drop 9762 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8251_mid := take_statements 749 joint_update_connection_8251_decl.
Lemma joint_update_connection_8251_position : straight_drop 9011 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8251 (Gtyp (Fuint 1))) joint_update_connection_8251_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8251_split : joint_update_connection_8251_decl = statement_append joint_update_connection_8251_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8251) (@Eref VarOrder.T (@Eid VarOrder.T 8998))) joint_update_connection_8251_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8251_straight : straight_statements joint_update_connection_8251_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8251_mid_safe : formal_typed_suffix_safe flat_memories 8251 joint_update_connection_8251_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8251_tail_safe : formal_typed_suffix_safe flat_memories 8251 joint_update_connection_8251_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8251_nonregister : has_register 8251 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8251_output invalid old current result :
 (exists ground bits, VM.find 8998 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8251 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9011 flat_statements joint_update_connection_8251_decl joint_update_connection_8251_mid joint_update_connection_8251_tail
 8251 8998 1 ground bits invalid flat_memories old current result
 joint_update_connection_8251_position joint_update_connection_8251_split joint_update_connection_8251_straight joint_update_connection_8251_mid_safe joint_update_connection_8251_tail_safe
 joint_update_connection_8251_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_8260_decl := match straight_drop 9021 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8260_tail := match straight_drop 9771 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_8260_mid := take_statements 749 joint_update_connection_8260_decl.
Lemma joint_update_connection_8260_position : straight_drop 9020 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8260 (Gtyp (Fuint 1))) joint_update_connection_8260_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8260_split : joint_update_connection_8260_decl = statement_append joint_update_connection_8260_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8260) (@Eref VarOrder.T (@Eid VarOrder.T 8999))) joint_update_connection_8260_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8260_straight : straight_statements joint_update_connection_8260_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_8260_mid_safe : formal_typed_suffix_safe flat_memories 8260 joint_update_connection_8260_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8260_tail_safe : formal_typed_suffix_safe flat_memories 8260 joint_update_connection_8260_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_8260_nonregister : has_register 8260 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_8260_output invalid old current result :
 (exists ground bits, VM.find 8999 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8260 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9020 flat_statements joint_update_connection_8260_decl joint_update_connection_8260_mid joint_update_connection_8260_tail
 8260 8999 1 ground bits invalid flat_memories old current result
 joint_update_connection_8260_position joint_update_connection_8260_split joint_update_connection_8260_straight joint_update_connection_8260_mid_safe joint_update_connection_8260_tail_safe
 joint_update_connection_8260_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_85_decl := match straight_drop 63 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_85_tail := match straight_drop 9992 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_85_mid := take_statements 9928 joint_update_connection_85_decl.
Lemma joint_update_connection_85_position : straight_drop 62 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 85 (Gtyp (Fuint 1))) joint_update_connection_85_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_85_split : joint_update_connection_85_decl = statement_append joint_update_connection_85_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 85) (@Eref VarOrder.T (@Eid VarOrder.T 8251))) joint_update_connection_85_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_85_straight : straight_statements joint_update_connection_85_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_85_mid_safe : formal_typed_suffix_safe flat_memories 85 joint_update_connection_85_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_85_tail_safe : formal_typed_suffix_safe flat_memories 85 joint_update_connection_85_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_85_nonregister : has_register 85 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_85_output invalid old current result :
 (exists ground bits, VM.find 8251 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 85 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 62 flat_statements joint_update_connection_85_decl joint_update_connection_85_mid joint_update_connection_85_tail
 85 8251 1 ground bits invalid flat_memories old current result
 joint_update_connection_85_position joint_update_connection_85_split joint_update_connection_85_straight joint_update_connection_85_mid_safe joint_update_connection_85_tail_safe
 joint_update_connection_85_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_94_decl := match straight_drop 72 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_94_tail := match straight_drop 10001 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_94_mid := take_statements 9928 joint_update_connection_94_decl.
Lemma joint_update_connection_94_position : straight_drop 71 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 94 (Gtyp (Fuint 1))) joint_update_connection_94_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_94_split : joint_update_connection_94_decl = statement_append joint_update_connection_94_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 94) (@Eref VarOrder.T (@Eid VarOrder.T 8260))) joint_update_connection_94_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_94_straight : straight_statements joint_update_connection_94_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_94_mid_safe : formal_typed_suffix_safe flat_memories 94 joint_update_connection_94_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_94_tail_safe : formal_typed_suffix_safe flat_memories 94 joint_update_connection_94_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_94_nonregister : has_register 94 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_94_output invalid old current result :
 (exists ground bits, VM.find 8260 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 94 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 71 flat_statements joint_update_connection_94_decl joint_update_connection_94_mid joint_update_connection_94_tail
 94 8260 1 ground bits invalid flat_memories old current result
 joint_update_connection_94_position joint_update_connection_94_split joint_update_connection_94_straight joint_update_connection_94_mid_safe joint_update_connection_94_tail_safe
 joint_update_connection_94_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_1359_decl := match straight_drop 1438 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1359_tail := match straight_drop 8850 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1359_mid := take_statements 7411 joint_update_connection_1359_decl.
Lemma joint_update_connection_1359_position : straight_drop 1437 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1359 (Gtyp (Fuint 3))) joint_update_connection_1359_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1359_split : joint_update_connection_1359_decl = statement_append joint_update_connection_1359_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1359) (@Eref VarOrder.T (@Eid VarOrder.T 90))) joint_update_connection_1359_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1359_straight : straight_statements joint_update_connection_1359_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_1359_mid_safe : formal_typed_suffix_safe flat_memories 1359 joint_update_connection_1359_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1359_tail_safe : formal_typed_suffix_safe flat_memories 1359 joint_update_connection_1359_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1359_nonregister : has_register 1359 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_1359_output invalid old current result :
 (exists ground bits, VM.find 90 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1359 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1437 flat_statements joint_update_connection_1359_decl joint_update_connection_1359_mid joint_update_connection_1359_tail
 1359 90 3 ground bits invalid flat_memories old current result
 joint_update_connection_1359_position joint_update_connection_1359_split joint_update_connection_1359_straight joint_update_connection_1359_mid_safe joint_update_connection_1359_tail_safe
 joint_update_connection_1359_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_1360_decl := match straight_drop 1439 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1360_tail := match straight_drop 1472 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1360_mid := take_statements 32 joint_update_connection_1360_decl.
Lemma joint_update_connection_1360_position : straight_drop 1438 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1360 (Gtyp (Fuint 1))) joint_update_connection_1360_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1360_split : joint_update_connection_1360_decl = statement_append joint_update_connection_1360_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1360) (@Eref VarOrder.T (@Eid VarOrder.T 1392))) joint_update_connection_1360_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1360_straight : straight_statements joint_update_connection_1360_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_1360_mid_safe : formal_typed_suffix_safe flat_memories 1360 joint_update_connection_1360_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1360_tail_safe : formal_typed_suffix_safe flat_memories 1360 joint_update_connection_1360_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1360_nonregister : has_register 1360 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_1360_output invalid old current result :
 (exists ground bits, VM.find 1392 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1360 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1438 flat_statements joint_update_connection_1360_decl joint_update_connection_1360_mid joint_update_connection_1360_tail
 1360 1392 1 ground bits invalid flat_memories old current result
 joint_update_connection_1360_position joint_update_connection_1360_split joint_update_connection_1360_straight joint_update_connection_1360_mid_safe joint_update_connection_1360_tail_safe
 joint_update_connection_1360_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition joint_update_connection_1154_decl := match straight_drop 1230 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1154_tail := match straight_drop 1380 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_update_connection_1154_mid := take_statements 149 joint_update_connection_1154_decl.
Lemma joint_update_connection_1154_position : straight_drop 1229 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1154 (Gtyp (Fuint 32))) joint_update_connection_1154_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1154_split : joint_update_connection_1154_decl = statement_append joint_update_connection_1154_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1154) (@Eref VarOrder.T (@Eid VarOrder.T 1303))) joint_update_connection_1154_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1154_straight : straight_statements joint_update_connection_1154_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_update_connection_1154_mid_safe : formal_typed_suffix_safe flat_memories 1154 joint_update_connection_1154_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1154_tail_safe : formal_typed_suffix_safe flat_memories 1154 joint_update_connection_1154_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_update_connection_1154_nonregister : has_register 1154 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_connection_1154_output invalid old current result :
 (exists ground bits, VM.find 1303 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1154 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail
 1154 1303 32 ground bits invalid flat_memories old current result
 joint_update_connection_1154_position joint_update_connection_1154_split joint_update_connection_1154_straight joint_update_connection_1154_mid_safe joint_update_connection_1154_tail_safe
 joint_update_connection_1154_nonregister (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions joint_update_connection_1154_output.
