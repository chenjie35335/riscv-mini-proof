Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_address_connection_83_decl := match straight_drop 61 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_83_tail := match straight_drop 8765 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_83_mid := take_statements 8703 data_address_connection_83_decl.
Lemma data_address_connection_83_position : straight_drop 60 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 83 (Gtyp (Fuint 32))) data_address_connection_83_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_83_split : data_address_connection_83_decl = statement_append data_address_connection_83_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 83) (@Eref VarOrder.T (@Eid VarOrder.T 7748))) data_address_connection_83_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_83_straight : straight_statements data_address_connection_83_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_83_mid_safe : formal_typed_suffix_safe flat_memories 83 data_address_connection_83_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_83_tail_safe : formal_typed_suffix_safe flat_memories 83 data_address_connection_83_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_83_nonregister : has_register 83 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_83_output invalid old current result :
 (exists ground bits, VM.find 7748 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 83 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 60 flat_statements data_address_connection_83_decl data_address_connection_83_mid data_address_connection_83_tail
 83 7748 32 ground bits invalid flat_memories old current result
 data_address_connection_83_position data_address_connection_83_split data_address_connection_83_straight data_address_connection_83_mid_safe data_address_connection_83_tail_safe
 data_address_connection_83_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1306_decl := match straight_drop 1384 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1306_tail := match straight_drop 8844 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1306_mid := take_statements 7459 data_address_connection_1306_decl.
Lemma data_address_connection_1306_position : straight_drop 1383 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1306 (Gtyp (Fuint 32))) data_address_connection_1306_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1306_split : data_address_connection_1306_decl = statement_append data_address_connection_1306_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1306) (@Eref VarOrder.T (@Eid VarOrder.T 7748))) data_address_connection_1306_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1306_straight : straight_statements data_address_connection_1306_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1306_mid_safe : formal_typed_suffix_safe flat_memories 1306 data_address_connection_1306_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1306_tail_safe : formal_typed_suffix_safe flat_memories 1306 data_address_connection_1306_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1306_nonregister : has_register 1306 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1306_output invalid old current result :
 (exists ground bits, VM.find 7748 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1306 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1383 flat_statements data_address_connection_1306_decl data_address_connection_1306_mid data_address_connection_1306_tail
 1306 7748 32 ground bits invalid flat_memories old current result
 data_address_connection_1306_position data_address_connection_1306_split data_address_connection_1306_straight data_address_connection_1306_mid_safe data_address_connection_1306_tail_safe
 data_address_connection_1306_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_780_decl := match straight_drop 790 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_780_tail := match straight_drop 8800 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_780_mid := take_statements 8009 data_address_connection_780_decl.
Lemma data_address_connection_780_position : straight_drop 789 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 780 (Gtyp (Fuint 5))) data_address_connection_780_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_780_split : data_address_connection_780_decl = statement_append data_address_connection_780_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 780) (@Eref VarOrder.T (@Eid VarOrder.T 7803))) data_address_connection_780_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_780_straight : straight_statements data_address_connection_780_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_780_mid_safe : formal_typed_suffix_safe flat_memories 780 data_address_connection_780_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_780_tail_safe : formal_typed_suffix_safe flat_memories 780 data_address_connection_780_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_780_nonregister : has_register 780 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_780_output invalid old current result :
 (exists ground bits, VM.find 7803 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 780 result = Some (Gval (Fuint 5) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 789 flat_statements data_address_connection_780_decl data_address_connection_780_mid data_address_connection_780_tail
 780 7803 5 ground bits invalid flat_memories old current result
 data_address_connection_780_position data_address_connection_780_split data_address_connection_780_straight data_address_connection_780_mid_safe data_address_connection_780_tail_safe
 data_address_connection_780_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_781_decl := match straight_drop 791 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_781_tail := match straight_drop 8801 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_781_mid := take_statements 8009 data_address_connection_781_decl.
Lemma data_address_connection_781_position : straight_drop 790 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 781 (Gtyp (Fuint 5))) data_address_connection_781_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_781_split : data_address_connection_781_decl = statement_append data_address_connection_781_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 781) (@Eref VarOrder.T (@Eid VarOrder.T 7804))) data_address_connection_781_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_781_straight : straight_statements data_address_connection_781_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_781_mid_safe : formal_typed_suffix_safe flat_memories 781 data_address_connection_781_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_781_tail_safe : formal_typed_suffix_safe flat_memories 781 data_address_connection_781_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_781_nonregister : has_register 781 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_781_output invalid old current result :
 (exists ground bits, VM.find 7804 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 781 result = Some (Gval (Fuint 5) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 790 flat_statements data_address_connection_781_decl data_address_connection_781_mid data_address_connection_781_tail
 781 7804 5 ground bits invalid flat_memories old current result
 data_address_connection_781_position data_address_connection_781_split data_address_connection_781_straight data_address_connection_781_mid_safe data_address_connection_781_tail_safe
 data_address_connection_781_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_8249_decl := match straight_drop 9010 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8249_tail := match straight_drop 10006 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8249_mid := take_statements 995 data_address_connection_8249_decl.
Lemma data_address_connection_8249_position : straight_drop 9009 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8249 (Gtyp (Fuint 32))) data_address_connection_8249_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8249_split : data_address_connection_8249_decl = statement_append data_address_connection_8249_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8249) (@Eref VarOrder.T (@Eid VarOrder.T 83))) data_address_connection_8249_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8249_straight : straight_statements data_address_connection_8249_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_8249_mid_safe : formal_typed_suffix_safe flat_memories 8249 data_address_connection_8249_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8249_tail_safe : formal_typed_suffix_safe flat_memories 8249 data_address_connection_8249_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8249_nonregister : has_register 8249 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_8249_output invalid old current result :
 (exists ground bits, VM.find 83 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8249 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9009 flat_statements data_address_connection_8249_decl data_address_connection_8249_mid data_address_connection_8249_tail
 8249 83 32 ground bits invalid flat_memories old current result
 data_address_connection_8249_position data_address_connection_8249_split data_address_connection_8249_straight data_address_connection_8249_mid_safe data_address_connection_8249_tail_safe
 data_address_connection_8249_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_33_decl := match straight_drop 11 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_33_tail := match straight_drop 10097 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_33_mid := take_statements 10085 data_address_connection_33_decl.
Lemma data_address_connection_33_position : straight_drop 10 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 33 (Gtyp (Fuint 1))) data_address_connection_33_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_33_split : data_address_connection_33_decl = statement_append data_address_connection_33_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 33) (@Eref VarOrder.T (@Eid VarOrder.T 9216))) data_address_connection_33_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_33_straight : straight_statements data_address_connection_33_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_33_mid_safe : formal_typed_suffix_safe flat_memories 33 data_address_connection_33_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_33_tail_safe : formal_typed_suffix_safe flat_memories 33 data_address_connection_33_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_33_nonregister : has_register 33 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_33_output invalid old current result :
 (exists ground bits, VM.find 9216 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 33 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 10 flat_statements data_address_connection_33_decl data_address_connection_33_mid data_address_connection_33_tail
 33 9216 1 ground bits invalid flat_memories old current result
 data_address_connection_33_position data_address_connection_33_split data_address_connection_33_straight data_address_connection_33_mid_safe data_address_connection_33_tail_safe
 data_address_connection_33_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_40_decl := match straight_drop 18 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_40_tail := match straight_drop 10099 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_40_mid := take_statements 10080 data_address_connection_40_decl.
Lemma data_address_connection_40_position : straight_drop 17 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 40 (Gtyp (Fuint 1))) data_address_connection_40_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_40_split : data_address_connection_40_decl = statement_append data_address_connection_40_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 40) (@Eref VarOrder.T (@Eid VarOrder.T 9218))) data_address_connection_40_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_40_straight : straight_statements data_address_connection_40_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_40_mid_safe : formal_typed_suffix_safe flat_memories 40 data_address_connection_40_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_40_tail_safe : formal_typed_suffix_safe flat_memories 40 data_address_connection_40_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_40_nonregister : has_register 40 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_40_output invalid old current result :
 (exists ground bits, VM.find 9218 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 40 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 17 flat_statements data_address_connection_40_decl data_address_connection_40_mid data_address_connection_40_tail
 40 9218 1 ground bits invalid flat_memories old current result
 data_address_connection_40_position data_address_connection_40_split data_address_connection_40_straight data_address_connection_40_mid_safe data_address_connection_40_tail_safe
 data_address_connection_40_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_74_decl := match straight_drop 52 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_74_tail := match straight_drop 9987 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_74_mid := take_statements 9934 data_address_connection_74_decl.
Lemma data_address_connection_74_position : straight_drop 51 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 74 (Gtyp (Fuint 1))) data_address_connection_74_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_74_split : data_address_connection_74_decl = statement_append data_address_connection_74_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 74) (@Eref VarOrder.T (@Eid VarOrder.T 33))) data_address_connection_74_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_74_straight : straight_statements data_address_connection_74_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_74_mid_safe : formal_typed_suffix_safe flat_memories 74 data_address_connection_74_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_74_tail_safe : formal_typed_suffix_safe flat_memories 74 data_address_connection_74_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_74_nonregister : has_register 74 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_74_output invalid old current result :
 (exists ground bits, VM.find 33 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 74 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 51 flat_statements data_address_connection_74_decl data_address_connection_74_mid data_address_connection_74_tail
 74 33 1 ground bits invalid flat_memories old current result
 data_address_connection_74_position data_address_connection_74_split data_address_connection_74_straight data_address_connection_74_mid_safe data_address_connection_74_tail_safe
 data_address_connection_74_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_81_decl := match straight_drop 59 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_81_tail := match straight_drop 9989 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_81_mid := take_statements 9929 data_address_connection_81_decl.
Lemma data_address_connection_81_position : straight_drop 58 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 81 (Gtyp (Fuint 1))) data_address_connection_81_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_81_split : data_address_connection_81_decl = statement_append data_address_connection_81_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 81) (@Eref VarOrder.T (@Eid VarOrder.T 40))) data_address_connection_81_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_81_straight : straight_statements data_address_connection_81_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_81_mid_safe : formal_typed_suffix_safe flat_memories 81 data_address_connection_81_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_81_tail_safe : formal_typed_suffix_safe flat_memories 81 data_address_connection_81_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_81_nonregister : has_register 81 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_81_output invalid old current result :
 (exists ground bits, VM.find 40 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 81 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 58 flat_statements data_address_connection_81_decl data_address_connection_81_mid data_address_connection_81_tail
 81 40 1 ground bits invalid flat_memories old current result
 data_address_connection_81_position data_address_connection_81_split data_address_connection_81_straight data_address_connection_81_mid_safe data_address_connection_81_tail_safe
 data_address_connection_81_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_782_decl := match straight_drop 792 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_782_tail := match straight_drop 1159 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_782_mid := take_statements 366 data_address_connection_782_decl.
Lemma data_address_connection_782_position : straight_drop 791 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 782 (Gtyp (Fuint 32))) data_address_connection_782_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_782_split : data_address_connection_782_decl = statement_append data_address_connection_782_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 782) (@Eref VarOrder.T (@Eid VarOrder.T 917))) data_address_connection_782_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_782_straight : straight_statements data_address_connection_782_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_782_mid_safe : formal_typed_suffix_safe flat_memories 782 data_address_connection_782_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_782_tail_safe : formal_typed_suffix_safe flat_memories 782 data_address_connection_782_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_782_nonregister : has_register 782 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_782_output invalid old current result :
 (exists ground bits, VM.find 917 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 782 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 791 flat_statements data_address_connection_782_decl data_address_connection_782_mid data_address_connection_782_tail
 782 917 32 ground bits invalid flat_memories old current result
 data_address_connection_782_position data_address_connection_782_split data_address_connection_782_straight data_address_connection_782_mid_safe data_address_connection_782_tail_safe
 data_address_connection_782_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_783_decl := match straight_drop 793 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_783_tail := match straight_drop 1160 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_783_mid := take_statements 366 data_address_connection_783_decl.
Lemma data_address_connection_783_position : straight_drop 792 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 783 (Gtyp (Fuint 32))) data_address_connection_783_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_783_split : data_address_connection_783_decl = statement_append data_address_connection_783_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 783) (@Eref VarOrder.T (@Eid VarOrder.T 952))) data_address_connection_783_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_783_straight : straight_statements data_address_connection_783_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_783_mid_safe : formal_typed_suffix_safe flat_memories 783 data_address_connection_783_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_783_tail_safe : formal_typed_suffix_safe flat_memories 783 data_address_connection_783_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_783_nonregister : has_register 783 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_783_output invalid old current result :
 (exists ground bits, VM.find 952 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 783 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 792 flat_statements data_address_connection_783_decl data_address_connection_783_mid data_address_connection_783_tail
 783 952 32 ground bits invalid flat_memories old current result
 data_address_connection_783_position data_address_connection_783_split data_address_connection_783_straight data_address_connection_783_mid_safe data_address_connection_783_tail_safe
 data_address_connection_783_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_8252_decl := match straight_drop 9013 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8252_tail := match straight_drop 9763 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8252_mid := take_statements 749 data_address_connection_8252_decl.
Lemma data_address_connection_8252_position : straight_drop 9012 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8252 (Gtyp (Fuint 1))) data_address_connection_8252_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8252_split : data_address_connection_8252_decl = statement_append data_address_connection_8252_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8252) (@Eref VarOrder.T (@Eid VarOrder.T 8458))) data_address_connection_8252_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8252_straight : straight_statements data_address_connection_8252_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_8252_mid_safe : formal_typed_suffix_safe flat_memories 8252 data_address_connection_8252_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8252_tail_safe : formal_typed_suffix_safe flat_memories 8252 data_address_connection_8252_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8252_nonregister : has_register 8252 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_8252_output invalid old current result :
 (exists ground bits, VM.find 8458 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8252 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9012 flat_statements data_address_connection_8252_decl data_address_connection_8252_mid data_address_connection_8252_tail
 8252 8458 1 ground bits invalid flat_memories old current result
 data_address_connection_8252_position data_address_connection_8252_split data_address_connection_8252_straight data_address_connection_8252_mid_safe data_address_connection_8252_tail_safe
 data_address_connection_8252_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_8253_decl := match straight_drop 9014 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8253_tail := match straight_drop 9764 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8253_mid := take_statements 749 data_address_connection_8253_decl.
Lemma data_address_connection_8253_position : straight_drop 9013 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8253 (Gtyp (Fuint 1))) data_address_connection_8253_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8253_split : data_address_connection_8253_decl = statement_append data_address_connection_8253_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8253) (@Eref VarOrder.T (@Eid VarOrder.T 8507))) data_address_connection_8253_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8253_straight : straight_statements data_address_connection_8253_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_8253_mid_safe : formal_typed_suffix_safe flat_memories 8253 data_address_connection_8253_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8253_tail_safe : formal_typed_suffix_safe flat_memories 8253 data_address_connection_8253_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8253_nonregister : has_register 8253 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_8253_output invalid old current result :
 (exists ground bits, VM.find 8507 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8253 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9013 flat_statements data_address_connection_8253_decl data_address_connection_8253_mid data_address_connection_8253_tail
 8253 8507 1 ground bits invalid flat_memories old current result
 data_address_connection_8253_position data_address_connection_8253_split data_address_connection_8253_straight data_address_connection_8253_mid_safe data_address_connection_8253_tail_safe
 data_address_connection_8253_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_8254_decl := match straight_drop 9015 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8254_tail := match straight_drop 9765 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8254_mid := take_statements 749 data_address_connection_8254_decl.
Lemma data_address_connection_8254_position : straight_drop 9014 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8254 (Gtyp (Fuint 3))) data_address_connection_8254_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8254_split : data_address_connection_8254_decl = statement_append data_address_connection_8254_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8254) (@Eref VarOrder.T (@Eid VarOrder.T 8556))) data_address_connection_8254_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8254_straight : straight_statements data_address_connection_8254_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_8254_mid_safe : formal_typed_suffix_safe flat_memories 8254 data_address_connection_8254_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8254_tail_safe : formal_typed_suffix_safe flat_memories 8254 data_address_connection_8254_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8254_nonregister : has_register 8254 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_8254_output invalid old current result :
 (exists ground bits, VM.find 8556 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8254 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9014 flat_statements data_address_connection_8254_decl data_address_connection_8254_mid data_address_connection_8254_tail
 8254 8556 3 ground bits invalid flat_memories old current result
 data_address_connection_8254_position data_address_connection_8254_split data_address_connection_8254_straight data_address_connection_8254_mid_safe data_address_connection_8254_tail_safe
 data_address_connection_8254_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_8255_decl := match straight_drop 9016 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8255_tail := match straight_drop 9766 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_8255_mid := take_statements 749 data_address_connection_8255_decl.
Lemma data_address_connection_8255_position : straight_drop 9015 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8255 (Gtyp (Fuint 4))) data_address_connection_8255_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8255_split : data_address_connection_8255_decl = statement_append data_address_connection_8255_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8255) (@Eref VarOrder.T (@Eid VarOrder.T 8605))) data_address_connection_8255_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8255_straight : straight_statements data_address_connection_8255_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_8255_mid_safe : formal_typed_suffix_safe flat_memories 8255 data_address_connection_8255_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8255_tail_safe : formal_typed_suffix_safe flat_memories 8255 data_address_connection_8255_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_8255_nonregister : has_register 8255 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_8255_output invalid old current result :
 (exists ground bits, VM.find 8605 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8255 result = Some (Gval (Fuint 4) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9015 flat_statements data_address_connection_8255_decl data_address_connection_8255_mid data_address_connection_8255_tail
 8255 8605 4 ground bits invalid flat_memories old current result
 data_address_connection_8255_position data_address_connection_8255_split data_address_connection_8255_straight data_address_connection_8255_mid_safe data_address_connection_8255_tail_safe
 data_address_connection_8255_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_86_decl := match straight_drop 64 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_86_tail := match straight_drop 9993 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_86_mid := take_statements 9928 data_address_connection_86_decl.
Lemma data_address_connection_86_position : straight_drop 63 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 86 (Gtyp (Fuint 1))) data_address_connection_86_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_86_split : data_address_connection_86_decl = statement_append data_address_connection_86_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 86) (@Eref VarOrder.T (@Eid VarOrder.T 8252))) data_address_connection_86_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_86_straight : straight_statements data_address_connection_86_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_86_mid_safe : formal_typed_suffix_safe flat_memories 86 data_address_connection_86_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_86_tail_safe : formal_typed_suffix_safe flat_memories 86 data_address_connection_86_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_86_nonregister : has_register 86 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_86_output invalid old current result :
 (exists ground bits, VM.find 8252 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 86 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 63 flat_statements data_address_connection_86_decl data_address_connection_86_mid data_address_connection_86_tail
 86 8252 1 ground bits invalid flat_memories old current result
 data_address_connection_86_position data_address_connection_86_split data_address_connection_86_straight data_address_connection_86_mid_safe data_address_connection_86_tail_safe
 data_address_connection_86_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_87_decl := match straight_drop 65 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_87_tail := match straight_drop 9994 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_87_mid := take_statements 9928 data_address_connection_87_decl.
Lemma data_address_connection_87_position : straight_drop 64 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 87 (Gtyp (Fuint 1))) data_address_connection_87_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_87_split : data_address_connection_87_decl = statement_append data_address_connection_87_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 87) (@Eref VarOrder.T (@Eid VarOrder.T 8253))) data_address_connection_87_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_87_straight : straight_statements data_address_connection_87_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_87_mid_safe : formal_typed_suffix_safe flat_memories 87 data_address_connection_87_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_87_tail_safe : formal_typed_suffix_safe flat_memories 87 data_address_connection_87_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_87_nonregister : has_register 87 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_87_output invalid old current result :
 (exists ground bits, VM.find 8253 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 87 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 64 flat_statements data_address_connection_87_decl data_address_connection_87_mid data_address_connection_87_tail
 87 8253 1 ground bits invalid flat_memories old current result
 data_address_connection_87_position data_address_connection_87_split data_address_connection_87_straight data_address_connection_87_mid_safe data_address_connection_87_tail_safe
 data_address_connection_87_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_88_decl := match straight_drop 66 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_88_tail := match straight_drop 9995 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_88_mid := take_statements 9928 data_address_connection_88_decl.
Lemma data_address_connection_88_position : straight_drop 65 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 88 (Gtyp (Fuint 3))) data_address_connection_88_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_88_split : data_address_connection_88_decl = statement_append data_address_connection_88_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 88) (@Eref VarOrder.T (@Eid VarOrder.T 8254))) data_address_connection_88_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_88_straight : straight_statements data_address_connection_88_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_88_mid_safe : formal_typed_suffix_safe flat_memories 88 data_address_connection_88_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_88_tail_safe : formal_typed_suffix_safe flat_memories 88 data_address_connection_88_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_88_nonregister : has_register 88 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_88_output invalid old current result :
 (exists ground bits, VM.find 8254 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 88 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 65 flat_statements data_address_connection_88_decl data_address_connection_88_mid data_address_connection_88_tail
 88 8254 3 ground bits invalid flat_memories old current result
 data_address_connection_88_position data_address_connection_88_split data_address_connection_88_straight data_address_connection_88_mid_safe data_address_connection_88_tail_safe
 data_address_connection_88_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_89_decl := match straight_drop 67 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_89_tail := match straight_drop 9996 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_89_mid := take_statements 9928 data_address_connection_89_decl.
Lemma data_address_connection_89_position : straight_drop 66 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 89 (Gtyp (Fuint 4))) data_address_connection_89_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_89_split : data_address_connection_89_decl = statement_append data_address_connection_89_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 89) (@Eref VarOrder.T (@Eid VarOrder.T 8255))) data_address_connection_89_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_89_straight : straight_statements data_address_connection_89_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_89_mid_safe : formal_typed_suffix_safe flat_memories 89 data_address_connection_89_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_89_tail_safe : formal_typed_suffix_safe flat_memories 89 data_address_connection_89_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_89_nonregister : has_register 89 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_89_output invalid old current result :
 (exists ground bits, VM.find 8255 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 89 result = Some (Gval (Fuint 4) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 66 flat_statements data_address_connection_89_decl data_address_connection_89_mid data_address_connection_89_tail
 89 8255 4 ground bits invalid flat_memories old current result
 data_address_connection_89_position data_address_connection_89_split data_address_connection_89_straight data_address_connection_89_mid_safe data_address_connection_89_tail_safe
 data_address_connection_89_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1153_decl := match straight_drop 1229 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1153_tail := match straight_drop 8841 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1153_mid := take_statements 7611 data_address_connection_1153_decl.
Lemma data_address_connection_1153_position : straight_drop 1228 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1153 (Gtyp (Fuint 4))) data_address_connection_1153_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1153_split : data_address_connection_1153_decl = statement_append data_address_connection_1153_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1153) (@Eref VarOrder.T (@Eid VarOrder.T 89))) data_address_connection_1153_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1153_straight : straight_statements data_address_connection_1153_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1153_mid_safe : formal_typed_suffix_safe flat_memories 1153 data_address_connection_1153_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1153_tail_safe : formal_typed_suffix_safe flat_memories 1153 data_address_connection_1153_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1153_nonregister : has_register 1153 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1153_output invalid old current result :
 (exists ground bits, VM.find 89 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1153 result = Some (Gval (Fuint 4) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1228 flat_statements data_address_connection_1153_decl data_address_connection_1153_mid data_address_connection_1153_tail
 1153 89 4 ground bits invalid flat_memories old current result
 data_address_connection_1153_position data_address_connection_1153_split data_address_connection_1153_straight data_address_connection_1153_mid_safe data_address_connection_1153_tail_safe
 data_address_connection_1153_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1307_decl := match straight_drop 1385 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1307_tail := match straight_drop 8845 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1307_mid := take_statements 7459 data_address_connection_1307_decl.
Lemma data_address_connection_1307_position : straight_drop 1384 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1307 (Gtyp (Fuint 3))) data_address_connection_1307_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1307_split : data_address_connection_1307_decl = statement_append data_address_connection_1307_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1307) (@Eref VarOrder.T (@Eid VarOrder.T 88))) data_address_connection_1307_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1307_straight : straight_statements data_address_connection_1307_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1307_mid_safe : formal_typed_suffix_safe flat_memories 1307 data_address_connection_1307_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1307_tail_safe : formal_typed_suffix_safe flat_memories 1307 data_address_connection_1307_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1307_nonregister : has_register 1307 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1307_output invalid old current result :
 (exists ground bits, VM.find 88 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1307 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1384 flat_statements data_address_connection_1307_decl data_address_connection_1307_mid data_address_connection_1307_tail
 1307 88 3 ground bits invalid flat_memories old current result
 data_address_connection_1307_position data_address_connection_1307_split data_address_connection_1307_straight data_address_connection_1307_mid_safe data_address_connection_1307_tail_safe
 data_address_connection_1307_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1151_decl := match straight_drop 1227 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1151_tail := match straight_drop 8839 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1151_mid := take_statements 7611 data_address_connection_1151_decl.
Lemma data_address_connection_1151_position : straight_drop 1226 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1151 (Gtyp (Fuint 32))) data_address_connection_1151_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1151_split : data_address_connection_1151_decl = statement_append data_address_connection_1151_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1151) (@Eref VarOrder.T (@Eid VarOrder.T 7821))) data_address_connection_1151_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1151_straight : straight_statements data_address_connection_1151_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1151_mid_safe : formal_typed_suffix_safe flat_memories 1151 data_address_connection_1151_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1151_tail_safe : formal_typed_suffix_safe flat_memories 1151 data_address_connection_1151_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1151_nonregister : has_register 1151 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1151_output invalid old current result :
 (exists ground bits, VM.find 7821 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1151 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1226 flat_statements data_address_connection_1151_decl data_address_connection_1151_mid data_address_connection_1151_tail
 1151 7821 32 ground bits invalid flat_memories old current result
 data_address_connection_1151_position data_address_connection_1151_split data_address_connection_1151_straight data_address_connection_1151_mid_safe data_address_connection_1151_tail_safe
 data_address_connection_1151_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1308_decl := match straight_drop 1386 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1308_tail := match straight_drop 1433 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1308_mid := take_statements 46 data_address_connection_1308_decl.
Lemma data_address_connection_1308_position : straight_drop 1385 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1308 (Gtyp (Fuint 32))) data_address_connection_1308_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1308_split : data_address_connection_1308_decl = statement_append data_address_connection_1308_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1308) (@Eref VarOrder.T (@Eid VarOrder.T 1354))) data_address_connection_1308_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1308_straight : straight_statements data_address_connection_1308_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1308_mid_safe : formal_typed_suffix_safe flat_memories 1308 data_address_connection_1308_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1308_tail_safe : formal_typed_suffix_safe flat_memories 1308 data_address_connection_1308_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1308_nonregister : has_register 1308 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1308_output invalid old current result :
 (exists ground bits, VM.find 1354 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1308 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1385 flat_statements data_address_connection_1308_decl data_address_connection_1308_mid data_address_connection_1308_tail
 1308 1354 32 ground bits invalid flat_memories old current result
 data_address_connection_1308_position data_address_connection_1308_split data_address_connection_1308_straight data_address_connection_1308_mid_safe data_address_connection_1308_tail_safe
 data_address_connection_1308_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1152_decl := match straight_drop 1228 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1152_tail := match straight_drop 8840 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1152_mid := take_statements 7611 data_address_connection_1152_decl.
Lemma data_address_connection_1152_position : straight_drop 1227 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1152 (Gtyp (Fuint 32))) data_address_connection_1152_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1152_split : data_address_connection_1152_decl = statement_append data_address_connection_1152_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1152) (@Eref VarOrder.T (@Eid VarOrder.T 7823))) data_address_connection_1152_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1152_straight : straight_statements data_address_connection_1152_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1152_mid_safe : formal_typed_suffix_safe flat_memories 1152 data_address_connection_1152_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1152_tail_safe : formal_typed_suffix_safe flat_memories 1152 data_address_connection_1152_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1152_nonregister : has_register 1152 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1152_output invalid old current result :
 (exists ground bits, VM.find 7823 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1152 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1227 flat_statements data_address_connection_1152_decl data_address_connection_1152_mid data_address_connection_1152_tail
 1152 7823 32 ground bits invalid flat_memories old current result
 data_address_connection_1152_position data_address_connection_1152_split data_address_connection_1152_straight data_address_connection_1152_mid_safe data_address_connection_1152_tail_safe
 data_address_connection_1152_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_1155_decl := match straight_drop 1231 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1155_tail := match straight_drop 1381 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_1155_mid := take_statements 149 data_address_connection_1155_decl.
Lemma data_address_connection_1155_position : straight_drop 1230 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1155 (Gtyp (Fuint 32))) data_address_connection_1155_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1155_split : data_address_connection_1155_decl = statement_append data_address_connection_1155_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1155) (@Eref VarOrder.T (@Eid VarOrder.T 1161))) data_address_connection_1155_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1155_straight : straight_statements data_address_connection_1155_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_1155_mid_safe : formal_typed_suffix_safe flat_memories 1155 data_address_connection_1155_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1155_tail_safe : formal_typed_suffix_safe flat_memories 1155 data_address_connection_1155_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_1155_nonregister : has_register 1155 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_1155_output invalid old current result :
 (exists ground bits, VM.find 1161 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1155 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 1230 flat_statements data_address_connection_1155_decl data_address_connection_1155_mid data_address_connection_1155_tail
 1155 1161 32 ground bits invalid flat_memories old current result
 data_address_connection_1155_position data_address_connection_1155_split data_address_connection_1155_straight data_address_connection_1155_mid_safe data_address_connection_1155_tail_safe
 data_address_connection_1155_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_address_connection_37_decl := match straight_drop 15 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_37_tail := match straight_drop 9958 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_address_connection_37_mid := take_statements 9942 data_address_connection_37_decl.
Lemma data_address_connection_37_position : straight_drop 14 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 37 (Gtyp (Fuint 32))) data_address_connection_37_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_37_split : data_address_connection_37_decl = statement_append data_address_connection_37_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 37) (@Eref VarOrder.T (@Eid VarOrder.T 78))) data_address_connection_37_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_address_connection_37_straight : straight_statements data_address_connection_37_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_address_connection_37_mid_safe : formal_typed_suffix_safe flat_memories 37 data_address_connection_37_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_37_tail_safe : formal_typed_suffix_safe flat_memories 37 data_address_connection_37_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_address_connection_37_nonregister : has_register 37 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_address_connection_37_output invalid old current result :
 (exists ground bits, VM.find 78 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 37 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 14 flat_statements data_address_connection_37_decl data_address_connection_37_mid data_address_connection_37_tail
 37 78 32 ground bits invalid flat_memories old current result
 data_address_connection_37_position data_address_connection_37_split data_address_connection_37_straight data_address_connection_37_mid_safe data_address_connection_37_tail_safe
 data_address_connection_37_nonregister (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions data_address_connection_37_output.
