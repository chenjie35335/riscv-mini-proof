Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection FormalDeclaredConcreteUnaryConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_writer_connection_8257_decl := match straight_drop 9018 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_8257_tail := match straight_drop 9768 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_8257_mid := take_statements 749 data_writer_connection_8257_decl.
Lemma data_writer_connection_8257_position : straight_drop 9017 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8257 (Gtyp (Fuint 2))) data_writer_connection_8257_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8257_split : data_writer_connection_8257_decl = statement_append data_writer_connection_8257_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8257) (@Eref VarOrder.T (@Eid VarOrder.T 8752))) data_writer_connection_8257_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8257_straight : straight_statements data_writer_connection_8257_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_8257_mid_safe : formal_typed_suffix_safe flat_memories 8257 data_writer_connection_8257_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8257_tail_safe : formal_typed_suffix_safe flat_memories 8257 data_writer_connection_8257_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8257_nonregister : has_register 8257 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_8257_output invalid old current result :
 (exists ground bits, VM.find 8752 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8257 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9017 flat_statements data_writer_connection_8257_decl data_writer_connection_8257_mid data_writer_connection_8257_tail
 8257 8752 2 ground bits invalid flat_memories old current result
 data_writer_connection_8257_position data_writer_connection_8257_split data_writer_connection_8257_straight data_writer_connection_8257_mid_safe data_writer_connection_8257_tail_safe
 data_writer_connection_8257_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_8258_decl := match straight_drop 9019 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_8258_tail := match straight_drop 9769 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_8258_mid := take_statements 749 data_writer_connection_8258_decl.
Lemma data_writer_connection_8258_position : straight_drop 9018 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 8258 (Gtyp (Fuint 3))) data_writer_connection_8258_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8258_split : data_writer_connection_8258_decl = statement_append data_writer_connection_8258_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8258) (@Eref VarOrder.T (@Eid VarOrder.T 8801))) data_writer_connection_8258_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8258_straight : straight_statements data_writer_connection_8258_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_8258_mid_safe : formal_typed_suffix_safe flat_memories 8258 data_writer_connection_8258_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8258_tail_safe : formal_typed_suffix_safe flat_memories 8258 data_writer_connection_8258_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_8258_nonregister : has_register 8258 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_8258_output invalid old current result :
 (exists ground bits, VM.find 8801 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8258 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 9018 flat_statements data_writer_connection_8258_decl data_writer_connection_8258_mid data_writer_connection_8258_tail
 8258 8801 3 ground bits invalid flat_memories old current result
 data_writer_connection_8258_position data_writer_connection_8258_split data_writer_connection_8258_straight data_writer_connection_8258_mid_safe data_writer_connection_8258_tail_safe
 data_writer_connection_8258_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_91_decl := match straight_drop 69 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_91_tail := match straight_drop 9998 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_91_mid := take_statements 9928 data_writer_connection_91_decl.
Lemma data_writer_connection_91_position : straight_drop 68 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 91 (Gtyp (Fuint 2))) data_writer_connection_91_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_91_split : data_writer_connection_91_decl = statement_append data_writer_connection_91_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 91) (@Eref VarOrder.T (@Eid VarOrder.T 8257))) data_writer_connection_91_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_91_straight : straight_statements data_writer_connection_91_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_91_mid_safe : formal_typed_suffix_safe flat_memories 91 data_writer_connection_91_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_91_tail_safe : formal_typed_suffix_safe flat_memories 91 data_writer_connection_91_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_91_nonregister : has_register 91 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_91_output invalid old current result :
 (exists ground bits, VM.find 8257 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 91 result = Some (Gval (Fuint 2) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 68 flat_statements data_writer_connection_91_decl data_writer_connection_91_mid data_writer_connection_91_tail
 91 8257 2 ground bits invalid flat_memories old current result
 data_writer_connection_91_position data_writer_connection_91_split data_writer_connection_91_straight data_writer_connection_91_mid_safe data_writer_connection_91_tail_safe
 data_writer_connection_91_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_92_decl := match straight_drop 70 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_92_tail := match straight_drop 9999 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_92_mid := take_statements 9928 data_writer_connection_92_decl.
Lemma data_writer_connection_92_position : straight_drop 69 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 92 (Gtyp (Fuint 3))) data_writer_connection_92_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_92_split : data_writer_connection_92_decl = statement_append data_writer_connection_92_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 92) (@Eref VarOrder.T (@Eid VarOrder.T 8258))) data_writer_connection_92_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_92_straight : straight_statements data_writer_connection_92_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_92_mid_safe : formal_typed_suffix_safe flat_memories 92 data_writer_connection_92_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_92_tail_safe : formal_typed_suffix_safe flat_memories 92 data_writer_connection_92_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_92_nonregister : has_register 92 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_92_output invalid old current result :
 (exists ground bits, VM.find 8258 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 92 result = Some (Gval (Fuint 3) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 69 flat_statements data_writer_connection_92_decl data_writer_connection_92_mid data_writer_connection_92_tail
 92 8258 3 ground bits invalid flat_memories old current result
 data_writer_connection_92_position data_writer_connection_92_split data_writer_connection_92_straight data_writer_connection_92_mid_safe data_writer_connection_92_tail_safe
 data_writer_connection_92_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_77_decl := match straight_drop 55 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_77_tail := match straight_drop 8761 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_77_mid := take_statements 8705 data_writer_connection_77_decl.
Lemma data_writer_connection_77_position : straight_drop 54 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 77 (Gtyp (Fuint 1))) data_writer_connection_77_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_77_split : data_writer_connection_77_decl = statement_append data_writer_connection_77_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 77) (@Eref VarOrder.T (@Eid VarOrder.T 7836))) data_writer_connection_77_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_77_straight : straight_statements data_writer_connection_77_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_77_mid_safe : formal_typed_suffix_safe flat_memories 77 data_writer_connection_77_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_77_tail_safe : formal_typed_suffix_safe flat_memories 77 data_writer_connection_77_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_77_nonregister : has_register 77 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_77_output invalid old current result :
 (exists ground bits, VM.find 7836 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 77 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 54 flat_statements data_writer_connection_77_decl data_writer_connection_77_mid data_writer_connection_77_tail
 77 7836 1 ground bits invalid flat_memories old current result
 data_writer_connection_77_position data_writer_connection_77_split data_writer_connection_77_straight data_writer_connection_77_mid_safe data_writer_connection_77_tail_safe
 data_writer_connection_77_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_36_decl := match straight_drop 14 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_36_tail := match straight_drop 9957 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_36_mid := take_statements 9942 data_writer_connection_36_decl.
Lemma data_writer_connection_36_position : straight_drop 13 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 36 (Gtyp (Fuint 1))) data_writer_connection_36_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_36_split : data_writer_connection_36_decl = statement_append data_writer_connection_36_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 36) (@Eref VarOrder.T (@Eid VarOrder.T 77))) data_writer_connection_36_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_36_straight : straight_statements data_writer_connection_36_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_36_mid_safe : formal_typed_suffix_safe flat_memories 36 data_writer_connection_36_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_36_tail_safe : formal_typed_suffix_safe flat_memories 36 data_writer_connection_36_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_36_nonregister : has_register 36 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_36_output invalid old current result :
 (exists ground bits, VM.find 77 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 36 result = Some (Gval (Fuint 1) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 13 flat_statements data_writer_connection_36_decl data_writer_connection_36_mid data_writer_connection_36_tail
 36 77 1 ground bits invalid flat_memories old current result
 data_writer_connection_36_position data_writer_connection_36_split data_writer_connection_36_straight data_writer_connection_36_mid_safe data_writer_connection_36_tail_safe
 data_writer_connection_36_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_79_decl := match straight_drop 57 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_79_tail := match straight_drop 8763 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_79_mid := take_statements 8705 data_writer_connection_79_decl.
Lemma data_writer_connection_79_position : straight_drop 56 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 79 (Gtyp (Fuint 32))) data_writer_connection_79_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_79_split : data_writer_connection_79_decl = statement_append data_writer_connection_79_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 79) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7837)))) data_writer_connection_79_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_79_straight : straight_statements data_writer_connection_79_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_79_mid_safe : formal_typed_suffix_safe flat_memories 79 data_writer_connection_79_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_79_tail_safe : formal_typed_suffix_safe flat_memories 79 data_writer_connection_79_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_79_nonregister : has_register 79 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_79_output invalid old current result :
 (exists ground bits, VM.find 7837 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 79 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_unary_connection_concrete 56 flat_statements data_writer_connection_79_decl data_writer_connection_79_mid data_writer_connection_79_tail
 79 7837 (Uextr 31 0) 32 ground bits invalid flat_memories old current result
 data_writer_connection_79_position data_writer_connection_79_split data_writer_connection_79_straight data_writer_connection_79_mid_safe data_writer_connection_79_tail_safe
 data_writer_connection_79_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_80_decl := match straight_drop 58 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_80_tail := match straight_drop 8764 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_80_mid := take_statements 8705 data_writer_connection_80_decl.
Lemma data_writer_connection_80_position : straight_drop 57 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 80 (Gtyp (Fuint 4))) data_writer_connection_80_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_80_split : data_writer_connection_80_decl = statement_append data_writer_connection_80_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 80) (@Eprim_unop VarOrder.T (Uextr 3 0) (@Eref VarOrder.T (@Eid VarOrder.T 7848)))) data_writer_connection_80_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_80_straight : straight_statements data_writer_connection_80_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_80_mid_safe : formal_typed_suffix_safe flat_memories 80 data_writer_connection_80_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_80_tail_safe : formal_typed_suffix_safe flat_memories 80 data_writer_connection_80_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_80_nonregister : has_register 80 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_80_output invalid old current result :
 (exists ground bits, VM.find 7848 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 80 result = Some (Gval (Fuint 4) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_unary_connection_concrete 57 flat_statements data_writer_connection_80_decl data_writer_connection_80_mid data_writer_connection_80_tail
 80 7848 (Uextr 3 0) 4 ground bits invalid flat_memories old current result
 data_writer_connection_80_position data_writer_connection_80_split data_writer_connection_80_straight data_writer_connection_80_mid_safe data_writer_connection_80_tail_safe
 data_writer_connection_80_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_38_decl := match straight_drop 16 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_38_tail := match straight_drop 9959 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_38_mid := take_statements 9942 data_writer_connection_38_decl.
Lemma data_writer_connection_38_position : straight_drop 15 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 38 (Gtyp (Fuint 32))) data_writer_connection_38_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_38_split : data_writer_connection_38_decl = statement_append data_writer_connection_38_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 38) (@Eref VarOrder.T (@Eid VarOrder.T 79))) data_writer_connection_38_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_38_straight : straight_statements data_writer_connection_38_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_38_mid_safe : formal_typed_suffix_safe flat_memories 38 data_writer_connection_38_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_38_tail_safe : formal_typed_suffix_safe flat_memories 38 data_writer_connection_38_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_38_nonregister : has_register 38 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_38_output invalid old current result :
 (exists ground bits, VM.find 79 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 38 result = Some (Gval (Fuint 32) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 15 flat_statements data_writer_connection_38_decl data_writer_connection_38_mid data_writer_connection_38_tail
 38 79 32 ground bits invalid flat_memories old current result
 data_writer_connection_38_position data_writer_connection_38_split data_writer_connection_38_straight data_writer_connection_38_mid_safe data_writer_connection_38_tail_safe
 data_writer_connection_38_nonregister (Logic.eq_refl _) Source Step).
Qed.
Definition data_writer_connection_39_decl := match straight_drop 17 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_39_tail := match straight_drop 9960 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_writer_connection_39_mid := take_statements 9942 data_writer_connection_39_decl.
Lemma data_writer_connection_39_position : straight_drop 16 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 39 (Gtyp (Fuint 4))) data_writer_connection_39_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_39_split : data_writer_connection_39_decl = statement_append data_writer_connection_39_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 39) (@Eref VarOrder.T (@Eid VarOrder.T 80))) data_writer_connection_39_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_39_straight : straight_statements data_writer_connection_39_mid.
Proof. vm_compute. exact I. Qed.
Lemma data_writer_connection_39_mid_safe : formal_typed_suffix_safe flat_memories 39 data_writer_connection_39_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_39_tail_safe : formal_typed_suffix_safe flat_memories 39 data_writer_connection_39_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_writer_connection_39_nonregister : has_register 39 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_connection_39_output invalid old current result :
 (exists ground bits, VM.find 80 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 39 result = Some (Gval (Fuint 4) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact (declared_connection_concrete 16 flat_statements data_writer_connection_39_decl data_writer_connection_39_mid data_writer_connection_39_tail
 39 80 4 ground bits invalid flat_memories old current result
 data_writer_connection_39_position data_writer_connection_39_split data_writer_connection_39_straight data_writer_connection_39_mid_safe data_writer_connection_39_tail_safe
 data_writer_connection_39_nonregister (Logic.eq_refl _) Source Step).
Qed.
Print Assumptions data_writer_connection_39_output.
