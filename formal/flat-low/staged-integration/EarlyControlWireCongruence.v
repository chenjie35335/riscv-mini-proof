Require Import CoreSocModel ComparisonNodes FormalDeclaredConnectionCongruence DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem early_control_wire_83_congruent invalid left right next_left next_right :
 VM.find 7748 left = VM.find 7748 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 83 next_left = VM.find 83 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 60 flat_statements data_address_connection_83_decl data_address_connection_83_mid data_address_connection_83_tail
 83 7748 32 invalid flat_memories left right next_left next_right
 data_address_connection_83_position data_address_connection_83_split data_address_connection_83_straight data_address_connection_83_mid_safe data_address_connection_83_tail_safe
 data_address_connection_83_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_83_output invalid old current result :
 (exists ground bits, VM.find 7748 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 83 result = Some (Gval (Fuint 32) bits).
Proof. exact (data_address_connection_83_output invalid old current result). Qed.
Theorem early_control_wire_780_congruent invalid left right next_left next_right :
 VM.find 7803 left = VM.find 7803 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 780 next_left = VM.find 780 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 789 flat_statements data_address_connection_780_decl data_address_connection_780_mid data_address_connection_780_tail
 780 7803 5 invalid flat_memories left right next_left next_right
 data_address_connection_780_position data_address_connection_780_split data_address_connection_780_straight data_address_connection_780_mid_safe data_address_connection_780_tail_safe
 data_address_connection_780_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_780_output invalid old current result :
 (exists ground bits, VM.find 7803 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 780 result = Some (Gval (Fuint 5) bits).
Proof. exact (data_address_connection_780_output invalid old current result). Qed.
Theorem early_control_wire_781_congruent invalid left right next_left next_right :
 VM.find 7804 left = VM.find 7804 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 781 next_left = VM.find 781 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 790 flat_statements data_address_connection_781_decl data_address_connection_781_mid data_address_connection_781_tail
 781 7804 5 invalid flat_memories left right next_left next_right
 data_address_connection_781_position data_address_connection_781_split data_address_connection_781_straight data_address_connection_781_mid_safe data_address_connection_781_tail_safe
 data_address_connection_781_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_781_output invalid old current result :
 (exists ground bits, VM.find 7804 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 781 result = Some (Gval (Fuint 5) bits).
Proof. exact (data_address_connection_781_output invalid old current result). Qed.
Theorem early_control_wire_8249_congruent invalid left right next_left next_right :
 VM.find 83 left = VM.find 83 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 8249 next_left = VM.find 8249 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 9009 flat_statements data_address_connection_8249_decl data_address_connection_8249_mid data_address_connection_8249_tail
 8249 83 32 invalid flat_memories left right next_left next_right
 data_address_connection_8249_position data_address_connection_8249_split data_address_connection_8249_straight data_address_connection_8249_mid_safe data_address_connection_8249_tail_safe
 data_address_connection_8249_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_8249_output invalid old current result :
 (exists ground bits, VM.find 83 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8249 result = Some (Gval (Fuint 32) bits).
Proof. exact (data_address_connection_8249_output invalid old current result). Qed.
Theorem early_control_wire_782_congruent invalid left right next_left next_right :
 VM.find 917 left = VM.find 917 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 782 next_left = VM.find 782 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 791 flat_statements data_address_connection_782_decl data_address_connection_782_mid data_address_connection_782_tail
 782 917 32 invalid flat_memories left right next_left next_right
 data_address_connection_782_position data_address_connection_782_split data_address_connection_782_straight data_address_connection_782_mid_safe data_address_connection_782_tail_safe
 data_address_connection_782_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_782_output invalid old current result :
 (exists ground bits, VM.find 917 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 782 result = Some (Gval (Fuint 32) bits).
Proof. exact (data_address_connection_782_output invalid old current result). Qed.
Theorem early_control_wire_783_congruent invalid left right next_left next_right :
 VM.find 952 left = VM.find 952 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 783 next_left = VM.find 783 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 792 flat_statements data_address_connection_783_decl data_address_connection_783_mid data_address_connection_783_tail
 783 952 32 invalid flat_memories left right next_left next_right
 data_address_connection_783_position data_address_connection_783_split data_address_connection_783_straight data_address_connection_783_mid_safe data_address_connection_783_tail_safe
 data_address_connection_783_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_783_output invalid old current result :
 (exists ground bits, VM.find 952 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 783 result = Some (Gval (Fuint 32) bits).
Proof. exact (data_address_connection_783_output invalid old current result). Qed.
Theorem early_control_wire_1357_congruent invalid left right next_left next_right :
 VM.find 7816 left = VM.find 7816 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1357 next_left = VM.find 1357 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1435 flat_statements joint_update_connection_1357_decl joint_update_connection_1357_mid joint_update_connection_1357_tail
 1357 7816 32 invalid flat_memories left right next_left next_right
 joint_update_connection_1357_position joint_update_connection_1357_split joint_update_connection_1357_straight joint_update_connection_1357_mid_safe joint_update_connection_1357_tail_safe
 joint_update_connection_1357_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_1357_output invalid old current result :
 (exists ground bits, VM.find 7816 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1357 result = Some (Gval (Fuint 32) bits).
Proof. exact (joint_update_connection_1357_output invalid old current result). Qed.
Theorem early_control_wire_1358_congruent invalid left right next_left next_right :
 VM.find 7819 left = VM.find 7819 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1358 next_left = VM.find 1358 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1436 flat_statements joint_update_connection_1358_decl joint_update_connection_1358_mid joint_update_connection_1358_tail
 1358 7819 32 invalid flat_memories left right next_left next_right
 joint_update_connection_1358_position joint_update_connection_1358_split joint_update_connection_1358_straight joint_update_connection_1358_mid_safe joint_update_connection_1358_tail_safe
 joint_update_connection_1358_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_1358_output invalid old current result :
 (exists ground bits, VM.find 7819 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1358 result = Some (Gval (Fuint 32) bits).
Proof. exact (joint_update_connection_1358_output invalid old current result). Qed.
Theorem early_control_wire_8256_congruent invalid left right next_left next_right :
 VM.find 8654 left = VM.find 8654 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 8256 next_left = VM.find 8256 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 9016 flat_statements joint_update_connection_8256_decl joint_update_connection_8256_mid joint_update_connection_8256_tail
 8256 8654 3 invalid flat_memories left right next_left next_right
 joint_update_connection_8256_position joint_update_connection_8256_split joint_update_connection_8256_straight joint_update_connection_8256_mid_safe joint_update_connection_8256_tail_safe
 joint_update_connection_8256_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_8256_output invalid old current result :
 (exists ground bits, VM.find 8654 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8256 result = Some (Gval (Fuint 3) bits).
Proof. exact (joint_update_connection_8256_output invalid old current result). Qed.
Theorem early_control_wire_90_congruent invalid left right next_left next_right :
 VM.find 8256 left = VM.find 8256 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 90 next_left = VM.find 90 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 67 flat_statements joint_update_connection_90_decl joint_update_connection_90_mid joint_update_connection_90_tail
 90 8256 3 invalid flat_memories left right next_left next_right
 joint_update_connection_90_position joint_update_connection_90_split joint_update_connection_90_straight joint_update_connection_90_mid_safe joint_update_connection_90_tail_safe
 joint_update_connection_90_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_90_output invalid old current result :
 (exists ground bits, VM.find 8256 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 90 result = Some (Gval (Fuint 3) bits).
Proof. exact (joint_update_connection_90_output invalid old current result). Qed.
Theorem early_control_wire_8251_congruent invalid left right next_left next_right :
 VM.find 8998 left = VM.find 8998 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 8251 next_left = VM.find 8251 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 9011 flat_statements joint_update_connection_8251_decl joint_update_connection_8251_mid joint_update_connection_8251_tail
 8251 8998 1 invalid flat_memories left right next_left next_right
 joint_update_connection_8251_position joint_update_connection_8251_split joint_update_connection_8251_straight joint_update_connection_8251_mid_safe joint_update_connection_8251_tail_safe
 joint_update_connection_8251_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_8251_output invalid old current result :
 (exists ground bits, VM.find 8998 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 8251 result = Some (Gval (Fuint 1) bits).
Proof. exact (joint_update_connection_8251_output invalid old current result). Qed.
Theorem early_control_wire_85_congruent invalid left right next_left next_right :
 VM.find 8251 left = VM.find 8251 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 85 next_left = VM.find 85 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 62 flat_statements joint_update_connection_85_decl joint_update_connection_85_mid joint_update_connection_85_tail
 85 8251 1 invalid flat_memories left right next_left next_right
 joint_update_connection_85_position joint_update_connection_85_split joint_update_connection_85_straight joint_update_connection_85_mid_safe joint_update_connection_85_tail_safe
 joint_update_connection_85_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_85_output invalid old current result :
 (exists ground bits, VM.find 8251 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 85 result = Some (Gval (Fuint 1) bits).
Proof. exact (joint_update_connection_85_output invalid old current result). Qed.
Theorem early_control_wire_1359_congruent invalid left right next_left next_right :
 VM.find 90 left = VM.find 90 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1359 next_left = VM.find 1359 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1437 flat_statements joint_update_connection_1359_decl joint_update_connection_1359_mid joint_update_connection_1359_tail
 1359 90 3 invalid flat_memories left right next_left next_right
 joint_update_connection_1359_position joint_update_connection_1359_split joint_update_connection_1359_straight joint_update_connection_1359_mid_safe joint_update_connection_1359_tail_safe
 joint_update_connection_1359_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_1359_output invalid old current result :
 (exists ground bits, VM.find 90 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1359 result = Some (Gval (Fuint 3) bits).
Proof. exact (joint_update_connection_1359_output invalid old current result). Qed.
Theorem early_control_wire_1360_congruent invalid left right next_left next_right :
 VM.find 1392 left = VM.find 1392 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1360 next_left = VM.find 1360 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1438 flat_statements joint_update_connection_1360_decl joint_update_connection_1360_mid joint_update_connection_1360_tail
 1360 1392 1 invalid flat_memories left right next_left next_right
 joint_update_connection_1360_position joint_update_connection_1360_split joint_update_connection_1360_straight joint_update_connection_1360_mid_safe joint_update_connection_1360_tail_safe
 joint_update_connection_1360_nonregister (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem early_control_wire_1360_output invalid old current result :
 (exists ground bits, VM.find 1392 old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find 1360 result = Some (Gval (Fuint 1) bits).
Proof. exact (joint_update_connection_1360_output invalid old current result). Qed.
Print Assumptions early_control_wire_85_congruent.
Print Assumptions early_control_wire_1360_congruent.
Print Assumptions early_control_wire_1360_output.
