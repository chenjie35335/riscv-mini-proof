Require Import CoreSocModel ComparisonNodes FormalDeclaredConnectionCongruence X0RegisterInputConnections FormalExceptionInput.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_wire_118_congruent invalid left right next_left next_right :
 VM.find 7758 left = VM.find 7758 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 118 next_left = VM.find 118 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 95 flat_statements x0_register_input_decl_118 x0_register_input_mid_118 x0_register_input_tail_118
 118 7758 3 invalid flat_memories left right next_left next_right
 x0_register_input_position_118 x0_register_input_split_118 x0_register_input_straight_118 x0_register_input_mid_safe_118 x0_register_input_tail_safe_118
 x0_register_input_nonregister_118 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_122_congruent invalid left right next_left next_right :
 VM.find 7752 left = VM.find 7752 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 122 next_left = VM.find 122 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 99 flat_statements x0_register_input_decl_122 x0_register_input_mid_122 x0_register_input_tail_122
 122 7752 32 invalid flat_memories left right next_left next_right
 x0_register_input_position_122 x0_register_input_split_122 x0_register_input_straight_122 x0_register_input_mid_safe_122 x0_register_input_tail_safe_122
 x0_register_input_nonregister_122 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_123_congruent invalid left right next_left next_right :
 VM.find 7750 left = VM.find 7750 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 123 next_left = VM.find 123 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 100 flat_statements x0_register_input_decl_123 x0_register_input_mid_123 x0_register_input_tail_123
 123 7750 32 invalid flat_memories left right next_left next_right
 x0_register_input_position_123 x0_register_input_split_123 x0_register_input_straight_123 x0_register_input_mid_safe_123 x0_register_input_tail_safe_123
 x0_register_input_nonregister_123 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_124_congruent invalid left right next_left next_right :
 VM.find 7759 left = VM.find 7759 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 124 next_left = VM.find 124 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 101 flat_statements x0_register_input_decl_124 x0_register_input_mid_124 x0_register_input_tail_124
 124 7759 1 invalid flat_memories left right next_left next_right
 x0_register_input_position_124 x0_register_input_split_124 x0_register_input_straight_124 x0_register_input_mid_safe_124 x0_register_input_tail_safe_124
 x0_register_input_nonregister_124 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_125_congruent invalid left right next_left next_right :
 VM.find 7754 left = VM.find 7754 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 125 next_left = VM.find 125 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 102 flat_statements x0_register_input_decl_125 x0_register_input_mid_125 x0_register_input_tail_125
 125 7754 2 invalid flat_memories left right next_left next_right
 x0_register_input_position_125 x0_register_input_split_125 x0_register_input_straight_125 x0_register_input_mid_safe_125 x0_register_input_tail_safe_125
 x0_register_input_nonregister_125 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_126_congruent invalid left right next_left next_right :
 VM.find 7755 left = VM.find 7755 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 126 next_left = VM.find 126 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 103 flat_statements x0_register_input_decl_126 x0_register_input_mid_126 x0_register_input_tail_126
 126 7755 3 invalid flat_memories left right next_left next_right
 x0_register_input_position_126 x0_register_input_split_126 x0_register_input_straight_126 x0_register_input_mid_safe_126 x0_register_input_tail_safe_126
 x0_register_input_nonregister_126 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_127_congruent invalid left right next_left next_right :
 VM.find 7760 left = VM.find 7760 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 127 next_left = VM.find 127 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 104 flat_statements x0_register_input_decl_127 x0_register_input_mid_127 x0_register_input_tail_127
 127 7760 1 invalid flat_memories left right next_left next_right
 x0_register_input_position_127 x0_register_input_split_127 x0_register_input_straight_127 x0_register_input_mid_safe_127 x0_register_input_tail_safe_127
 x0_register_input_nonregister_127 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem exception_wire_128_congruent invalid left right next_left next_right :
 VM.find 442 left = VM.find 442 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 128 next_left = VM.find 128 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 105 flat_statements exception_input_decl_128 exception_input_mid_128 exception_input_tail_128
 128 442 1 invalid flat_memories left right next_left next_right
 exception_input_position_128 exception_input_split_128 exception_input_straight_128 exception_input_mid_safe_128 exception_input_tail_safe_128
 exception_input_nonregister_128 (Logic.eq_refl _) Equal Left Right).
Qed.
Print Assumptions exception_wire_128_congruent.
