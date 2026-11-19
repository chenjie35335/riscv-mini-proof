Require Import CoreSocModel ComparisonNodes FormalReferenceValid FormalDeclaredConnectionCongruence FormalCheckerValidStability.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma reference_valid_1517_congruent invalid left right next_left next_right :
 VM.find 1395 left = VM.find 1395 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1517 next_left = VM.find 1517 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1596 flat_statements reference_valid_decl_1517 reference_valid_mid_1517 reference_valid_tail_1517
 1517 1395 1 invalid flat_memories left right next_left next_right
 reference_valid_position_1517 reference_valid_split_1517 reference_valid_straight_1517 reference_valid_mid_safe_1517 reference_valid_tail_safe_1517
 reference_valid_nonregister_1517 (Logic.eq_refl _) Equal Left Right).
Qed.
Lemma reference_valid_1707_congruent invalid left right next_left next_right :
 VM.find 1517 left = VM.find 1517 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1707 next_left = VM.find 1707 next_right.
Proof.
 intros Equal Left Right.
 exact (declared_connection_congruence 1786 flat_statements reference_valid_decl_1707 reference_valid_mid_1707 reference_valid_tail_1707
 1707 1517 1 invalid flat_memories left right next_left next_right
 reference_valid_position_1707 reference_valid_split_1707 reference_valid_straight_1707 reference_valid_mid_safe_1707 reference_valid_tail_safe_1707
 reference_valid_nonregister_1707 (Logic.eq_refl _) Equal Left Right).
Qed.
Theorem reference_valid_history_stable invalid history limit j k bit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 (Nat.add j 14 <= limit)%coq_nat -> (Nat.add k 14 <= limit)%coq_nat ->
 VM.find 1707 (history (Nat.add j 14)) = VM.find 1707 (history (Nat.add k 14)).
Proof.
 intros Steps Resets J K.
 assert (Step13 : forall p, (Nat.add p 14 <= limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history (Nat.add p 12)) false (history (Nat.add p 12)) flat_statements = Some (history (Nat.add p 13))).
 { intros p Bound. replace (Nat.add p 13) with (S (Nat.add p 12)) by lia. apply Steps. lia. }
 assert (Step14 : forall p, (Nat.add p 14 <= limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history (Nat.add p 13)) false (history (Nat.add p 13)) flat_statements = Some (history (Nat.add p 14))).
 { intros p Bound. replace (Nat.add p 14) with (S (Nat.add p 13)) by lia. apply Steps. lia. }
 apply (reference_valid_1707_congruent invalid
 (history (Nat.add j 13)) (history (Nat.add k 13)) (history (Nat.add j 14)) (history (Nat.add k 14))).
 - apply (reference_valid_1517_congruent invalid
   (history (Nat.add j 12)) (history (Nat.add k 12)) (history (Nat.add j 13)) (history (Nat.add k 13))).
   + apply (checker_valid_history_stable invalid history limit j k bit Steps Resets); lia.
   + exact (Step13 j J).
   + exact (Step13 k K).
 - exact (Step14 j J).
 - exact (Step14 k K).
Qed.
Print Assumptions reference_valid_history_stable.
