Require Import ExceptionInstructionWindow ExceptionInstructionNonzeroAgreement.
Require Import CoreSocModel ComparisonNodes ComparisonTruth FormalLocalHistory ExceptionInstructionAgreement.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem exception_instruction_nonzero_window_agreement invalid history limit start bits :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (Nat.add start 11 <= limit)%coq_nat ->
 size bits = 32%nat ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) bits) ->
 VM.find 1707 (history (Nat.add start 3)) = Some (Gval (Fuint 1) [::true]) ->
 (exists cw cb, VM.find 6780 (history (Nat.add start 6)) = Some (Gval (Fuint cw) cb) /\ is_zero cb = false) ->
 VM.find 1707 (history (Nat.add start 7)) = Some (Gval (Fuint 1) [::true]) ->
 comparison_inputs_agree (history (Nat.add start 11)) 1473 1671.
Proof.
 intros Steps Bound Size Source Valid3 Raise6 Valid7.
 set (h := fun j => history (Nat.add start j)).
 assert (LocalSteps : forall j, (j < 11)%coq_nat -> formal_flat_local_step invalid (h j) (h (S j))).
 { intros j Small. unfold h. rewrite Nat.add_succ_r. apply Steps. lia. }
 assert (Source0 : VM.find 7750 (h 0%nat) = Some (Gval (Fuint 32) bits)).
 { unfold h. rewrite Nat.add_0_r.
   rewrite (exception_instruction_history_hold invalid history limit Steps start ltac:(lia)). exact Source. }
 apply (exception_instruction_nonzero_agreement_after_eleven invalid
  (h 0%nat) (h 1%nat) (h 2%nat) (h 3%nat) (h 4%nat) (h 5%nat)
  (h 6%nat) (h 7%nat) (h 8%nat) (h 9%nat) (h 10%nat) (h 11%nat) bits);
 try assumption; apply LocalSteps; lia.
Qed.
Print Assumptions exception_instruction_nonzero_window_agreement.
