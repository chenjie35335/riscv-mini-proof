Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalLegalObservation FormalResetPreparation FormalTopResetHold StagedIterationCount LegalNoTrapWindow.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma legal_local_reset_history invalid history limit bit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::bit]) ->
 forall time, (time <= limit)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Steps Reset time. induction time as [|time IH]; intro Bound; [exact Reset|].
 eapply top_reset_iteration; [apply IH; lia|apply Steps; lia].
Qed.
Theorem observed_legal_no_trap_history memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists committed initial history,
 generated_run memory inputs k = Some committed /\
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k)) = Some initial /\
 history 0%nat = top_environment initial /\ history 9259%nat = top_environment states /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) /\
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset.
 pose proof Observe as Expanded. unfold generated_observe, generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare; [|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial states Expanded)
 as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last.
   destruct (legal_observation_assumptions memory inputs k states Legal Observe) as [_ Assume].
   apply (proj1 (flat_assumption_at_top states)) in Assume.
   unfold top_environment. destruct (SVM.find nil states); [exact Assume|contradiction]. }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps); try (vm_compute; lia).
   - apply (legal_local_reset_history _ history 9259 false Steps Reset0). vm_compute; lia.
   - exact LocalAssume. }
 exists committed, initial, history. repeat split; assumption.
Qed.
Print Assumptions observed_legal_no_trap_history.
