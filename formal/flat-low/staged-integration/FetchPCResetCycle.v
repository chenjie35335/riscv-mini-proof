Require Import CoreSocModel ComparisonNodes RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount FormalResetTrace FormalResetPreparation FormalLocalHistory ObservedLegalNoTrap FormalPCRegister FetchPCResetValue FormalCheckerResetConnections FetchPCResetCommit.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma fetch_pc_initial_safe : initial_register_safe 7768 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem fetch_pc_settle_reset_commit inputs initial stable result old_value :
 state_reset initial true ->
 staged_register_lookup 7768 initial = Some old_value -> type_of_val old_value = Gtyp (Fuint 33) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33).
Proof.
 intros [start [Start Reset]] Old Typed Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 pose proof (legal_local_reset_history _ history 9259 true Steps Reset0) as Resets.
 pose proof (reset_connection_24_transfer (formal_invalid_policy inputs nil)
 (history 9257%nat) (history 9257%nat) (history 9258%nat) true
 (Resets 9257%nat ltac:(vm_compute; lia)) (Steps 9257%nat ltac:(vm_compute; lia))) as R1.
 pose proof (reset_connection_65_transfer (formal_invalid_policy inputs nil)
 (history 9258%nat) (history 9258%nat) (history 9259%nat) true R1
 (Steps 9258%nat ltac:(vm_compute; lia))) as ResetBit.
 pose proof (fetch_pc_reset_value_after_two (formal_invalid_policy inputs nil)
 (history 9257%nat) (history 9258%nat) (history 9259%nat)
 (Steps 9257%nat ltac:(vm_compute; lia)) (Steps 9258%nat ltac:(vm_compute; lia))) as Word.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit)
 as [before [after [Before [Local After]]]].
 rewrite Last in ResetBit, Word. unfold top_environment in ResetBit, Word. rewrite Before in ResetBit, Word.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 7768 pc_register_present Iterations) as Hold.
 unfold staged_register_lookup in Hold. rewrite Before in Hold.
 change (VM.find 7768 before = staged_register_lookup 7768 initial) in Hold. rewrite Old in Hold.
 exists after. split; [exact After|].
 exact (fetch_pc_formal_reset_commit (formal_invalid_policy inputs nil) before before after old_value fetch_pc_reset_word32
 Hold Typed ResetBit Word fetch_pc_reset_size32 Local).
Qed.
Theorem fetch_pc_real_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 7768 old = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 33) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33).
Proof.
 intros Previous Old Typed Reset Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Steps; [|discriminate Cycle].
 apply (fetch_pc_settle_reset_commit inputs initial stable result old_value); try assumption.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 7768
 (Logic.eq_refl _) (Logic.eq_refl _) fetch_pc_initial_safe pc_register_present Previous Prepare).
 exact Old.
Qed.
Print Assumptions fetch_pc_real_reset_cycle.
