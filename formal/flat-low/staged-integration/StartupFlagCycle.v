Require Import StartupFlagInitialization StartupFlagNodes StartupFlagCommit.
Require Import CoreSocModel ComparisonNodes RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount FormalResetPreparation FormalLocalHistory ObservedLegalNoTrap FormalCheckerResetConnections ConcreteRegisterInitialization.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem startup_flag_real_cycle inputs previous old result old_value bit :
 SVM.find nil previous = Some old -> VM.find 7762 old = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 7762 env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Previous Old Typed Reset Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some previous) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 bit Steps Reset0) as Resets.
 pose proof (reset_connection_24_transfer (formal_invalid_policy inputs nil)
 (history 9256%nat) (history 9256%nat) (history 9257%nat) bit
 (Resets 9256%nat ltac:(vm_compute; lia)) (Steps 9256%nat ltac:(vm_compute; lia))) as R1.
 pose proof (reset_connection_65_transfer (formal_invalid_policy inputs nil)
 (history 9257%nat) (history 9257%nat) (history 9258%nat) bit R1
 (Steps 9257%nat ltac:(vm_compute; lia))) as CoreReset.
 pose proof (startup_cast_value (formal_invalid_policy inputs nil) (history 9258%nat) (history 9258%nat)
 (history 9259%nat) bit CoreReset (Steps 9258%nat ltac:(vm_compute; lia))) as FlagSource.
 pose proof (staged_prepared_register_copies previous old _ initial 7762
 (Logic.eq_refl _) (Logic.eq_refl _) startup_initial_safe startup_register_present Previous Prepare) as Copy.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 7762 startup_register_present Iterations) as Hold.
 rewrite Copy Old in Hold.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Cycle)
 as [before [after [Before [Commit After]]]].
 unfold staged_register_lookup in Hold. rewrite Before in Hold.
 rewrite Last in FlagSource. unfold top_environment in FlagSource. rewrite Before in FlagSource.
 exists after. split; [exact After|].
 exact (startup_flag_commit (formal_invalid_policy inputs nil) before before after old_value bit Hold Typed FlagSource Commit).
Qed.
Print Assumptions startup_flag_real_cycle.
