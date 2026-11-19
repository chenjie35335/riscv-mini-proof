Require Import CoreSocModel ComparisonNodes RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount FormalResetPreparation FormalLocalHistory ObservedLegalNoTrap FormalCheckerResetConnections ConcreteRegisterInitialization.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Section RegisterReset.
Variable node : VarOrder.T.
Hypothesis Present : has_register node flat_statements = true.
Hypothesis NotClock : node != 0.
Hypothesis NotReset : node != 1.
Hypothesis Safe : initial_register_safe node flat_statements.
Hypothesis ResetWrite : forall invalid old current result old_value,
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 1) [::true]).
Theorem boolean_register_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find node old = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find node env = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Previous Old Typed Reset Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some previous) _ initial _ Reset Prepare) as [env [Env InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 true Steps Reset0) as Resets.
 pose proof (reset_connection_24_transfer (formal_invalid_policy inputs nil)
 (history 9257%nat) (history 9257%nat) (history 9258%nat) true
 (Resets 9257%nat ltac:(vm_compute; lia)) (Steps 9257%nat ltac:(vm_compute; lia))) as R1.
 pose proof (reset_connection_65_transfer (formal_invalid_policy inputs nil)
 (history 9258%nat) (history 9258%nat) (history 9259%nat) true R1
 (Steps 9258%nat ltac:(vm_compute; lia))) as CoreReset.
 pose proof (staged_prepared_register_copies previous old _ initial node
 NotClock NotReset Safe Present Previous Prepare) as Copy.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable node Present Iterations) as Hold.
 rewrite Copy Old in Hold.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Cycle)
 as [before [after [Before [Commit After]]]].
 unfold staged_register_lookup in Hold. rewrite Before in Hold.
 rewrite Last in CoreReset. unfold top_environment in CoreReset. rewrite Before in CoreReset.
 exists after. split; [exact After|].
 exact (ResetWrite (formal_invalid_policy inputs nil) before before after old_value Hold Typed CoreReset Commit).
Qed.
Hypothesis Initial : forall memory inputs states,
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ map_uint_concrete node 1 env.
Theorem boolean_register_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find node env = Some (Gval (Fuint 1) [::true]).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init; [|discriminate].
 intro Reset.
 destruct (Initial memory inputs initial Init) as [old [Old [bits [Size Value]]]].
 apply (boolean_register_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 1) bits));
 try assumption; try reflexivity.
 unfold force_formal_reset. cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem boolean_register_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ VM.find node env = Some (Gval (Fuint 1) [::true]).
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (boolean_register_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
End RegisterReset.
Print Assumptions boolean_register_run_zero.
