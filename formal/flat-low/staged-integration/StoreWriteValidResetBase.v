Require Import StagedCircuitRegisterHold StoreWriteValidReset StoreWriteCompareType StoreWriteValidReachableType StoreWriteValidInitialization StoreWriteValidRegister
 CoreSocModel ComparisonNodes ObservedLegalNoTrap FormalCheckerResetConnections FormalLocalHistory FormalResetPreparation FormalResetTrace
 StagedFlatCircuitIteration StagedIterationCount StagedObservedRegister RegisterPreparationFrames RegisterInvariants.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem store_write_valid_reset_fullhistory invalid history result old_value :
 VM.find 8028(history 0%nat)=Some old_value ->type_of_val old_value=Gtyp(Fuint 1) ->
 VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::true]) ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 formal_value_iter invalid flat_memories(history 9259%nat)true(history 9259%nat)flat_statements=Some result ->
 VM.find 8028 result=Some(Gval(Fuint 1)(from_N 1 0)).
Proof.
 intros Old Typed Reset Steps Commit.
 pose proof(legal_local_reset_history invalid history 9259 true Steps Reset)as Resets.
 assert(Control:VM.find 65(history 9259%nat)=Some(Gval(Fuint 1)[::true])).
 { eapply(reset_connection_65_transfer _ (history 9258%nat)(history 9258%nat)(history 9259%nat)true);[|apply Steps;vm_compute;lia].
   eapply(reset_connection_24_transfer _ (history 9257%nat)(history 9257%nat)(history 9258%nat)true);[apply Resets;vm_compute;lia|apply Steps;vm_compute;lia]. }
 destruct(store_write_compare_type_step _ (history 9258%nat)(history 9258%nat)(history 9259%nat)(Steps 9258%nat ltac:(vm_compute;lia)))as[value[Value ValueType]].
 eapply(store_write_valid_reset_commit _ _ _ _ old_value value);[|exact Typed|exact Control|exact Value|exact ValueType|exact Commit].
 rewrite(store_write_valid_register_history invalid history 9259 Steps 9259 ltac:(vm_compute;lia)). exact Old.
Qed.
Theorem store_write_valid_settle_reset_commit inputs initial stable result old_value :
 state_reset initial true -> staged_register_lookup 8028 initial = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 8028 env = Some (Gval (Fuint 1) (from_N 1 0)).
Proof.
 intros [start [Start Reset]] Old Typed Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 assert (Old0 : VM.find 8028 (history 0%nat) = Some old_value).
 { rewrite First. unfold top_environment. rewrite Start. unfold staged_register_lookup in Old. rewrite Start in Old. exact Old. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 assert (Same : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 exists after. split; [exact After|].
 eapply (store_write_valid_reset_fullhistory (formal_invalid_policy inputs nil) history after old_value); [exact Old0|exact Typed|exact Reset0|exact Steps|].
 rewrite Same. exact Local.
Qed.
Theorem store_write_valid_real_reset_cycle inputs previous old result old_value :
 SVM.find nil previous = Some old -> VM.find 8028 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 8028 env = Some (Gval (Fuint 1) (from_N 1 0)).
Proof.
 intros Previous Old Typed Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (store_write_valid_settle_reset_commit inputs initial stable result old_value); try assumption.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - rewrite (staged_prepared_register_copies previous old _ initial 8028 (Logic.eq_refl _) (Logic.eq_refl _) store_write_valid_initial_safe store_write_valid_register_present Previous Prepare). exact Old.
Qed.
Theorem store_write_valid_after_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1(Fuint 1)memory inputs=Some states ->
 VM.find 8028(top_environment states)=Some(Gval(Fuint 1)[::false]).
Proof.
 unfold formal_state_after_reset.
 destruct(circuit_symbolic_initial_state generated_modules generated_top memory inputs)as[initial|]eqn:Init;[|discriminate]. intro Reset.
 destruct(store_write_valid_initial_type memory inputs initial Init)as[old[value[Old[Value Typed]]]].
 destruct(store_write_valid_real_reset_cycle (force_formal_reset 1(Fuint 1)inputs)initial old states value Old Value Typed
 ltac:(unfold force_formal_reset;cbn[formal_external_inputs];apply RegisterMapFacts.find_add_eq;reflexivity)Reset)as[env[Env Zero]].
 unfold top_environment. rewrite Env. exact Zero.
Qed.
Theorem store_write_valid_run_zero memory inputs states :
 generated_run memory inputs 0=Some states ->VM.find 8028(top_environment states)=Some(Gval(Fuint 1)[::false]).
Proof.
 unfold generated_run,formal_run_after_reset.
 destruct(formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory(inputs 0%nat))as[initial|]eqn:Reset;[|discriminate].
 cbn[circuit_formal_run]. intro Run. inversion Run;subst states.
 exact(store_write_valid_after_reset memory(inputs 0%nat)initial Reset).
Qed.
