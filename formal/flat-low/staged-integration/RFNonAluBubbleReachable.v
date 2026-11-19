Require Import RFNonAluBubbleHazard CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation JointBoundaryRegisters FormalFetchType FormalResetPreparation ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories generated_run.
Theorem rf_nonalu_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 rf_nonalu_bubble_invariant (top_environment next).
Proof.
 intros Observe Legal Next Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 unfold top_environment. rewrite After. rewrite <- Top in Step. rewrite <- Last in Step.
 exact (rf_nonalu_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Require Import RFReadForwarding RFWriteEffect StagedRegisterHold.
From nbits Require Import NBits.
Theorem rf_actual_forwarding_with_bubble_invariant second invalid previous s0 s1 s2 s3 s4 s5 bank reference read_address destination enabled low high alu_data write_data :
 rf_nonalu_bubble_invariant previous ->
 VM.find (rf_source_address second) s0 = Some (Gval (Fuint 5) read_address) ->
 VM.find (rf_source_address second) s1 = Some (Gval (Fuint 5) read_address) ->
 VM.find 7805 s1 = Some (Gval (Fuint 5) destination) ->
 VM.find 7757 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 s2 = Some (Gval (Fuint 2) [::low;high]) ->
 size alu_data = 32%nat -> size (bank (to_nat read_address)) = 32%nat ->
 VM.find 7752 s4 = Some (Gval (Fuint 32) alu_data) ->
 VM.find (rf_forward_raw second) s4 = Some (Gval (Fuint 32) (bank (to_nat read_address))) ->
 bank (to_nat read_address) = rf_apply_effect reference RFNoWrite (to_nat read_address) ->
 ((~~low && ~~high) = true -> alu_data = write_data) ->
 formal_value_iter invalid flat_memories previous false previous flat_statements = Some s0 ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find (rf_forward_node second) s5 = Some (Gval (Fuint 32)
 (rf_apply_effect reference (if enabled then RFWrite (to_nat destination) write_data else RFNoWrite) (to_nat read_address))).
Proof.
 intros Invariant A0 A1 Destination Enabled Mode Size RawSize Data Raw Paired AluData S0 S1 S2 S3 S4 S5.
 eapply (rf_actual_forwarding_reads_written_bank second invalid s0 s1 s2 s3 s4 s5 bank reference read_address destination enabled low high alu_data write_data);
 [exact A0|exact A1|exact Destination|exact Enabled|exact Mode|exact Size|exact RawSize|exact Data|exact Raw|exact Paired|exact AluData| |exact S1|exact S2|exact S3|exact S4|exact S5].
 intros NonAlu Hit.
 pose proof (proj2 (joint_boundary_register_properties 7756 2 rf_nonalu_mode_member)) as ModeRegister.
 pose proof (proj2 (joint_boundary_register_properties 7757 1 rf_nonalu_enable_member)) as EnableRegister.
 rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7757 EnableRegister S1) in Enabled.
 rewrite (staged_combinational_holds_registers invalid flat_memories previous previous s0 flat_statements 7757 EnableRegister S0) in Enabled.
 rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7756 ModeRegister S2) in Mode.
 rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7756 ModeRegister S1) in Mode.
 rewrite (staged_combinational_holds_registers invalid flat_memories previous previous s0 flat_statements 7756 ModeRegister S0) in Mode.
 pose proof (rf_nonalu_bubble_no_read_collision second invalid previous s0 enabled low high read_address (to_nat destination) Invariant Enabled Mode A0 S0 NonAlu) as NoHit.
 rewrite NoHit in Hit. discriminate Hit.
Qed.
Require Import EarlyBubbleNopFullHistory StagedObservedRegister StagedCircuitRegisterHold.
Lemma rf_nonalu_bubble_comb_hold invalid old current result :
 rf_nonalu_bubble_invariant old ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 rf_nonalu_bubble_invariant result.
Proof.
 intros Invariant Step low high Enabled Mode NonAlu.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7757 (proj2 (joint_boundary_register_properties 7757 1 rf_nonalu_enable_member)) Step) in Enabled.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7756 (proj2 (joint_boundary_register_properties 7756 2 rf_nonalu_mode_member)) Step) in Mode.
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7748 (proj2 (joint_boundary_register_properties 7748 32 early_bubble_front_instruction_member)) Step).
 exact (Invariant low high Enabled Mode NonAlu).
Qed.
Lemma rf_nonalu_bubble_history_hold invalid history (limit:nat) :
 rf_nonalu_bubble_invariant (history 0%nat) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> rf_nonalu_bubble_invariant (history time).
Proof.
 intros Initial Steps time. induction time as [|time IH];intro Bound;[exact Initial|].
 exact (rf_nonalu_bubble_comb_hold invalid (history time) (history time) (history (S time)) (IH ltac:(lia)) (Steps time ltac:(lia))).
Qed.
Lemma rf_nonalu_bubble_prepared previous old external initial :
 SVM.find nil previous = Some old -> rf_nonalu_bubble_invariant old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial ->
 rf_nonalu_bubble_invariant (top_environment initial).
Proof.
 intros Previous Invariant Prepare.
 assert (Copy : forall node width, List.In (node,width) joint_boundary_registers ->
 staged_register_lookup (N.of_nat node) initial = VM.find (N.of_nat node) old).
 { intros node width Member. pose proof joint_boundary_preparation_check as Check.
   rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
   cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
   exact (staged_prepared_register_copies previous old external initial _ NotClock NotReset Safe
   (proj2 (joint_boundary_register_properties node width Member)) Previous Prepare). }
 pose proof (Copy 7757%nat 1%nat rf_nonalu_enable_member) as EnableCopy.
 pose proof (Copy 7756%nat 2%nat rf_nonalu_mode_member) as ModeCopy.
 pose proof (Copy 7748%nat 32%nat early_bubble_front_instruction_member) as FrontCopy.
 intros low high Enabled Mode NonAlu.
 unfold staged_register_lookup in EnableCopy,ModeCopy,FrontCopy. unfold top_environment in *.
 destruct (SVM.find nil initial) as [env|];[|discriminate Enabled].
 rewrite EnableCopy in Enabled. rewrite ModeCopy in Mode. rewrite FrontCopy.
 exact (Invariant low high Enabled Mode NonAlu).
Qed.
From firrtl Require Import FormalInitialization.
Require Import RegisterInvariants RFNonAluReset JointBoundaryInduction ExternalReset.
Lemma rf_nonalu_disabled_invariant env : VM.find 7757 env = Some (Gval (Fuint 1) [::false]) -> rf_nonalu_bubble_invariant env.
Proof. intros Disabled low high Enabled Mode NonAlu. rewrite Disabled in Enabled. discriminate Enabled. Qed.
Theorem rf_nonalu_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 rf_nonalu_bubble_invariant (top_environment states).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init;[|discriminate].
 intro Reset.
 destruct (joint_boundary_symbolic_initial memory inputs initial Init) as [Registers Storage].
 destruct (Registers 7757%nat 1%nat rf_nonalu_enable_member) as [bits [Size Value]].
 unfold top_environment in Value. destruct (SVM.find nil initial) as [old|] eqn:Old;[|discriminate Value].
 destruct (rf_nonalu_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 1) bits) Old Value (Logic.eq_refl _) ltac:(unfold force_formal_reset;cbn [formal_external_inputs];apply RegisterMapFacts.find_add_eq;reflexivity) Reset) as [env [Env Disabled]].
 unfold top_environment. rewrite Env. exact (rf_nonalu_disabled_invariant env Disabled).
Qed.
Local Transparent generated_run.
Theorem rf_nonalu_bubble_run memory inputs k states :
 generated_run memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 rf_nonalu_bubble_invariant (top_environment states).
Proof.
 destruct k as [|k];intros Run Legal.
 - unfold generated_run,formal_run_after_reset in Run.
   destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset;[|discriminate Run].
   cbn [circuit_formal_run] in Run. inversion Run;subst states.
   exact (rf_nonalu_after_formal_reset memory (inputs 0%nat) initial Reset).
 - assert (PriorLegal : generated_legal_trace memory inputs k) by (apply (joint_legal_trace_prefix memory inputs (S k) k Legal);lia).
   destruct (legal_observation_reset memory inputs k PriorLegal) as [reset Reset].
   destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7757%nat 1%nat rf_nonalu_enable_member) as [bits [Size Value]].
     destruct (rf_nonalu_real_reset_cycle (generated_observation_input inputs k) previous old states (Gval (Fuint 1) bits) Old Value (Logic.eq_refl _) Reset Next) as [env [Env Disabled]].
     unfold top_environment. rewrite Env. exact (rf_nonalu_disabled_invariant env Disabled).
   + destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
     exact (rf_nonalu_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Require Import StagedIterationCount.
Theorem rf_nonalu_bubble_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 rf_nonalu_bubble_invariant (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [previous|] eqn:Run;[|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Expanded) as [history [First [Last Steps]]].
 pose proof (rf_nonalu_bubble_run memory inputs k previous Run Legal) as Invariant.
 destruct (fetch9220_run_type memory inputs k previous Run) as [old [value [Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 rewrite <- Last. eapply (rf_nonalu_bubble_history_hold _ history 9259);
 [rewrite First;exact (rf_nonalu_bubble_prepared previous old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
Qed.
Lemma rf_nonalu_before_observation memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 exists previous, rf_nonalu_bubble_invariant previous /\
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories previous false previous flat_statements = Some (top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run;[|discriminate Expanded].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed) (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Expanded) as [history [First [Last Steps]]].
 pose proof (rf_nonalu_bubble_run memory inputs k committed Run Legal) as Invariant.
 destruct (fetch9220_run_type memory inputs k committed Run) as [old [value [Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 exists (history 9258%nat). split.
 - eapply (rf_nonalu_bubble_history_hold _ history 9259);
   [rewrite First;exact (rf_nonalu_bubble_prepared committed old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
 - rewrite <- Last. exact (Steps 9258%nat ltac:(vm_compute;lia)).
Qed.
Theorem rf_nonalu_observed_no_collision memory inputs k observed second enabled low high address destination :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7757 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 7756 (top_environment observed) = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find (rf_source_address second) (top_environment observed) = Some (Gval (Fuint 5) address) ->
 (~~low && ~~high) = false -> rf_write_hits enabled destination (to_nat address) = false.
Proof.
 intros Observe Legal Enabled Mode Address NonAlu.
 destruct (rf_nonalu_before_observation memory inputs k observed Observe Legal) as [previous [Invariant Step]].
 rewrite (staged_combinational_holds_registers _ flat_memories previous previous (top_environment observed) flat_statements 7757 (proj2 (joint_boundary_register_properties 7757 1 rf_nonalu_enable_member)) Step) in Enabled.
 rewrite (staged_combinational_holds_registers _ flat_memories previous previous (top_environment observed) flat_statements 7756 (proj2 (joint_boundary_register_properties 7756 2 rf_nonalu_mode_member)) Step) in Mode.
 exact (rf_nonalu_bubble_no_read_collision second _ previous (top_environment observed) enabled low high address destination Invariant Enabled Mode Address Step NonAlu).
Qed.
