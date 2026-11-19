Require Import ObservedLegalNoTrap ReferenceMISAConcreteNodes ReferencePCResetHistory ExceptionPCSourceRegisters FormalResetTrace FormalResetPreparation ConcreteRegisterInitialization UIntRegisterCertificate FormalSingletonSymbolic RegisterPreparationFrames StagedObservedRegister StagedCircuitRegisterHold StagedFlatCircuitIteration StagedIterationCount FormalLocalHistory FormalObservationCommit JointBoundaryInduction ExternalReset CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma misa_present : has_register 7332 flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_initial_safe : initial_register_safe 7332 flat_statements.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_uint_declarations : uint_register_declarations 7332 32 flat_statements.
Proof. apply uint_register_declarations_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_symbolic_init inputs path state :map_uint_concrete 7332 32(initialize_symbolic_registers inputs path flat_statements state).
Proof. apply initialize_establishes_uint_concrete;[exact misa_uint_declarations|exact misa_present]. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition reference_misa_concrete states :=exists env,SVM.find nil states=Some env /\map_uint_concrete 7332 32 env.
Lemma misa_normal_history invalid history limit word :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 size word=32%nat ->VM.find 7332(history 0%nat)=Some(Gval(Fuint 32)word) ->
 forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1820(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Steps Size Initial [|[|[|[|t]]]] Lower Upper;try lia.
 pose proof(flat_register_history_same invalid history limit 7332 misa_present Steps t ltac:(lia))as Held.
 rewrite Initial in Held.
 pose proof(misa_1750_step invalid(history t)(history(S t))word Size Held(Steps t ltac:(lia)))as A.
 pose proof(misa_2807_step invalid(history(S t))(history(S(S t)))word Size A(Steps(S t)ltac:(lia)))as B.
 pose proof(misa_7150_step invalid(history(S(S t)))(history(S(S(S t))))word Size B(Steps(S(S t))ltac:(lia)))as C.
 exact(misa_1820_step invalid(history(S(S(S t))))(history(S(S(S(S t)))))word Size C(Steps(S(S(S t)))ltac:(lia))).
Qed.
Theorem reference_misa_cycle_concrete inputs previous result bit :
 reference_misa_concrete previous ->VM.find 1(formal_external_inputs inputs)=Some(Gval(Fuint 1)[::bit]) ->
 circuit_formal_cycle generated_modules generated_top(Some previous)inputs=Some result ->reference_misa_concrete result.
Proof.
 intros[old[Old[word[Size Word]]]]Reset Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct(circuit_initial_map_with_memory generated_modules generated_top(Some previous)(formal_external_inputs inputs))as[initial|]eqn:Prepare;[|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count;rewrite Count in Cycle.
 destruct(circuit_formal_iterations generated_modules generated_top inputs 9259 initial)as[stable|]eqn:Iterations;[|discriminate Cycle].
 destruct(local_iteration_history inputs 9259 initial stable Iterations)as[history[First[Last Steps]]].
 pose proof(staged_prepared_register_copies previous old _ initial 7332(Logic.eq_refl _)(Logic.eq_refl _)misa_initial_safe misa_present Old Prepare)as Prepared.
 assert(Initial:VM.find 7332(history 0%nat)=Some(Gval(Fuint 32)word)).
 { rewrite First. unfold top_environment. rewrite Word in Prepared. unfold staged_register_lookup in Prepared.
   destruct(SVM.find nil initial);[exact Prepared|discriminate Prepared]. }
 destruct(top_reset_prepared(Some previous)_ initial _ Reset Prepare)as[env[Env Root]].
 assert(Root0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::bit]))by(rewrite First;unfold top_environment;rewrite Env;exact Root).
 pose proof(legal_local_reset_history _ history 9259 bit Steps Root0)as Resets.
 pose proof(reference_pc_reset_after_four _ (history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)bit
 (Resets 9255 ltac:(vm_compute;lia))(Steps 9255 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia))(Steps 9257 ltac:(vm_compute;lia))(Steps 9258 ltac:(vm_compute;lia)))as Control.
 pose proof(misa_7436_history _ history 9259 Steps 9259 ltac:(vm_compute;lia)ltac:(lia))as Yes.
 pose proof(misa_normal_history _ history 9259 word Steps Size Initial 9259 ltac:(vm_compute;lia)ltac:(lia))as No.
 pose proof(flat_register_history_same _ history 9259 7332 misa_present Steps 9259 ltac:(lia))as Held. rewrite Initial in Held.
 destruct(flat_iteration_projection _ stable true result Cycle)as[before[after[Before[Commit After]]]].
 assert(Top:history 9259%nat=before)by(rewrite Last;unfold top_environment;rewrite Before;reflexivity).
 rewrite Top in Control,Yes,No,Held.
 exists after;split;[exact After|]. exists(if bit then reference_misa_word else word);split.
 - destruct bit;[apply size_from_N|exact Size].
 - exact(misa_commit _ before after word bit Size Held Control Yes No Commit).
Qed.
Theorem reference_misa_initial_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs=Some states ->reference_misa_concrete states.
Proof.
 intro Init. exact(singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements memory inputs states(map_uint_concrete 7332 32)flat_instance_map_exact flat_module_exact(misa_symbolic_init inputs nil)Init).
Qed.
Theorem reference_misa_run_zero memory inputs states :generated_run memory inputs 0=Some states ->reference_misa_concrete states.
Proof.
 unfold generated_run,formal_run_after_reset.
 destruct(formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory(inputs 0%nat))as[initial|]eqn:Reset;[|discriminate].
 cbn[circuit_formal_run]. intro Run;inversion Run;subst states.
 unfold formal_state_after_reset in Reset.
 destruct(circuit_symbolic_initial_state generated_modules generated_top memory(inputs 0%nat))as[symbolic|]eqn:Init;[|discriminate Reset].
 apply(reference_misa_cycle_concrete (force_formal_reset generated_reset_id generated_reset_type(inputs 0%nat)) symbolic initial true(reference_misa_initial_concrete _ _ _ Init));[|exact Reset].
 unfold force_formal_reset;cbn[formal_external_inputs]. apply RegisterMapFacts.find_add_eq;reflexivity.
Qed.
Theorem reference_misa_run_concrete memory inputs k states :
 generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->reference_misa_concrete states.
Proof.
 revert states. induction k as[|k IH];intros states Run Legal;[exact(reference_misa_run_zero memory inputs states Run)|].
 pose proof Run as Expanded;rewrite generated_run_successor in Expanded.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Expanded].
 pose proof(joint_legal_trace_prefix memory inputs(S k)k Legal(Nat.le_succ_diag_r k))as PriorLegal.
 destruct(legal_observation_reset memory inputs k PriorLegal)as[bit Reset].
 exact(reference_misa_cycle_concrete _ previous states bit(IH previous(Logic.eq_refl _)PriorLegal)Reset Expanded).
Qed.
Theorem reference_misa_observed_concrete memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 map_uint_concrete 7332 32(top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded;unfold generated_observe in Expanded.
 destruct(generated_run memory inputs k)as[previous|]eqn:Run;[|discriminate Expanded].
 destruct(reference_misa_run_concrete memory inputs k previous Run Legal)as[old[Old[word[Size Word]]]].
 pose proof(staged_observed_register_copies memory inputs k previous old observed 7332(Logic.eq_refl _)(Logic.eq_refl _)misa_initial_safe misa_present Run Old Observe)as Copy.
 rewrite Word in Copy;unfold staged_register_lookup in Copy.
 exists word;split;[exact Size|]. unfold top_environment.
 destruct(SVM.find nil observed);[exact Copy|discriminate Copy].
Qed.
