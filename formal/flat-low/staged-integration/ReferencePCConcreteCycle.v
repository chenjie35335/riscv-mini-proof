Require Import FormalLocalHistory FormalObservedHistory FormalObservationCommit StagedFlatCircuitIteration StagedCircuitRegisterHold ReferencePCResetHistory ReferencePCResetValue ReferencePCResetCommit ReferencePCSequentialValues.
Require Import CoreSocModel ComparisonNodes ConcreteRegisterInitialization FormalFetchType StagedObservedRegister ReferencePCInitialization ReferencePCResetBase ReferencePCSequentialStableObserved ReferencePCRedirectObserved ObservedReferencePCStutter.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.

(* This certificate describes only the selected PC update, not alignment or
   equality with the DUT. Its discharge is a separate reference-cone obligation. *)
Definition reference_pc_normal_concrete_controls env :=
 VM.find 1395 env = Some (Gval (Fuint 1) [::false]) \/
 (VM.find 1395 env = Some (Gval (Fuint 1) [::true]) /\
  VM.find 6780 env = Some (Gval (Fuint 1) [::false]) /\
  (VM.find 6507 env = Some (Gval (Fuint 1) [::false]) \/
   (VM.find 6507 env = Some (Gval (Fuint 1) [::true]) /\
    map_uint_concrete 6508 32 env))).

Theorem reference_pc_concrete_run_observed memory inputs k states observed :
 generated_run memory inputs k = Some states ->
 generated_observe memory inputs k = Some observed ->
 map_uint_concrete 7331 32 (top_environment states) ->
 map_uint_concrete 7331 32 (top_environment observed).
Proof.
 intros Run Observe [bits [Size Value]].
 destruct (fetch9220_run_type memory inputs k states Run) as [old [value [Old Rest]]].
 unfold top_environment in Value. rewrite Old in Value.
 pose proof (staged_observed_register_copies memory inputs k states old observed 7331
 (Logic.eq_refl true) (Logic.eq_refl true) reference_pc7331_initial_safe reference_pc7331_present Run Old Observe) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy.
 exists bits. split; [exact Size|]. unfold top_environment.
 destruct (SVM.find nil observed); [exact Copy|discriminate Copy].
Qed.

Theorem reference_pc_concrete_base memory inputs states :
 generated_run memory inputs 0 = Some states ->
 map_uint_concrete 7331 32 (top_environment states).
Proof.
 intro Run. destruct (reference_pc7331_run_zero memory inputs states Run) as [env [Env Value]].
 exists reference_pc_reset_bits. split; [exact reference_pc_reset_size|].
 unfold top_environment. rewrite Env. exact Value.
Qed.

Theorem reference_pc_concrete_normal memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 map_uint_concrete 7331 32 (top_environment observed) ->
 reference_pc_normal_concrete_controls (top_environment observed) ->
 map_uint_concrete 7331 32 (top_environment next).
Proof.
 intros Observe Legal Next Reset [pc [Size PC]] Controls.
 destruct Controls as [Disabled|[Valid [Exception [Sequential|[Redirect [target [TargetSize Target]]]]]]].
 - exists pc. split; [exact Size|].
   exact (observed_reference_pc_disabled_step memory inputs k observed next pc Observe Legal Next Reset Disabled Size PC).
 - exists (reference_pc_plus_four pc). split; [apply reference_pc_plus_four_size|].
   exact (reference_pc_sequential_observed memory inputs k observed next pc Observe Legal Next Reset Size PC Valid Sequential Exception).
 - exists target. split; [exact TargetSize|].
   exact (reference_pc_redirect_observed memory inputs k observed next pc target Observe Legal Next Reset TargetSize PC Valid Redirect Exception Target).
Qed.

Theorem reference_pc_concrete_reset memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 map_uint_concrete 7331 32 (top_environment observed) ->
 map_uint_concrete 7331 32 (top_environment next).
Proof.
 intros Observe Legal Next Reset [pc [Size PC]].
 destruct (observed_history memory inputs k observed Observe Legal)
 as [bit [history [Last [Steps Resets]]]].
 assert (TrueBit : bit = true).
 { pose proof (Resets 9259%nat ltac:(vm_compute;lia)) as R.
   rewrite Last Reset in R. destruct bit; [reflexivity|discriminate R]. }
 subst bit.
 pose proof (reference_pc_reset_after_four (formal_invalid_policy (generated_observation_input inputs k) nil)
 (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) true
 (Resets 9255%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia))
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as ResetBit.
 pose proof (reference_pc_reset_value _ (history 9258%nat) (history 9258%nat) (history 9259%nat)
 (Steps 9258%nat ltac:(vm_compute;lia))) as Word.
 rewrite Last in ResetBit, Word.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in PC, ResetBit, Word.
 exists reference_pc_reset_bits. split; [exact reference_pc_reset_size|].
 unfold top_environment. rewrite After.
 exact (reference_pc_formal_reset_commit _ before before after (Gval (Fuint 32) pc) reference_pc_reset_bits
 PC (Logic.eq_refl _) ResetBit Word reference_pc_reset_size Step).
Qed.

Theorem reference_pc_concrete_step memory inputs k observed next bit :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::bit]) ->
 map_uint_concrete 7331 32 (top_environment observed) ->
 (bit = false -> reference_pc_normal_concrete_controls (top_environment observed)) ->
 map_uint_concrete 7331 32 (top_environment next).
Proof.
 intros Observe Legal Next Reset Concrete Controls. destruct bit.
 - exact (reference_pc_concrete_reset memory inputs k observed next Observe Legal Next Reset Concrete).
 - exact (reference_pc_concrete_normal memory inputs k observed next Observe Legal Next Reset Concrete (Controls (Logic.eq_refl _))).
Qed.
Print Assumptions reference_pc_concrete_step.

Theorem reference_pc_concrete_next_observed memory inputs k observed next next_observed bit :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 generated_observe memory inputs (S k) = Some next_observed ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::bit]) ->
 map_uint_concrete 7331 32 (top_environment observed) ->
 (bit = false -> reference_pc_normal_concrete_controls (top_environment observed)) ->
 map_uint_concrete 7331 32 (top_environment next_observed).
Proof.
 intros Observe Legal Next NextObserve Reset Concrete Controls.
 apply (reference_pc_concrete_run_observed memory inputs (S k) next next_observed Next NextObserve).
 exact (reference_pc_concrete_step memory inputs k observed next bit Observe Legal Next Reset Concrete Controls).
Qed.
