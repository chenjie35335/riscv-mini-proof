Require Import LegalNoTrapHistory CoreSocModel ComparisonNodes LegalAssumptionNodes LegalAssumptionTransport NormalizedBit BooleanControlFacts.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem active_assumption_instruction_after_five invalid s0 s1 s2 s3 s4 s5 left trap :
 VM.find 9139 s1 = Some left -> normalized_bit left ->
 VM.find 45 s0 = Some trap -> normalized_bit trap ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 generated_assume_m0_0_local s5 ->
 VM.find 9238 s5 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 9139 s1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Left NL Trap NT S1 S2 S3 S4 S5 Assume Enabled.
 destruct (legal_normalized_eq_false_total trap NT) as [right [Eq NR]].
 assert (Right : VM.find 9140 s1 = Some right).
 { rewrite (legal_equation_9140 invalid s0 s0 s1 S1).
   cbn [legal_expr_9140 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Trap. exact Eq. }
 destruct (legal_normalized_and_total left right NL NR) as [value [And NV]].
 assert (Conjunction : VM.find 9141 s2 = Some value).
 { eapply legal_value_9141; [|destruct NV; reflexivity|exact S2].
   cbn [legal_expr_9141 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right. exact And. }
 destruct (active_assumption_source_adapts_true invalid s2 s3 s4 s5 S3 S4 S5 Assume Enabled)
 as [source [Source Adapt]].
 rewrite Conjunction in Source. inversion Source; subst source.
 pose proof (normalized_adaptation_recovers_bit value true NV Adapt) as ValueTrue.
 rewrite ValueTrue in And.
 destruct (normalized_and_true_sources left right NL NR And) as [LeftTrue _].
 rewrite <- LeftTrue. exact Left.
Qed.
Require Import CoreSocModel ComparisonNodes FormalLocalHistory LegalBooleanHistory LegalWireNormalization LegalAssumptionActivation LegalNoTrapHistory.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem legal_instruction_history_window invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (14 <= start)%coq_nat -> (Nat.add start 5 <= limit)%coq_nat ->
 VM.find 1 (history (Nat.add start 3)) = Some (Gval (Fuint 1) [::false]) ->
 generated_assume_m0_0_local (history (Nat.add start 5)) ->
 VM.find 9139 (history (Nat.add start 1)) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Steps Lower Upper Reset Assume.
 set (h := fun j => history (Nat.add start j)).
 assert (LocalSteps : forall j, (j < 5)%coq_nat -> formal_flat_local_step invalid (h j) (h (S j))).
 { intros j Small. unfold h. rewrite Nat.add_succ_r. apply Steps. lia. }
 destruct (legal_bool_9139_history invalid history limit Steps (Nat.add start 1) ltac:(lia) ltac:(lia))
 as [left [Left NL]].
 pose proof (Steps (Nat.pred start) ltac:(lia)) as Previous.
 assert (Next : S (Nat.pred start) = start) by lia. rewrite Next in Previous.
 destruct (legal_wire_45_normalized invalid (history (Nat.pred start)) (history (Nat.pred start)) (history start) Previous)
 as [trap [Trap NT]].
 assert (Trap0 : VM.find 45 (h 0%nat) = Some trap).
 { unfold h. rewrite Nat.add_0_r. exact Trap. }
 assert (Enabled : VM.find 9238 (h 5%nat) = Some (Gval (Fuint 1) [::true])).
 { exact (assumption_reset_enable_after_two invalid (h 3%nat) (h 4%nat) (h 5%nat)
   Reset (LocalSteps 3%nat ltac:(lia)) (LocalSteps 4%nat ltac:(lia))). }
 pose proof (active_assumption_instruction_after_five invalid
 (h 0%nat) (h 1%nat) (h 2%nat) (h 3%nat) (h 4%nat) (h 5%nat) left trap
 Left NL Trap0 NT
 (LocalSteps 0%nat ltac:(lia)) (LocalSteps 1%nat ltac:(lia)) (LocalSteps 2%nat ltac:(lia))
 (LocalSteps 3%nat ltac:(lia)) (LocalSteps 4%nat ltac:(lia)) Assume Enabled) as NoTrap.
 exact NoTrap.
Qed.

Require Import ObservedLegalNoTrap FormalLegalObservation FormalResetPreparation StagedIterationCount.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_legal_instruction_history memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists committed initial history,
 generated_run memory inputs k = Some committed /\
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k)) = Some initial /\
 history 0%nat = top_environment initial /\ history 9259%nat = top_environment states /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) /\
 VM.find 9139 (history 9255%nat) = Some (Gval (Fuint 1) [::true]).
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
 assert (NoTrap : VM.find 9139 (history 9255%nat) = Some (Gval (Fuint 1) [::true])).
 { apply (legal_instruction_history_window _ history 9259 9254 Steps).
   - vm_compute; lia.
   - vm_compute; lia.
   - apply (legal_local_reset_history _ history 9259 false Steps Reset0). vm_compute; lia.
   - exact LocalAssume. }
 exists committed, initial, history. repeat split; assumption.
Qed.
