Require Import CoreSocModel ComparisonNodes ReferenceIllegalSpine ReferenceIllegalFold ReferenceInstructionDecode MemoryRequestObservedSemantics FormalObservedHistory ObservedJointRegisterConcrete LoadTypeCorrespondence JointUpdateBoundaryHistory ReferenceControlStabilityHistory FormalLocalHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_instruction_matches instruction row :=
 N.eqb (reference_instruction_code row) (N.land (to_N instruction) (reference_instruction_mask row)).
Theorem reference_illegal_observed_value memory inputs k observed instruction enabled :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 3042 (top_environment observed) = Some (Gval (Fuint 1)
 [::if enabled then reference_illegal_fold (reference_instruction_matches (memory_reference_instruction instruction enabled)) 48 else false]).
Proof.
 intros Observe Legal Instruction Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Inst : forall t, (t <= 9259)%coq_nat -> VM.find 7750 (history t) = Some (Gval (Fuint 32) instruction)).
 { intros t Upper. pose proof (joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps) as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last. exact Instruction. }
 assert (Enable : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1707 (history t) = Some (Gval (Fuint 1) [::enabled])).
 { intros t Lower Upper. rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert (Source : forall t, (205 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) (memory_reference_instruction instruction enabled))).
 { intros t Lower Upper. exact (memory_reference_instruction_history _ history 9259 200 instruction enabled Size Steps Inst Enable t Lower Upper). }
 set h := fun t => history (Nat.add 9207 t).
 assert (LocalSteps : forall i, (i < 52)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (h i) false (h i) flat_statements = Some (h (S i))).
 { intros i Bound. unfold h. replace (Nat.add 9207 (S i)) with (S (Nat.add 9207 i)) by lia.
 apply Steps. eapply Nat.lt_le_trans;[apply Nat.add_lt_mono_l;exact Bound|vm_compute;lia]. }
 assert (LocalSource : forall i, (i <= 52)%coq_nat -> VM.find 1884 (h i) = Some (Gval (Fuint 32) (memory_reference_instruction instruction enabled))).
 { intros i Bound. unfold h. apply Source;[eapply Nat.le_trans with (m:=9207%nat);[vm_compute;lia|apply Nat.le_add_r]|]. eapply Nat.le_trans;[apply Nat.add_le_mono_l;exact Bound|vm_compute;lia]. }
 assert (Decode : forall row i, (row < 48)%coq_nat -> (2 <= i)%coq_nat -> (i <= 52)%coq_nat -> VM.find (reference_instruction_guard row) (h i) = Some (Gval (Fuint 1) [::reference_instruction_matches (memory_reference_instruction instruction enabled) row])).
 { intros row i Row Lower Upper. exact (reference_instruction_decode_history _ h 52 (memory_reference_instruction instruction enabled) row Row LocalSteps LocalSource i Lower Upper). }
 pose proof (reference_illegal_output_history _ h 52 2 (reference_instruction_matches (memory_reference_instruction instruction enabled)) enabled LocalSteps Decode) as Output.
 assert (En : forall i, (2 <= i)%coq_nat -> (i <= 52)%coq_nat -> VM.find 1707 (h i) = Some (Gval (Fuint 1) [::enabled])).
 { intros i Lower Upper. unfold h. apply Enable;[eapply Nat.le_trans with (m:=9207%nat);[vm_compute;lia|apply Nat.le_add_r]|]. eapply Nat.le_trans;[apply Nat.add_le_mono_l;exact Upper|vm_compute;lia]. }
 specialize (Output En 52%nat ltac:(lia) ltac:(lia)).
 unfold h in Output. change (Nat.add 9207 52) with 9259%nat in Output.
 rewrite Last in Output. exact Output.
Qed.
Require Import ReferenceInstructionCoverage LegalInstructionClass.
Lemma reference_instruction_coverage_matches instruction row : (row < 48)%coq_nat ->
 reference_instruction_matches instruction row =
 N.eqb (snd (seq.nth (0,0) ReferenceInstructionCoverage.reference_instruction_codes row))
 (N.land (to_N instruction) (fst (seq.nth (0,0) ReferenceInstructionCoverage.reference_instruction_codes row))).
Proof.
 intro Bound. do 48 (destruct row as [|row];[reflexivity|]);lia.
Qed.
Theorem classified_reference_illegal_false instruction :
 legal_instruction_classified instruction ->
 reference_illegal_fold (reference_instruction_matches instruction) 48 = false.
Proof.
 intro Classified. destruct (classified_reference_decode instruction Classified) as [row [Bound Match]].
 eapply reference_illegal_fold_match;[exact Bound|].
 rewrite (reference_instruction_coverage_matches instruction row Bound). exact Match.
Qed.
Theorem reference_illegal_active_absent memory inputs k observed instruction enabled :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 3042 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset Bubble Instruction Enabled.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 pose proof (legal_active_commit_instruction_classified_observed memory inputs k observed instruction Observe Legal Reset Bubble Instruction Size) as Classified.
 rewrite (reference_illegal_observed_value memory inputs k observed instruction enabled Observe Legal Instruction Enabled).
 destruct enabled;[|reflexivity].
 change (Some (Gval (Fuint 1) [::reference_illegal_fold (reference_instruction_matches instruction) 48]) = Some (Gval (Fuint 1) [::false])).
 rewrite (classified_reference_illegal_false instruction Classified). reflexivity.
Qed.
Require Import LoadPipelineClassification ObservedCheckerBubbleValue ReferenceValidNormalizedLink NormalizedBit.
Theorem legal_observed_instruction_classified memory inputs k observed instruction :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 legal_instruction_classified instruction.
Proof.
 intros Observe Legal Reset Instruction.
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bubble [Bubble Nop]].
 destruct bubble.
 - specialize (Nop (Logic.eq_refl _)). rewrite Instruction in Nop. inversion Nop;subst instruction.
   exists 28799,19. split;[left;reflexivity|reflexivity].
 - destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [word [Size Word]].
   rewrite Instruction in Word. inversion Word;subst word.
   exact (legal_active_commit_instruction_classified_observed memory inputs k observed instruction Observe Legal Reset Bubble Instruction Size).
Qed.
Theorem reference_enable_observed_bubble memory inputs k observed bubble :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7947 (top_environment observed) = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::negb bubble]).
Proof.
 intros Observe Legal Reset Bubble.
 destruct (observed_checker_bubble_value memory inputs k observed bubble Observe Legal Reset Bubble) as [_ Valid].
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Source : VM.find 1395 (history 9257%nat) = Some (Gval (Fuint 1) [::negb bubble])).
 { rewrite (reference_control_stable_1395_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9257%nat 9259%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(lia)) Last. exact Valid. }
 rewrite <- Last.
 exact (reference_valid_normalized_after_two _ (history 9257%nat) (history 9258%nat) (history 9259%nat) _ (normalized_known _) Source (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Theorem reference_illegal_absent_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 3042 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Reset.
 destruct (observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member) as [instruction [Size Instruction]].
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bubble [Bubble Nop]].
 pose proof (reference_enable_observed_bubble memory inputs k observed bubble Observe Legal Reset Bubble) as Enabled.
 pose proof (legal_observed_instruction_classified memory inputs k observed instruction Observe Legal Reset Instruction) as Classified.
 rewrite (reference_illegal_observed_value memory inputs k observed instruction (negb bubble) Observe Legal Instruction Enabled).
 destruct bubble;[reflexivity|].
 change (Some (Gval (Fuint 1) [::reference_illegal_fold (reference_instruction_matches instruction) 48]) = Some (Gval (Fuint 1) [::false])).
 rewrite (classified_reference_illegal_false instruction Classified). reflexivity.
Qed.
