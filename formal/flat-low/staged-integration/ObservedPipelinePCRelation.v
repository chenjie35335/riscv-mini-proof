Require Import CoreSocModel PipelinePCRelation FormalLocalHistory StagedObservedRegister StagedCircuitRegisterHold JointBoundaryRegisters JointBoundaryPreparation ReferencePCInitialization PipelineBubbleInitialization.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run generated_observe.
Lemma observed_joint_register_copy memory inputs k previous old observed node width :
 List.In (node,width) joint_boundary_registers ->
 generated_run memory inputs k = Some previous -> SVM.find nil previous = Some old ->
 generated_observe memory inputs k = Some observed ->
 VM.find (N.of_nat node) (top_environment observed) = VM.find (N.of_nat node) old.
Proof.
 intros Member Run Old Observe.
 pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [/andP [Safe NotClock] NotReset].
 destruct (joint_boundary_register_properties node width Member) as [_ Present].
 pose proof (staged_observed_register_copies memory inputs k previous old observed (N.of_nat node)
 NotClock NotReset Safe Present Run Old Observe) as Copy.
 unfold staged_register_lookup in Copy. unfold top_environment.
 destruct (SVM.find nil observed); [exact Copy|].
 exact Copy.
Qed.
Theorem observed_pipeline_pc_relation memory inputs k previous old observed :
 generated_run memory inputs k = Some previous -> SVM.find nil previous = Some old ->
 generated_observe memory inputs k = Some observed ->
 pipeline_pc_relation old -> pipeline_pc_relation (top_environment observed).
Proof.
 intros Run Old Observe Relation.
 assert (C7749 : VM.find 7749 (top_environment observed) = VM.find 7749 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7749%nat 32%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 54%nat). vm_compute. reflexivity. }
 assert (C7751 : VM.find 7751 (top_environment observed) = VM.find 7751 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7751%nat 32%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 56%nat). vm_compute. reflexivity. }
 assert (C7762 : VM.find 7762 (top_environment observed) = VM.find 7762 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7762%nat 1%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 66%nat). vm_compute. reflexivity. }
 assert (C7768 : VM.find 7768 (top_environment observed) = VM.find 7768 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7768%nat 33%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 67%nat). vm_compute. reflexivity. }
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7331
 (Logic.eq_refl true) (Logic.eq_refl true) reference_pc7331_initial_safe reference_pc7331_present Run Old Observe) as C7331.
 unfold staged_register_lookup in C7331.
 assert (E7331 : VM.find 7331 (top_environment observed) = VM.find 7331 old).
 { unfold top_environment. destruct (SVM.find nil observed); [exact C7331|]. exact C7331. }
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as C7945.
 unfold staged_register_lookup in C7945.
 assert (E7945 : VM.find 7945 (top_environment observed) = VM.find 7945 old).
 { unfold top_environment. destruct (SVM.find nil observed); [exact C7945|]. exact C7945. }
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7947
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe bubble7947_present Run Old Observe) as C7947.
 unfold staged_register_lookup in C7947.
 assert (E7947 : VM.find 7947 (top_environment observed) = VM.find 7947 old).
 { unfold top_environment. destruct (SVM.find nil observed); [exact C7947|]. exact C7947. }
 unfold pipeline_pc_relation, pipeline_pc_phase in *.
 rewrite C7749 C7751 C7762 C7768 E7331 E7945 E7947. exact Relation.
Qed.
Print Assumptions observed_pipeline_pc_relation.
