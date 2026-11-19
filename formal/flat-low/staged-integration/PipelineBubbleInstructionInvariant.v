Require Import CoreSocModel FormalLocalHistory FormalInstructionResetBase FormalInstructionResetConstants ObservedPipelinePCRelation StagedObservedRegister StagedCircuitRegisterHold PipelineBubbleInitialization JointBoundaryRegisters.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition early_bubble_nop env : Prop :=
 VM.find 7945 env = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7748 env = Some (Gval (Fuint 32) instruction_nop).
Theorem early_bubble_nop_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ early_bubble_nop env.
Proof.
 intro Run. destruct (instruction_run_zero memory inputs states Run) as [env [Env [Early Late]]].
 exists env. split; [exact Env|]. intro Bubble. exact Early.
Qed.
Theorem early_bubble_nop_observed memory inputs k previous old observed :
 generated_run memory inputs k = Some previous -> SVM.find nil previous = Some old ->
 generated_observe memory inputs k = Some observed ->
 early_bubble_nop old -> early_bubble_nop (top_environment observed).
Proof.
 intros Run Old Observe Invariant Bubble.
 pose proof (staged_observed_register_copies memory inputs k previous old observed 7945
 (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe bubble7945_present Run Old Observe) as Copy.
 assert (Same : VM.find 7945 (top_environment observed) = VM.find 7945 old).
 { unfold top_environment. unfold staged_register_lookup in Copy.
   destruct (SVM.find nil observed); exact Copy. }
 rewrite Same in Bubble. specialize (Invariant Bubble).
 rewrite (observed_joint_register_copy memory inputs k previous old observed 7748%nat 32%nat
 ltac:(apply (List.nth_error_In joint_boundary_registers 53%nat); vm_compute;reflexivity) Run Old Observe).
 exact Invariant.
Qed.
Print Assumptions early_bubble_nop_run_zero.
Print Assumptions early_bubble_nop_observed.
