Require Import CoreSocModel FormalLocalHistory PipelinePCAdjacentTransfer ObservedPipelinePCRelation JointBoundaryRegisters.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem observed_pipeline_pc_adjacency memory inputs k previous old observed :
 generated_run memory inputs k = Some previous ->
 SVM.find nil previous = Some old ->
 generated_observe memory inputs k = Some observed ->
 (pipeline_front_fetch_adjacent old -> pipeline_front_fetch_adjacent (top_environment observed)) /\
 (pipeline_commit_front_adjacent old -> pipeline_commit_front_adjacent (top_environment observed)).
Proof.
 intros Run Old Observe.
 assert (Front : VM.find 7749 (top_environment observed) = VM.find 7749 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7749%nat 32%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 54%nat). vm_compute. reflexivity. }
 assert (Commit : VM.find 7751 (top_environment observed) = VM.find 7751 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7751%nat 32%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 56%nat). vm_compute. reflexivity. }
 assert (Fetch : VM.find 7768 (top_environment observed) = VM.find 7768 old).
 { apply (observed_joint_register_copy memory inputs k previous old observed 7768%nat 33%nat); try assumption.
   apply (List.nth_error_In joint_boundary_registers 67%nat). vm_compute. reflexivity. }
 split.
 - intros [front [fetch [Size [F [P Adjacent]]]]].
   exists front,fetch. rewrite Front Fetch. split; [exact Size|]. split; [exact F|]. split; assumption.
 - intros [commit [front [C [F Adjacent]]]].
   exists commit,front. rewrite Commit Front. split; [exact C|]. split; assumption.
Qed.
