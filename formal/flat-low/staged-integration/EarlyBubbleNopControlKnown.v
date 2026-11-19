Require Import CoreSocModel ComparisonNodes EarlyBubbleValues EarlyControlWireBitNormalization EarlyControlStabilityHistory ExceptionStabilityHistory ExceptionEventHistory JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization StartupFlagInitialization NormalizedBit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma early_bubble_normalized_concrete env node value :
 VM.find node env = Some value -> normalized_bit value ->
 (exists width bits, VM.find node env = Some (Gval (Fuint width) bits)) ->
 exists bit, VM.find node env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Value Normal [width [bits Concrete]].
 destruct Normal as [bit| | |].
 - exists bit. exact Value.
 - rewrite Concrete in Value. discriminate Value.
 - rewrite Concrete in Value. discriminate Value.
 - rewrite Concrete in Value. discriminate Value.
Qed.
Theorem early_bubble_nop_control_known inputs path history :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 exists bit, VM.find 7944 (history 9259%nat) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Boundary Steps.
 destruct (joint_update_register_history_concrete _ history 9259 7762 1 startup_register_member
 (Boundary 7762%nat 1%nat startup_register_member) Steps 9256 ltac:(vm_compute;lia)) as [started [StartedSize Started]].
 destruct started as [|start tail]; [discriminate StartedSize|].
 destruct tail as [|extra tail]; [|discriminate StartedSize].
 destruct (early_control_wire_85_normalized _ (history 9255%nat) (history 9255%nat) (history 9256%nat)
 (Steps 9255%nat ltac:(vm_compute;lia))) as [killValue [KillValue KillNormal]].
 destruct (early_bubble_normalized_concrete _ 85 killValue KillValue KillNormal
 (early_control_concrete_85_history inputs path history 9259 Boundary Steps 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [kill Kill].
 destruct (early_control_wire_1360_normalized _ (history 9256%nat) (history 9256%nat) (history 9257%nat)
 (Steps 9256%nat ltac:(vm_compute;lia))) as [branchValue [BranchValue BranchNormal]].
 destruct (early_bubble_normalized_concrete _ 1360 branchValue BranchValue BranchNormal
 (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 destruct (exception_source128_normalized _ (history 9257%nat) (history 9257%nat) (history 9258%nat)
 (Steps 9257%nat ltac:(vm_compute;lia))) as [exceptionValue [ExceptionValue ExceptionNormal]].
 destruct (early_bubble_normalized_concrete _ 128 exceptionValue ExceptionValue ExceptionNormal
 (exception_concrete_128_history inputs path history 9259 Boundary Steps 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [exception Exception].
 exists (((start || kill) || branch) || exception).
 exact (early_bubble_value_after_three (formal_invalid_policy inputs path)
 (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat)
 start kill branch exception Started Kill Branch Exception
 (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia))
 (Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Print Assumptions early_bubble_nop_control_known.
