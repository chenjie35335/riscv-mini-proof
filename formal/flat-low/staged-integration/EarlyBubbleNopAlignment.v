Require Import CoreSocModel ComparisonNodes EarlyBubbleNopControlCongruence EarlyBubbleInstructionControl EarlyControlStabilityHistory ExceptionStabilityHistory ExceptionPCSourceRegisters StartupFlagInitialization JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem early_bubble_nop_control_alignment inputs path history :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7944 (history 9259%nat) = VM.find 7796 (history 9257%nat).
Proof.
 intros Boundary Steps.
 transitivity (VM.find 7944 (history 9257%nat)).
 - apply (early_bubble_control_congruent_after_three (formal_invalid_policy inputs path)
   (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat)
   (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat)).
   + rewrite (flat_register_history_same _ history 9259 7762 startup_register_present Steps 9256 ltac:(vm_compute;lia)).
     rewrite (flat_register_history_same _ history 9259 7762 startup_register_present Steps 9254 ltac:(vm_compute;lia)). reflexivity.
   + apply (early_control_stable_85_history inputs path history 9259 Boundary Steps); vm_compute;lia.
   + apply (early_control_stable_1360_history inputs path history 9259 Boundary Steps); vm_compute;lia.
   + apply (exception_stable_128_history inputs path history 9259 Boundary Steps); vm_compute;lia.
   + apply Steps. vm_compute;lia.
   + apply Steps. vm_compute;lia.
   + apply Steps. vm_compute;lia.
   + apply Steps. vm_compute;lia.
   + apply Steps. vm_compute;lia.
   + apply Steps. vm_compute;lia.
 - exact (early_bubble_instruction_control_after_three (formal_invalid_policy inputs path)
   (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat)
   (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia))
   (Steps 9256%nat ltac:(vm_compute;lia))).
Qed.
Print Assumptions early_bubble_nop_control_alignment.
