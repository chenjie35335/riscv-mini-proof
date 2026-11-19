Require Import FetchPCNopFullHistory NopBranchHistory.
Require Import CoreSocModel ComparisonNodes NopPCSelectHistory FormalInstructionResetConstants FetchPCSequentialExact FormalPCControlNodes FormalStallHistory FormalCheckerResetConnections FormalPCRegister ExceptionSourceNoTrap ExceptionPCSourceRegisters JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem fetch_pc_nop_full_history inputs path history result pc :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 7768 (history 9259%nat) = Some (Gval (Fuint 33) pc) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) (fetch_pc_plus_four pc)).
Proof.
 intros Boundary Steps Resets Nop PC NoTrap Commit.
 apply (fetch_pc_nop_full_history_given_branch inputs path history result pc Boundary Steps Resets Nop PC NoTrap).
 - apply (nop_branch_false_history_from_final _ history 9259 Nop Steps); vm_compute;lia.
 - exact Commit.
Qed.
