Require Import FormalObservationCommit ComparisonNodes CycleView FormalInstructionResetBase FormalInstructionResetCycle FormalInstructionResetConstants FormalLocalHistory ReferenceBankObservation JointBoundaryRegisters JointBoundaryReachable FormalFetchType CoreSocModel.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem cycle_initial_commit_nop memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cv_commit_instruction v=instruction_nop.
Proof.
 intros Observe View. pose proof Observe as Prepare.
 unfold generated_observe,generated_observe_cycle in Prepare.
 destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate].
 destruct(instruction_run_zero memory inputs committed Run)as[env[Env[Front Nop]]].
 pose proof(joint_register_run_observed memory inputs 0 committed observed 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run Observe)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ View)in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_reset_commit_nop memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cv_commit_instruction after=instruction_nop.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset After.
 pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 destruct(joint_boundary_reachable memory inputs k previous Previous Legal)as[Registers Storage].
 unfold top_environment in Registers;rewrite Old in Registers.
 destruct(Registers 7748%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[front[FrontSize Front]].
 destruct(Registers 7750%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[instruction[Size Instruction]].
 destruct(instruction_real_reset_cycle (generated_observation_input inputs k)previous old committed(Gval(Fuint 32)front)(Gval(Fuint 32)instruction)Old Front(Logic.eq_refl _)Instruction(Logic.eq_refl _)Reset Cycle)as[env[Env[FrontNop Nop]]].
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ After)in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
