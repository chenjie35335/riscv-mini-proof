Require Import FormalObservationCommit ComparisonNodes PCRelativeAddressCycle CycleView MemoryCycleStep ReferenceLoadSemantics DUTRedirectReachability ReferenceRedirectSemantics FormalInstructionResetBase FormalInstructionResetCycle FormalInstructionResetConstants FormalLocalHistory ReferenceBankObservation JointBoundaryRegisters JointBoundaryReachable FormalFetchType CoreSocModel.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition cycle_pc_relative_pending v :Prop :=forall lane,(lane<7)%coq_nat ->pc_relative_match(cv_commit_instruction v)lane ->
 cv_pending_alu v=reference_load_address(cv_reference_pc v)(pc_relative_immediate lane(cv_commit_instruction v)).
Lemma cycle_pc_relative_pending_nop v :cv_commit_instruction v=instruction_nop ->cycle_pc_relative_pending v.
Proof. intros Nop lane Lane Match. rewrite Nop in Match;exfalso;exact(pc_relative_match_not_nop lane Lane Match). Qed.
Theorem cycle_pc_relative_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_pc_relative_pending v.
Proof.
 intros Observe View. pose proof Observe as Prepare.
 unfold generated_observe,generated_observe_cycle in Prepare.
 destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate].
 destruct(instruction_run_zero memory inputs committed Run)as[env[Env[Front Nop]]].
 pose proof(joint_register_run_observed memory inputs 0 committed observed 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run Observe)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ View)in Copy.
 apply cycle_pc_relative_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_pc_relative_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_pc_relative_pending after.
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
 apply cycle_pc_relative_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_pc_relative_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_pc_aligned after ->cycle_pc_relative_pending after.
Proof.
 intros Transition Reset Before After Aligned lane Lane Match.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 rewrite Instruction in Match.
 exact(proj2(cycle_pc_relative_pending_step lane memory inputs k current next before after Transition Reset Before After Lane Match Aligned)).
Qed.
(* The after-PC premise is explicit: a joint induction first establishes its PC
   component using the previous pending component, then establishes this one. *)
Theorem cycle_pc_relative_pending_preserved memory inputs k current next before after reset :
 cycle_transition memory inputs k current next ->cycle_reset inputs k reset ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (reset=false ->cycle_pc_aligned after) ->cycle_pc_relative_pending after.
Proof.
 intros Transition Reset Before After Aligned. destruct reset.
 - exact(cycle_pc_relative_pending_reset memory inputs k current next after Transition Reset After).
 - exact(cycle_pc_relative_pending_normal memory inputs k current next before after Transition Reset Before After(Aligned(Logic.eq_refl _))).
Qed.
Theorem cycle_pc_relative_pending_target_aligned lane memory inputs k observed v compressed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cycle_pc_aligned v ->cycle_pc_relative_pending v ->
 (lane<7)%coq_nat ->pc_relative_match(cv_commit_instruction v)lane ->cv_delayed_redirect v=true ->
 reference_redirect_aligned compressed(to_N(cv_reference_pc v)+to_N(pc_relative_immediate lane(cv_commit_instruction v)))=true.
Proof.
 intros Observe Legal Reset View Aligned Pending Lane Match Taken.
 pose proof(Pending lane Lane Match)as Target.
 assert(Low0:N.testbit(to_N(cv_pending_alu v))0=false).
 { rewrite Target. apply pc_relative_address_low_zero;[apply pc_relative_aligned_low_zero;exact(proj1 Aligned)|apply pc_relative_immediate_low_zero]. }
 pose proof(dut_no_trap_target_bit_observed memory inputs k observed(cv_pending_alu v)Observe Legal Reset ltac:(rewrite(cva_delayed_redirect _ _ View)Taken;reflexivity)(cva_pending_alu _ _ View)(cva_pending_width _ _ View))as Low1.
 assert(Result:reference_redirect_aligned compressed(to_N(cv_pending_alu v))=true)by(rewrite reference_redirect_aligned_bits Low0 Low1;destruct compressed;reflexivity).
 rewrite Target in Result. unfold reference_load_address in Result;rewrite reference_redirect_aligned_take32_from33 in Result;exact Result.
Qed.
