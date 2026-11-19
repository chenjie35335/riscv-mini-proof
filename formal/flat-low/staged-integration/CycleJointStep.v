Require Import CoreSocModel ComparisonNodes FormalLocalHistory CycleView CycleViewConstruction
 CycleJointReachability CycleDataReachability CycleDataNormalStep CycleISAReferenceAdvance
 CyclePCCommitted CycleBranchPCAdvance ReferencePCConcreteCycle ReferenceMISAConcrete
 CycleNextView CycleResetView CycleInstructionClassReachable RFArithmeticPendingClosure RFModeReachability
 RFAddPendingInvariant RFBitwisePendingInvariant RFSubtractPendingInvariant RFComparePendingInvariant
 RFCompareImmediatePendingInvariant RFShiftPendingInvariant RFUpperPendingInvariant
 MemoryPendingInvariant StorePendingInvariant PCRelativePendingInvariant CycleRedirectDecision
 JALRPendingAlignment JALRPendingInvariant JALRTakenInvariant ConcreteRegisterInitialization.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.

Theorem cycle_joint_step_with_quiet memory inputs k current next before bit :
 cycle_transition memory inputs k current next ->cycle_reset inputs k bit ->
 cycle_view_at(top_environment current)before ->cycle_pc_aligned before ->
 cycle_joint_pending(top_environment current)before ->
 (bit=false ->cv_late_bubble before=false ->VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false])) ->
 exists after,cycle_view_at(top_environment next)after /\cycle_pc_aligned after /\
 cycle_joint_pending(top_environment next)after.
Proof.
 intros Transition Reset Before PC Joint Quiet.
 pose proof Transition as Context.
 destruct Context as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 destruct Joint as[Data[Relative[Redirect[Jalr Taken]]]].
 destruct Data as[Banks[Arithmetic[Memory[Store Assertion]]]].
 destruct Arithmetic as[Add[Bitwise[Subtract[Compare[Immediate[Shift Upper]]]]]].
 destruct(reference_misa_observed_concrete memory inputs k current Observe Legal)as[csr[CSRSize CSR]].
 assert(Pending:cycle_isa_pending before).
 { constructor;try assumption.
   - exact(cycle_writeback_mode_reachable memory inputs k current before Observe Legal Before).
   - exact(proj2 PC). }
 pose proof(cycle_pc_committed memory inputs k current committed before csr bit Observe Legal Run Reset Before PC
 Relative Redirect Jalr Taken CSR CSRSize Quiet)as CommittedPC.
 assert(NextPC:map_uint_concrete 7331 32(top_environment next)).
 { exact(reference_pc_concrete_run_observed memory inputs(S k)committed next Run NextObserve
   (cycle_pc_relation_concrete _ CommittedPC)). }
 set(after:=cycle_snapshot(top_environment next)).
 assert(After:cycle_view_at(top_environment next)after).
 { unfold after. destruct bit.
   - exact(cycle_view_reset_next memory inputs k current next before Transition Reset Before NextPC).
   - exact(cycle_view_normal_next memory inputs k current next before csr Transition Reset Before Banks Pending CSR CSRSize NextPC). }
 assert(Aligned:cycle_pc_aligned after).
 { exact(cycle_pc_aligned_from_committed memory inputs(S k)committed next after Run NextObserve After CommittedPC). }
 exists after. split;[exact After|]. split;[exact Aligned|].
 destruct bit.
 - split.
   + exact(cycle_data_reset_step memory inputs k current next before after Transition Reset Before After).
   + split;[exact(cycle_pc_relative_pending_reset memory inputs k current next after Transition Reset After)|].
     split.
     { intro Late. pose proof(cycle_late_bubble_reset memory inputs k current next after Transition Reset After);congruence. }
     split;[exact(cycle_jalr_pending_reset memory inputs k current next after Transition Reset After)|].
     exact(cycle_jalr_taken_reset memory inputs k current next after Transition Reset After).
 - destruct(cycle_commit_instruction_reference_row memory inputs k current before Observe Legal Reset Before)as[row[Row Match]].
   pose proof(cycle_isa_reference_advance memory inputs k current next before after row csr
     Transition Reset Before After Banks Pending Row Match CSR CSRSize)as Effect.
   split.
   + exact(cycle_data_normal_step memory inputs k current next before after row csr
       Transition Reset Before After Banks Pending Row Match CSR CSRSize).
   + split;[exact(cycle_pc_relative_pending_normal memory inputs k current next before after Transition Reset Before After Aligned)|].
     split;[exact(cycle_redirect_decision_normal memory inputs k current next before after Transition Reset Before After Banks Effect)|].
     split;[exact(cycle_jalr_pending_normal memory inputs k current next before after Transition Reset Before After Banks Effect)|].
     exact(cycle_jalr_taken_normal memory inputs k current next before after Transition Reset Before After).
Qed.

Require Import CycleReferenceNoException.
Theorem cycle_joint_step memory inputs k current next before bit :
 cycle_transition memory inputs k current next ->cycle_reset inputs k bit ->
 cycle_view_at(top_environment current)before ->cycle_pc_aligned before ->
 cycle_joint_pending(top_environment current)before ->
 exists after,cycle_view_at(top_environment next)after /\cycle_pc_aligned after /\
 cycle_joint_pending(top_environment next)after.
Proof.
 intros Transition Reset Before PC Joint.
 apply(cycle_joint_step_with_quiet memory inputs k current next before bit Transition Reset Before PC Joint).
 intros FalseBit Late. subst bit.
 destruct Joint as[[Banks[Arithmetic[Memory Rest]]][Relative[Decision[Jalr Taken]]]].
 exact(cycle_reference_no_exception_active memory inputs k current before
   (proj1 Transition)(proj1(proj2 Transition))Reset Before Late Memory PC Relative Decision Jalr Taken).
Qed.
