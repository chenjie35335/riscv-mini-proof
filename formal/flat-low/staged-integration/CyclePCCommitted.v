Require Import CoreSocModel ComparisonNodes FormalLocalHistory CycleView CycleInstructionCoverage ReferenceInstructionDecode ReferenceBranchOperands CycleBranchPCAdvance CycleNonredirectPCAdvance CycleJumpTarget PCRelativePendingInvariant CycleRedirectDecision JALRPendingAlignment JALRTakenInvariant PipelinePCRelation PipelinePCBubbleTransition PipelinePCResetTransition ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem cycle_pc_normal_committed memory inputs k current committed before csr :
 generated_observe memory inputs k=Some current ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_pc_aligned before ->
 cycle_pc_relative_pending before ->cycle_redirect_decision before ->cycle_jalr_pending before ->cycle_jalr_taken before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 (cv_late_bubble before=false ->VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false])) ->
 pipeline_pc_relation(top_environment committed).
Proof.
 intros Observe Legal Run Reset Before PC Relative Decision Jalr Taken CSR CSRSize Quiet.
 destruct(cv_late_bubble before)eqn:Late.
 - apply(pipeline_pc_bubble_transition memory inputs k current committed Observe Legal Run Reset(cycle_pc_relation_sound _ _ Before PC)).
   rewrite(cva_late_bubble _ _ Before)Late;reflexivity.
 - specialize(Quiet(Logic.eq_refl _)).
   destruct(cycle_commit_instruction_coverage memory inputs k current before Observe Legal Reset Before)as[row[group[Row[Group Match]]]].
   destruct(Nat.lt_ge_cases row 21)as[Small|Lower].
   + exact(cycle_nonredirect_pc_committed memory inputs k current committed before row Observe Legal Run Reset Before Late PC Decision Row (or_introl Small)Match Quiet).
   + destruct(Nat.eq_dec row 21)as[Same|NotJal].
     * subst row. exact(cycle_jump_pc_committed memory inputs k current committed before false csr Observe Legal Run Reset Before Late Match PC Relative Decision Jalr Taken CSR CSRSize Quiet).
     * destruct(Nat.eq_dec row 22)as[Same|NotJalr].
       -- subst row. exact(cycle_jump_pc_committed memory inputs k current committed before true csr Observe Legal Run Reset Before Late Match PC Relative Decision Jalr Taken CSR CSRSize Quiet).
       -- destruct(Nat.le_gt_cases row 28)as[Branch|Other].
          ++ assert(Lane:(Nat.sub row 23<6)%coq_nat)by lia.
             assert(BMatch:branch_operand_match(cv_commit_instruction before)(Nat.sub row 23)).
             { unfold branch_operand_match. replace(Nat.add 23(Nat.sub row 23))with row by lia. exact Match. }
             exact(cycle_branch_pc_committed memory inputs k current committed before(Nat.sub row 23)csr Observe Legal Run Reset Before Lane BMatch Late PC Relative Decision CSR CSRSize Quiet).
          ++ exact(cycle_nonredirect_pc_committed memory inputs k current committed before row Observe Legal Run Reset Before Late PC Decision Row (or_intror Other)Match Quiet).
Qed.

Theorem cycle_pc_committed memory inputs k current committed before csr bit :
 generated_observe memory inputs k=Some current ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k bit ->
 cycle_view_at(top_environment current)before ->cycle_pc_aligned before ->
 cycle_pc_relative_pending before ->cycle_redirect_decision before ->cycle_jalr_pending before ->cycle_jalr_taken before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 (bit=false ->cv_late_bubble before=false ->VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false])) ->
 pipeline_pc_relation(top_environment committed).
Proof.
 intros Observe Legal Run Reset Before PC Relative Decision Jalr Taken CSR CSRSize Quiet.
 destruct bit.
 - exact(pipeline_pc_reset_transition memory inputs k current committed Observe Legal Run Reset).
 - exact(cycle_pc_normal_committed memory inputs k current committed before csr Observe Legal Run Reset Before PC Relative Decision Jalr Taken CSR CSRSize(Quiet(Logic.eq_refl _))).
Qed.

Lemma cycle_pc_relation_concrete env :pipeline_pc_relation env ->map_uint_concrete 7331 32 env.
Proof. intros[pc[Width[Aligned[Value Phase]]]]. exists pc;split;assumption. Qed.
