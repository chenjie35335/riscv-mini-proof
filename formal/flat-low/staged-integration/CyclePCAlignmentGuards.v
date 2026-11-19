Require Import MemoryCycleStep CycleView PCRelativeAddressCycle ReferenceRedirectAlignmentObserved ReferenceRedirectSemantics FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* The PC invariant remains explicit; this adapter does not assert its preservation. *)
Theorem cycle_pc_relative_alignment_guards lane memory inputs k current next before after rs1 csr :
 cycle_transition memory inputs k current next ->
 cycle_reset inputs k false -> cycle_reset inputs(S k)false ->
 cycle_view_at(top_environment current)before -> cycle_view_at(top_environment next)after ->
 (lane<7)%coq_nat -> pc_relative_match(cv_front_instruction before)lane ->
 cycle_pc_aligned after -> cv_delayed_redirect after=true ->
 VM.find 2209(top_environment next)=Some(Gval(Fuint 32)rs1) ->
 VM.find 7332(top_environment next)=Some(Gval(Fuint 32)csr) -> size csr=32%nat ->
 forall node,List.In node reference_pc_alignment_nodes ->
 VM.find node(top_environment next)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Transition Reset NextReset Before After Lane Match Aligned Taken Rs1 Csr CsrSize.
 pose proof(cycle_pc_relative_taken_sum_aligned lane memory inputs k current next before after
 (N.testbit(to_N csr)2) Transition Reset NextReset Before After Lane Match Aligned Taken)as Sum.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 assert(CommitMatch:pc_relative_match(cv_commit_instruction after)lane).
 { rewrite Instruction. exact Match. }
 destruct Transition as[Observe[Legal[NextObserve[NextLegal Run]]]].
 pose proof(pc_relative_reference_immediate_observed lane memory inputs(S k)next
 (cv_commit_instruction after) Lane NextObserve NextLegal NextReset
 (cva_commit_instruction _ _ After) CommitMatch)as Immediate.
 exact(reference_pc_alignment_guards_true memory inputs(S k)next rs1
 (pc_relative_immediate lane(cv_commit_instruction after))(cv_reference_pc after)csr
 NextObserve NextLegal Rs1 Immediate(cva_reference_pc _ _ After)Csr
 (cva_reference_pc_width _ _ After)CsrSize Sum).
Qed.
Require Import PCRelativePendingInvariant CoreSocModel.
Theorem cycle_pc_pending_alignment_guards lane memory inputs k observed v rs1 csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->
 (lane<7)%coq_nat ->pc_relative_match(cv_commit_instruction v)lane ->cv_delayed_redirect v=true ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 forall node,List.In node reference_pc_alignment_nodes ->
 VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Aligned Pending Lane Match Taken Rs1 Csr CsrSize.
 pose proof(cycle_pc_relative_pending_target_aligned lane memory inputs k observed v
 (N.testbit(to_N csr)2) Observe Legal Reset View Aligned Pending Lane Match Taken)as Sum.
 pose proof(pc_relative_reference_immediate_observed lane memory inputs k observed
 (cv_commit_instruction v) Lane Observe Legal Reset(cva_commit_instruction _ _ View)Match)as Immediate.
 exact(reference_pc_alignment_guards_true memory inputs k observed rs1
 (pc_relative_immediate lane(cv_commit_instruction v))(cv_reference_pc v)csr
 Observe Legal Rs1 Immediate(cva_reference_pc _ _ View)Csr(cva_reference_pc_width _ _ View)CsrSize Sum).
Qed.
