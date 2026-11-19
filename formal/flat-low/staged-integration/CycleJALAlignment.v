Require Import CycleView CycleRedirectDecision PCRelativeAddressCycle PCRelativePendingInvariant ReferenceJALAlignment ReferenceRedirectSemantics DUTRedirectSemantics CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma cycle_jal_reference_taken v :pc_relative_match(cv_commit_instruction v)6 ->cycle_reference_taken v=true.
Proof.
 intro Match. change(N.land(to_N(cv_commit_instruction v))127=111)in Match.
 unfold cycle_reference_taken,dut_reference_taken. rewrite Match N.eqb_refl. btauto.
Qed.
Theorem cycle_jal_alignment_guard memory inputs k observed v csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 pc_relative_match(cv_commit_instruction v)6 ->cv_late_bubble v=false ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 2966(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Match Late PC Pending Decision Csr CsrSize.
 assert(Taken:cv_delayed_redirect v=true).
 { rewrite(Decision Late). exact(cycle_jal_reference_taken v Match). }
 pose proof(pc_relative_reference_immediate_observed 6 memory inputs k observed(cv_commit_instruction v)
 ltac:(lia)Observe Legal Reset(cva_commit_instruction _ _ View)Match)as Immediate.
 pose proof(reference_jal_alignment_observed memory inputs k observed(cv_reference_pc v)
 (pc_relative_immediate 6(cv_commit_instruction v))csr Observe Legal(cva_reference_pc _ _ View)Immediate Csr(cva_reference_pc_width _ _ View)CsrSize)as Value.
 rewrite(cycle_pc_relative_pending_target_aligned 6 memory inputs k observed v(N.testbit(to_N csr)2)
 Observe Legal Reset View PC Pending ltac:(lia)Match Taken)in Value.
 exact Value.
Qed.
