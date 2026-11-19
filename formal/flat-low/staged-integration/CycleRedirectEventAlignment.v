Require Import CycleBranchAlignment CycleJALAlignment JALRPendingAlignment JALRTakenInvariant
 CycleView CycleRedirectDecision PCRelativePendingInvariant ReferenceInstructionDecode RFALUReferenceData
 ReferenceIllegalObserved ReferenceBranchOperands PCRelativeAddressCycle JALRAddressCycle
 CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma cycle_active_reference_decode memory inputs k observed v row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->(row<48)%coq_nat ->
 VM.find(reference_instruction_guard row)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros Observe Legal Reset View Late Row Active.
 pose proof(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset
 ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity))as Enabled.
 pose proof(rf_reference_decoder_observed memory inputs k observed(cv_commit_instruction v)row Observe Legal(cva_commit_instruction _ _ View)Enabled Row)as Decode.
 rewrite Active in Decode.
 assert(Match:N.eqb(reference_instruction_code row)(N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row))=true)by congruence.
 apply N.eqb_eq in Match;exact(Logic.eq_sym Match).
Qed.
Theorem cycle_branch_event_alignment memory inputs k observed v lane csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->(lane<6)%coq_nat ->
 VM.find(reference_instruction_guard(Nat.add 23 lane))(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find(branch_comparison_node lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find(branch_alignment_node lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Late PC Pending Decision Csr Size Lane Active Compare.
 pose proof(cycle_active_reference_decode memory inputs k observed v(Nat.add 23 lane)Observe Legal Reset View Late ltac:(lia)Active)as Match.
 exact(cycle_branch_alignment_from_comparison memory inputs k observed v lane csr Observe Legal Reset View Lane Match Late PC Pending Decision Csr Size Compare).
Qed.
Theorem cycle_jalr_event_alignment memory inputs k observed v csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->cycle_jalr_pending v ->cycle_jalr_taken v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 2010(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2949(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Late Pending Taken Csr Size Active.
 pose proof(cycle_active_reference_decode memory inputs k observed v 22 Observe Legal Reset View Late ltac:(lia)Active)as Match.
 exact(cycle_jalr_alignment_guard memory inputs k observed v csr Observe Legal Reset View Pending Match(Taken Match)Csr Size).
Qed.
Theorem cycle_jal_event_alignment memory inputs k observed v csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 2357(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2966(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Late PC Pending Decision Csr Size Active.
 pose proof(cycle_active_reference_decode memory inputs k observed v 21 Observe Legal Reset View Late ltac:(lia)Active)as Match.
 exact(cycle_jal_alignment_guard memory inputs k observed v csr Observe Legal Reset View Match Late PC Pending Decision Csr Size).
Qed.
Theorem cycle_branch_event_comparison memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->(lane<6)%coq_nat ->
 VM.find(reference_instruction_guard(Nat.add 23 lane))(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 exists bit,VM.find(branch_comparison_node lane)(top_environment observed)=Some(Gval(Fuint 1)[::bit]).
Proof.
 intros Observe Legal Reset View Late Lane Active.
 pose proof(cycle_active_reference_decode memory inputs k observed v(Nat.add 23 lane)Observe Legal Reset View Late ltac:(lia)Active)as Match.
 eexists. exact(cycle_branch_comparison_observed memory inputs k observed v lane Observe Legal Reset View Lane Match).
Qed.
