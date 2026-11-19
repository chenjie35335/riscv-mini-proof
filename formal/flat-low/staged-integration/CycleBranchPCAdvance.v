Require Import ReferenceRedirectSpine ReferenceBranchOperands PipelinePCRelation.
Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalFetchType CycleView CycleViewConstruction ObservedPipelinePCRelation PipelinePCHoldReachable PipelinePCSuccessor ReferencePCRedirectObserved ReferencePCSequentialWindowFromControls CycleBranchRedirect CycleBranchTarget PCRelativePendingInvariant PCRelativeAddressCycle CycleRedirectDecision ReferenceRedirectSemantics ObservedCheckerBubbleValue PipelinePCAdjacentTransfer.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma cycle_even_redirect_word word : size word=32%nat ->N.testbit(to_N word)0=false ->
 take 32(pipeline_redirect_target word)=word.
Proof.
 intros Size Low. rewrite(pipeline_redirect_target_bits word Size).
 rewrite(redirect_to_N_testbit _ 0%nat)in Low.
 destruct word as[|bit tail];[discriminate Size|]. cbn[nth drop]in Low |-*. subst bit.
rewrite drop0.
 change(false :: take 31(tail++[::false])=false::tail).
 assert(Tail:size tail=31%nat)by(inversion Size;reflexivity).
 rewrite take_cat Tail ltnn subnn take0 cats0;reflexivity.
Qed.

Theorem cycle_pc_aligned_from_committed memory inputs k committed observed v :
 generated_run memory inputs k=Some committed ->generated_observe memory inputs k=Some observed ->
 cycle_view_at(top_environment observed)v ->pipeline_pc_relation(top_environment committed) ->cycle_pc_aligned v.
Proof.
 intros Run Observe View Relation.
 destruct(fetch9220_run_type memory inputs k committed Run)as[old[value[Old Rest]]].
 apply(cycle_pc_relation_complete _ v View).
 apply(observed_pipeline_pc_relation memory inputs k committed old observed Run Old Observe).
 unfold top_environment in Relation;rewrite Old in Relation;exact Relation.
Qed.

Theorem cycle_branch_pc_committed memory inputs k current committed before lane csr :
 generated_observe memory inputs k=Some current ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->
 (lane<6)%coq_nat ->branch_operand_match(cv_commit_instruction before)lane ->
 cv_late_bubble before=false ->cycle_pc_aligned before ->cycle_pc_relative_pending before ->cycle_redirect_decision before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false]) ->
 pipeline_pc_relation(top_environment committed).
Proof.
 intros Observe Legal Run Reset Before Lane Match Late PC Pending Decision CSR CSRSize Quiet.
 pose proof(cycle_branch_redirect_observed memory inputs k current before lane csr Observe Legal Reset Before Lane Match Late PC Pending Decision CSR CSRSize)as Redirect.
 pose proof(adjacent_transfer_observed_reset memory inputs k current Observe Legal Reset)as RootReset.
 assert(LateNode:VM.find 7947(top_environment current)=Some(Gval(Fuint 1)[::false])).
 { rewrite(cva_late_bubble _ _ Before)Late;reflexivity. }
 destruct(cv_delayed_redirect before)eqn:Taken.
 - apply(pipeline_pc_active_redirect_target memory inputs k current committed Observe Legal Run Reset LateNode).
   + rewrite(cva_delayed_redirect _ _ Before)Taken;reflexivity.
   + intros word Width Word.
     rewrite(cva_pending_alu _ _ Before)in Word;inversion Word;subst word.
     assert(Low:N.testbit(to_N(cv_pending_alu before))0=false).
     { rewrite(Pending(Nat.sub 5 lane)ltac:(lia)(branch_operand_pc_match _ lane Lane Match)).
       apply pc_relative_address_low_zero;[apply pc_relative_aligned_low_zero;exact(proj1 PC)|apply pc_relative_immediate_low_zero]. }
     rewrite(cycle_even_redirect_word _ Width Low).
     destruct(observed_checker_bubble_value memory inputs k current false Observe Legal Reset LateNode)as[Valid Enabled].
     exact(reference_pc_redirect_observed memory inputs k current committed(cv_reference_pc before)(cv_pending_alu before)
      Observe Legal Run RootReset(cva_pending_width _ _ Before)(cva_reference_pc _ _ Before)Enabled Redirect Quiet
      (cycle_branch_target_observed memory inputs k current before lane csr Observe Legal Reset Before Lane Match Late Taken PC Pending Decision CSR CSRSize)).
 - apply(pipeline_pc_active_no_redirect_sequential memory inputs k current committed Observe Legal Run Reset).
   + exact(reference_pc_window_from_observed_controls memory inputs k current Observe Legal RootReset Redirect Quiet).
   + exact(cycle_pc_relation_sound _ _ Before PC).
   + exact LateNode.
   + rewrite(cva_delayed_redirect _ _ Before)Taken;reflexivity.
Qed.
