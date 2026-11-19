from pathlib import Path
s='''Require Import PipelinePCRelation CoreSocModel ComparisonNodes FormalLocalHistory CycleView CycleRedirectDecision DUTRedirectSemantics RFScalarControl RFALUReferenceData ReferenceInstructionDecode ReferenceNonredirectZero ReferenceIllegalObserved CycleBranchPCAdvance PipelinePCHoldReachable ReferencePCSequentialWindowFromControls PipelinePCAdjacentTransfer.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition cycle_nonredirect_class row :Prop := (row<21 \/ 28<row)%coq_nat.
Lemma cycle_nonredirect_decoder instruction row (col:nat) :
 (row<37)%coq_nat ->cycle_nonredirect_class row ->((21<=col)%coq_nat /\ (col<=28)%coq_nat) ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 N.eqb(reference_instruction_code col)(N.land(to_N instruction)(reference_instruction_mask col))=false.
Proof.
 intros Row Class [ColLower ColUpper] Match. rewrite(rf_reference_decode_onehot instruction row col Row ltac:(lia)Match).
 apply Nat.eqb_neq. unfold cycle_nonredirect_class in Class;lia.
Qed.
Lemma cycle_nonredirect_not_taken v row :
 (row<37)%coq_nat ->cycle_nonredirect_class row ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row)=reference_instruction_code row ->
 cycle_reference_taken v=false.
Proof.
 intros Row Class Match.
'''
for i in range(21,29):
 s+=f' pose proof(cycle_nonredirect_decoder(cv_commit_instruction v)row {i}%nat Row Class ltac:(lia)Match)as D{i}.\n'
 s+=f' cbv[reference_instruction_code reference_instruction_codes reference_instruction_mask reference_instruction_masks nth]in D{i}. rewrite N.eqb_sym in D{i}.\n'
s+=' unfold cycle_reference_taken,dut_reference_taken. rewrite D21 D22 D23 D24 D25 D26 D27 D28. reflexivity.\nQed.\n'
s+='''Theorem cycle_nonredirect_node memory inputs k observed v row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->
 (row<37)%coq_nat ->cycle_nonredirect_class row ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 6507(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset View Late Row Class Match.
 assert(Bubble:VM.find 7947(top_environment observed)=Some(Gval(Fuint 1)[::false]))by(rewrite(cva_late_bubble _ _ View)Late;reflexivity).
 pose proof(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Bubble)as Enabled.
 apply(reference_nonredirect_false_observed memory inputs k observed Observe Legal).
 intros node Member. cbn[reference_nonredirect_guards List.In]in Member.
'''
for i in range(21,29):
 s+=f''' destruct Member as[<-|Member].
 {{ pose proof(rf_reference_decoder_observed memory inputs k observed(cv_commit_instruction v){i}%nat Observe Legal(cva_commit_instruction _ _ View)Enabled ltac:(lia))as Value.
 rewrite(cycle_nonredirect_decoder _ row {i}%nat Row Class ltac:(lia)Match)in Value. exact Value. }}
'''
s+=' contradiction.\nQed.\n'
s+='''Theorem cycle_nonredirect_pc_committed memory inputs k current committed before row :
 generated_observe memory inputs k=Some current ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cv_late_bubble before=false ->
 cycle_pc_aligned before ->cycle_redirect_decision before ->
 (row<37)%coq_nat ->cycle_nonredirect_class row ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false]) ->
 pipeline_pc_relation(top_environment committed).
Proof.
 intros Observe Legal Run Reset Before Late PC Decision Row Class Match Quiet.
 pose proof(cycle_nonredirect_node memory inputs k current before row Observe Legal Reset Before Late Row Class Match)as Redirect.
 pose proof(adjacent_transfer_observed_reset memory inputs k current Observe Legal Reset)as RootReset.
 apply(pipeline_pc_active_no_redirect_sequential memory inputs k current committed Observe Legal Run Reset).
 - exact(reference_pc_window_from_observed_controls memory inputs k current Observe Legal RootReset Redirect Quiet).
 - exact(cycle_pc_relation_sound _ _ Before PC).
 - rewrite(cva_late_bubble _ _ Before)Late;reflexivity.
 - rewrite(cva_delayed_redirect _ _ Before)(Decision Late)(cycle_nonredirect_not_taken before row Row Class Match);reflexivity.
Qed.
'''
Path('formal/flat-low/staged-integration/CycleNonredirectPCAdvance.v').write_text(s)
