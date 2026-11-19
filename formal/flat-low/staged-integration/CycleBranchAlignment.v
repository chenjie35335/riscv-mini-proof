Require Import CycleBranchRedirect ReferenceBranchComparisons CycleView CycleRedirectDecision ReferenceBranchOperands PCRelativeAddressCycle PCRelativePendingInvariant CyclePCAlignmentGuards ReferenceRedirectAlignmentObserved ReferenceRedirectSemantics DUTRedirectSemantics RFScalarControl ReferenceInstructionDecode RFReadPorts ObservedJointRegisterConcrete LoadTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith ZArith List Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition branch_comparison_node lane :VarOrder.T:=nth 0[::2912;2892;2872;2850;2830;2806]lane.
Definition branch_alignment_node lane :VarOrder.T:=nth 0[::2929;2909;2889;2867;2847;2825]lane.
Definition branch_comparison lane left right :bool:=nth false
 [::N.eqb left right;negb(N.eqb left right);
 Z.ltb(reference_redirect_signed left)(reference_redirect_signed right);N.ltb left right;
 Z.leb(reference_redirect_signed right)(reference_redirect_signed left);N.leb right left]lane.
Lemma branch_reference_taken instruction lane left right :(lane<6)%coq_nat ->branch_operand_match instruction lane ->
 (dut_reference_taken(to_N instruction)left right || N.eqb(N.land(to_N instruction)28799)103)=branch_comparison lane left right.
Proof.
 intros Lane Match.
 assert(NotJal:N.eqb(N.land(to_N instruction)127)111=false).
 { rewrite N.eqb_sym.
 change(N.eqb(reference_instruction_code 21)(N.land(to_N instruction)(reference_instruction_mask 21))=false).
 rewrite(rf_reference_decode_onehot instruction(Nat.add 23 lane)21 ltac:(lia)ltac:(lia)Match).
 apply Nat.eqb_neq;lia. }
 rewrite(branch_operand_not_jalr _ _ Lane Match)Bool.orb_false_r.
 unfold dut_reference_taken.
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=99)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=4195)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=16483)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=24675)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=20579)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 destruct lane as[|lane];[change(N.land(to_N instruction)28799=28771)in Match;rewrite Match NotJal;cbv[branch_comparison seq.nth];cbn[N.eqb Pos.eqb];btauto|].
 lia.
Qed.
Theorem cycle_branch_comparison_observed memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->(lane<6)%coq_nat ->branch_operand_match(cv_commit_instruction v)lane ->
 VM.find(branch_comparison_node lane)(top_environment observed)=Some(Gval(Fuint 1)
 [::branch_comparison lane
 (to_N(cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v)))))
 (to_N(cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v)))))]).
Proof.
 intros Observe Legal Reset View Lane Match.
 destruct(reference_branch_operands_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View))as[Rs1 Rs2].
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[instruction[Size Inst]].
 rewrite(cva_commit_instruction _ _ View)in Inst;inversion Inst;subst instruction.
 assert(BankSize:forall second,size(cv_reference_bank v(to_nat(rf_instruction_address second(cv_commit_instruction v))))=32%nat).
 { intro second. assert(Bound:(to_nat(rf_instruction_address second(cv_commit_instruction v))<32)%coq_nat).
 { pose proof(to_nat_bounded(rf_instruction_address second(cv_commit_instruction v)))as H.
 rewrite(rf_instruction_address_size second _ Size)in H. exact(elimT ltP H). }
 exact(proj1(cva_reference_bank _ _ View _ Bound)). }
 destruct(reference_branch_comparisons_observed memory inputs k observed
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))
 (cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v))))
 Observe Legal Rs1 Rs2(BankSize false)(BankSize true))as[H0[H1[H2[H3[H4 H5]]]]].
 do 6(destruct lane as[|lane];[cbn[branch_comparison_node branch_comparison nth];assumption|]);lia.
Qed.
Theorem cycle_branch_alignment_from_comparison memory inputs k observed v lane csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->(lane<6)%coq_nat ->branch_operand_match(cv_commit_instruction v)lane ->
 cv_late_bubble v=false ->cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find(branch_comparison_node lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find(branch_alignment_node lane)(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Lane Match Late PC Pending Decision Csr CsrSize Test.
 pose proof(cycle_branch_comparison_observed memory inputs k observed v lane Observe Legal Reset View Lane Match)as Compare.
 rewrite Test in Compare.
 specialize(Decision Late). unfold cycle_reference_taken in Decision.
 rewrite(branch_reference_taken _ _ _ _ Lane Match)in Decision.
 assert(Taken:cv_delayed_redirect v=true)by(congruence).
 destruct(reference_branch_operands_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View))as[Rs1 Rs2].
 apply(cycle_pc_pending_alignment_guards(Nat.sub 5 lane)memory inputs k observed v
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))csr
 Observe Legal Reset View PC Pending ltac:(lia)(branch_operand_pc_match _ _ Lane Match)Taken Rs1 Csr CsrSize).
 do 6(destruct lane as[|lane];[vm_compute;tauto|]);lia.
Qed.
