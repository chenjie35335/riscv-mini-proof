Require Import CycleView CycleRedirectDecision ReferenceBranchOperands PCRelativeAddressCycle PCRelativePendingInvariant ReferenceRedirectSemantics DUTRedirectSemantics DelayedDUTRedirectSemantics ObservedCheckerBubbleValue ObservedJointRegisterConcrete LoadTypeCorrespondence CoreSocModel FormalLocalHistory RFReadPorts ReferenceInstructionDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma branch_operand_pc_match instruction lane :(lane<6)%coq_nat ->branch_operand_match instruction lane ->pc_relative_match instruction(Nat.sub 5 lane).
Proof. do 6(destruct lane as[|lane];[exact(fun _ H=>H)|]);lia. Qed.
Lemma branch_operand_not_jalr instruction lane :(lane<6)%coq_nat ->branch_operand_match instruction lane ->
 N.eqb(N.land(to_N instruction)28799)103=false.
Proof.
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=99)in Match;rewrite Match;reflexivity|].
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=4195)in Match;rewrite Match;reflexivity|].
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=16483)in Match;rewrite Match;reflexivity|].
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=24675)in Match;rewrite Match;reflexivity|].
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=20579)in Match;rewrite Match;reflexivity|].
 destruct lane as[|lane];[intros Bound Match;change(N.land(to_N instruction)28799=28771)in Match;rewrite Match;reflexivity|].
 lia.
Qed.
Theorem cycle_branch_redirect_observed memory inputs k observed v lane csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 (lane<6)%coq_nat ->branch_operand_match(cv_commit_instruction v)lane ->cv_late_bubble v=false ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 6507(top_environment observed)=Some(Gval(Fuint 1)[::cv_delayed_redirect v]).
Proof.
 intros Observe Legal Reset View Lane Match Late PC Pending Decision Csr CsrSize.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[instruction[Size Inst]].
 rewrite(cva_commit_instruction _ _ View)in Inst;inversion Inst;subst instruction.
 destruct(observed_checker_bubble_value memory inputs k observed false Observe Legal Reset
 ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity))as[_ Enabled].
 pose proof(delayed_reference_instruction_observed memory inputs k observed(cv_commit_instruction v)Observe Legal(cva_commit_instruction _ _ View)Enabled Size)as Instruction.
 destruct(reference_branch_operands_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View))as[Rs1 Rs2].
 pose proof(branch_operand_pc_match _ _ Lane Match)as PCMatch.
 pose proof(pc_relative_reference_immediate_observed(Nat.sub 5 lane)memory inputs k observed(cv_commit_instruction v)
 ltac:(lia)Observe Legal Reset(cva_commit_instruction _ _ View)PCMatch)as Immediate.
 assert(BankSize:forall second,size(cv_reference_bank v(to_nat(rf_instruction_address second(cv_commit_instruction v))))=32%nat).
 { intro second. assert(Bound:(to_nat(rf_instruction_address second(cv_commit_instruction v))<32)%coq_nat).
 { pose proof(to_nat_bounded(rf_instruction_address second(cv_commit_instruction v)))as H.
 rewrite(rf_instruction_address_size second _ Size)in H. exact(elimT ltP H). }
 exact(proj1(cva_reference_bank _ _ View _ Bound)). }
 pose proof(reference_redirect_function_observed memory inputs k observed(cv_commit_instruction v)
 (cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))))
 (cv_reference_bank v(to_nat(rf_instruction_address true(cv_commit_instruction v))))
 (pc_relative_immediate(Nat.sub 5 lane)(cv_commit_instruction v))(cv_reference_pc v)csr
 Observe Legal Instruction Rs1 Rs2 Immediate(cva_reference_pc _ _ View)Csr(BankSize false)(BankSize true)(cva_reference_pc_width _ _ View)CsrSize)as Value.
 pose proof(branch_operand_not_jalr _ _ Lane Match)as NotJalr.
 specialize(Decision Late). unfold cycle_reference_taken in Decision. rewrite NotJalr Bool.orb_false_r in Decision.
 rewrite dut_reference_alignment NotJalr Bool.andb_false_l Bool.orb_false_r in Value.
 rewrite <-Decision in Value.
 destruct(cv_delayed_redirect v)eqn:Taken;[|exact Value].
 pose proof(cycle_pc_relative_pending_target_aligned(Nat.sub 5 lane)memory inputs k observed v(N.testbit(to_N csr)2)
 Observe Legal Reset View PC Pending ltac:(lia)PCMatch Taken)as Align.
 rewrite Align in Value;exact Value.
Qed.
