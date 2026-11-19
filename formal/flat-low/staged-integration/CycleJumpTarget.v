Require Import ReferencePCTargetObserved ReferencePCTargetSemantics ReferenceRedirectSemantics ReferenceLoadSemantics LoadImmediateSemantics RFScalarControl
 ReferenceUnusedReadObserved ReferenceJALRRead ReferenceJALRImmediate CycleJALAlignment JALRPendingAlignment JALRTakenInvariant
 CycleView CycleRedirectDecision PCRelativePendingInvariant PCRelativeAddressCycle ReferenceInstructionDecode
 ObservedCheckerBubbleValue ObservedJointRegisterConcrete LoadTypeCorrespondence DelayedDUTRedirectSemantics
 ReferenceIllegalObserved RFReadPorts CoreSocModel FormalLocalHistory PipelinePCSuccessor.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition jump_reference_target jalr pc rs1 immediate :=
 if jalr then [::false]++drop 1(take 32(reference_load_address rs1 immediate)) else reference_load_address pc immediate.
Lemma jump_reference_semantics instruction jalr rs1 rs2 immediate pc csr :
 N.land(to_N instruction)(reference_instruction_mask(if jalr then 22 else 21))=reference_instruction_code(if jalr then 22 else 21) ->
 reference_redirect_aligned(N.testbit(to_N csr)2)
 (if jalr then N.clearbit(to_N rs1+to_N immediate)0 else to_N pc+to_N immediate)=true ->
 reference_pc_target_function instruction rs1 rs2 immediate pc csr=jump_reference_target jalr pc rs1 immediate /\
 reference_redirect_function(to_N instruction)(to_N rs1)(to_N rs2)(to_N immediate)(to_N pc)(to_N csr)=true.
Proof.
 intros Match Align.
 assert(D21:N.eqb(N.land(to_N instruction)(reference_instruction_mask 21))(reference_instruction_code 21)=Nat.eqb 21(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)21 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D22:N.eqb(N.land(to_N instruction)(reference_instruction_mask 22))(reference_instruction_code 22)=Nat.eqb 22(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)22 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D23:N.eqb(N.land(to_N instruction)(reference_instruction_mask 23))(reference_instruction_code 23)=Nat.eqb 23(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)23 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D24:N.eqb(N.land(to_N instruction)(reference_instruction_mask 24))(reference_instruction_code 24)=Nat.eqb 24(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)24 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D25:N.eqb(N.land(to_N instruction)(reference_instruction_mask 25))(reference_instruction_code 25)=Nat.eqb 25(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)25 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D26:N.eqb(N.land(to_N instruction)(reference_instruction_mask 26))(reference_instruction_code 26)=Nat.eqb 26(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)26 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D27:N.eqb(N.land(to_N instruction)(reference_instruction_mask 27))(reference_instruction_code 27)=Nat.eqb 27(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)27 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 assert(D28:N.eqb(N.land(to_N instruction)(reference_instruction_mask 28))(reference_instruction_code 28)=Nat.eqb 28(if jalr then 22 else 21)).
 { rewrite N.eqb_sym. exact(rf_reference_decode_onehot instruction(if jalr then 22 else 21)28 ltac:(destruct jalr;vm_compute;lia)ltac:(vm_compute;lia)Match). }
 cbn[reference_instruction_mask reference_instruction_code reference_instruction_masks reference_instruction_codes nth]in D21,D22,D23,D24,D25,D26,D27,D28.
 destruct jalr;cbn in D21,D22,D23,D24,D25,D26,D27,D28,Align |- *;
 unfold reference_pc_target_function,reference_pc_target_value,reference_pc_target_guards,reference_redirect_function,jump_reference_target;
 rewrite D21 D22 D23 D24 D25 D26 D27 D28;cbn;rewrite Align;split;reflexivity.
Qed.
Definition cycle_jump_rs1 jalr v :=if jalr then cv_reference_bank v(to_nat(rf_instruction_address false(cv_commit_instruction v))) else cv_reference_bank v 0%nat.
Definition cycle_jump_immediate jalr v :=if jalr then load_i_immediate(cv_commit_instruction v) else pc_relative_immediate 6(cv_commit_instruction v).
Theorem cycle_jump_ports_observed memory inputs k observed v jalr csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cv_late_bubble v=false ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(if jalr then 22 else 21))=reference_instruction_code(if jalr then 22 else 21) ->
 cycle_pc_aligned v ->cycle_pc_relative_pending v ->cycle_redirect_decision v ->cycle_jalr_pending v ->cycle_jalr_taken v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cv_delayed_redirect v=true /\
 VM.find 6507(top_environment observed)=Some(Gval(Fuint 1)[::true]) /\
 VM.find 6508(top_environment observed)=Some(Gval(Fuint 32)(if jalr then [::false]++drop 1(cv_pending_alu v) else cv_pending_alu v)).
Proof.
 intros Observe Legal Reset View Late Match PC Pending Decision JPending JTaken Csr CsrSize.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[instruction[Size Inst]].
 rewrite(cva_commit_instruction _ _ View)in Inst;inversion Inst;subst instruction.
 destruct(observed_checker_bubble_value memory inputs k observed false Observe Legal Reset
 ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity))as[_ Valid].
 pose proof(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset
 ltac:(rewrite(cva_late_bubble _ _ View)Late;reflexivity))as Enabled.
 pose proof(delayed_reference_instruction_observed memory inputs k observed(cv_commit_instruction v)Observe Legal(cva_commit_instruction _ _ View)Valid Size)as Instruction.
 assert(Rs1:VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)(cycle_jump_rs1 jalr v))).
 { destruct jalr;unfold cycle_jump_rs1.
 - exact(reference_jalr_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)(cv_reference_bank v)Observe Legal Reset(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View)).
 - exact(unused_link_bank_observed false memory inputs k observed(cv_commit_instruction v)21(cv_reference_bank v)Observe Legal Enabled(cva_commit_instruction _ _ View)(Logic.eq_refl _)Match(cva_reference_bank _ _ View)). }
 assert(Rs2:VM.find 2804(top_environment observed)=Some(Gval(Fuint 32)(cv_reference_bank v 0%nat))).
 { exact(unused_link_bank_observed true memory inputs k observed(cv_commit_instruction v)(if jalr then 22 else 21)(cv_reference_bank v)Observe Legal Enabled(cva_commit_instruction _ _ View)ltac:(destruct jalr;auto)Match(cva_reference_bank _ _ View)). }
 assert(Immediate:VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(cycle_jump_immediate jalr v))).
 { destruct jalr;unfold cycle_jump_immediate.
 - exact(reference_jalr_immediate_observed memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Match).
 - exact(pc_relative_reference_immediate_observed 6 memory inputs k observed(cv_commit_instruction v)ltac:(lia)Observe Legal Reset(cva_commit_instruction _ _ View)Match). }
 assert(Rs1Size:size(cycle_jump_rs1 jalr v)=32%nat).
 { unfold cycle_jump_rs1;destruct jalr.
 - pose proof(to_nat_bounded(rf_instruction_address false(cv_commit_instruction v)))as Bound.
   rewrite(rf_instruction_address_size false _ Size)in Bound.
   exact(proj1(cva_reference_bank _ _ View _ (elimT ltP Bound))).
 - exact(proj1(cva_reference_bank _ _ View 0%nat ltac:(lia))). }
 pose proof(proj1(cva_reference_bank _ _ View 0%nat ltac:(lia)))as Rs2Size.
 assert(Taken:cv_delayed_redirect v=true).
 { destruct jalr;[exact(JTaken Match)|rewrite(Decision Late);exact(cycle_jal_reference_taken v Match)]. }
 assert(Align:reference_redirect_aligned(N.testbit(to_N csr)2)
 (if jalr then N.clearbit(to_N(cycle_jump_rs1 jalr v)+to_N(cycle_jump_immediate jalr v))0 else to_N(cv_reference_pc v)+to_N(cycle_jump_immediate jalr v))=true).
 { destruct jalr;unfold cycle_jump_rs1,cycle_jump_immediate.
 - exact(cycle_jalr_pending_aligned memory inputs k observed v(N.testbit(to_N csr)2)Observe Legal Reset View JPending Match Taken).
 - exact(cycle_pc_relative_pending_target_aligned 6 memory inputs k observed v(N.testbit(to_N csr)2)Observe Legal Reset View PC Pending ltac:(lia)Match Taken). }
 destruct(jump_reference_semantics(cv_commit_instruction v)jalr(cycle_jump_rs1 jalr v)(cv_reference_bank v 0%nat)(cycle_jump_immediate jalr v)(cv_reference_pc v)csr Match Align)as[Target Redirect].
 pose proof(reference_pc_target_function_observed memory inputs k observed(cv_commit_instruction v)(cycle_jump_rs1 jalr v)(cv_reference_bank v 0%nat)(cycle_jump_immediate jalr v)(cv_reference_pc v)csr Observe Legal Instruction Rs1 Rs2 Immediate(cva_reference_pc _ _ View)Csr Rs1Size Rs2Size(cva_reference_pc_width _ _ View)CsrSize)as Value.
 pose proof(reference_redirect_function_observed memory inputs k observed(cv_commit_instruction v)(cycle_jump_rs1 jalr v)(cv_reference_bank v 0%nat)(cycle_jump_immediate jalr v)(cv_reference_pc v)csr Observe Legal Instruction Rs1 Rs2 Immediate(cva_reference_pc _ _ View)Csr Rs1Size Rs2Size(cva_reference_pc_width _ _ View)CsrSize)as Flag.
 rewrite Redirect in Flag. rewrite Target in Value. split;[exact Taken|]. split;[exact Flag|].
 destruct jalr;unfold jump_reference_target,cycle_jump_rs1,cycle_jump_immediate in Value.
 - pose proof(JPending Match)as JP. unfold cycle_jalr_address in JP. rewrite <-JP in Value. rewrite take_oversize in Value;[exact Value|rewrite(cva_pending_width _ _ View);reflexivity].
 - change(VM.find 6508(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address(cv_reference_pc v)(pc_relative_immediate 6(cv_commit_instruction v)))))in Value.
   rewrite(Pending 6 ltac:(vm_compute;lia)Match). exact Value.
Qed.
Lemma cycle_jump_target_low word :size word=32%nat ->
 take 32(pipeline_redirect_target word)=[::false]++drop 1 word.
Proof.
 intro Size. rewrite(pipeline_redirect_target_bits word Size).
 destruct word as[|bit tail];[discriminate Size|]. cbn[drop]. rewrite drop0.
 change(false::take 31(tail++[::false])=false::tail).
 assert(Tail:size tail=31%nat)by(inversion Size;reflexivity).
 rewrite take_cat Tail ltnn subnn take0 cats0;reflexivity.
Qed.
Require Import CycleBranchPCAdvance PipelinePCRelation PipelinePCHoldReachable ReferencePCRedirectObserved PipelinePCAdjacentTransfer.
Theorem cycle_jump_pc_committed memory inputs k current committed before jalr csr :
 generated_observe memory inputs k=Some current ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cv_late_bubble before=false ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask(if jalr then 22 else 21))=reference_instruction_code(if jalr then 22 else 21) ->
 cycle_pc_aligned before ->cycle_pc_relative_pending before ->cycle_redirect_decision before ->cycle_jalr_pending before ->cycle_jalr_taken before ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 VM.find 6780(top_environment current)=Some(Gval(Fuint 1)[::false]) ->pipeline_pc_relation(top_environment committed).
Proof.
 intros Observe Legal Run Reset Before Late Match PC Pending Decision JPending JTaken Csr CsrSize Quiet.
 destruct(cycle_jump_ports_observed memory inputs k current before jalr csr Observe Legal Reset Before Late Match PC Pending Decision JPending JTaken Csr CsrSize)as[Taken[Redirect Target]].
 assert(LateNode:VM.find 7947(top_environment current)=Some(Gval(Fuint 1)[::false])).
 { rewrite(cva_late_bubble _ _ Before)Late;reflexivity. }
 apply(pipeline_pc_active_redirect_target memory inputs k current committed Observe Legal Run Reset LateNode).
 - rewrite(cva_delayed_redirect _ _ Before)Taken;reflexivity.
 - intros word Width Word. rewrite(cva_pending_alu _ _ Before)in Word;inversion Word;subst word.
   destruct(observed_checker_bubble_value memory inputs k current false Observe Legal Reset LateNode)as[Valid Enabled].
   pose proof(adjacent_transfer_observed_reset memory inputs k current Observe Legal Reset)as RootReset.
   assert(TargetWidth:size(take 32(pipeline_redirect_target(cv_pending_alu before)))=32%nat).
   { rewrite size_take(pipeline_redirect_target_size _ Width);reflexivity. }
   apply(reference_pc_redirect_observed memory inputs k current committed(cv_reference_pc before)(take 32(pipeline_redirect_target(cv_pending_alu before)))
     Observe Legal Run RootReset TargetWidth(cva_reference_pc _ _ Before)Enabled Redirect Quiet).
   destruct jalr.
   + rewrite(cycle_jump_target_low _ Width);exact Target.
   + assert(Low:N.testbit(to_N(cv_pending_alu before))0=false).
     { rewrite(Pending 6 ltac:(vm_compute;lia)Match).
       apply pc_relative_address_low_zero;[apply pc_relative_aligned_low_zero;exact(proj1 PC)|apply pc_relative_immediate_low_zero]. }
     rewrite(cycle_even_redirect_word _ Width Low);exact Target.
Qed.
