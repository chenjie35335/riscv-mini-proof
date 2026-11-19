Require Import DUTBankCycleObserved DUTBankNoWriteObserved CycleView RFAluWritebackObserved RFBitwiseEffectAgreement RFEffectState RFModeInvariant RFWritebackModeCycle RFPipelineEnable RFScalarControl RFWriteEffect ReferenceInstructionDecode FormalInstructionResetConstants ControlWritebackKill FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma dut_bank_no_write_effect bank destination data enabled :bank 0%nat=nseq 32 false ->enabled && (destination!=0%nat)=false ->
 forall index,rf_apply_effect bank(if enabled then RFWrite destination data else RFNoWrite)index=bank index.
Proof.
 intros Zero Disabled index. unfold rf_apply_effect. case I:(index==0%nat);[move/eqP:I=>I;subst index;exact(Logic.eq_sym Zero)|].
 destruct enabled;[|reflexivity]. cbn[andb]in Disabled.
 assert(D:destination=0%nat)by(move/negbFE:Disabled=>/eqP;auto).
 subst destination. rewrite I;reflexivity.
Qed.
Theorem cycle_dut_bank_guarded_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (cv_write_enabled before && (to_nat(cv_destination before)!=0%nat)=true ->cv_write_select_low before && cv_write_select_high before=false) ->
 forall index,(index<32)%coq_nat ->cv_dut_bank after index=rf_apply_effect(cv_dut_bank before)(cycle_pending_effect before)index.
Proof.
 intros Transition Reset Before After Mode.
 case Enabled:(cv_write_enabled before && (to_nat(cv_destination before)!=0%nat)).
 - exact(cycle_dut_bank_effect_step memory inputs k current next before after Transition Reset Before After(Mode Enabled)).
 - intros index Bound. rewrite(cycle_dut_no_write_step memory inputs k current next before after Transition Reset Before After Enabled index Bound).
   unfold cycle_pending_effect. symmetry;apply dut_bank_no_write_effect;[|exact Enabled].
   destruct Transition as[Observe[Legal Rest]]. exact(cycle_dut_x0 memory inputs k current before Observe Legal Before).
Qed.
Lemma dut_isa_mode_checked :List.forallb(fun row=>negb(wbkill_low(wbkill_row_value(rf_wb_row(rf_wb_class_index row))) && wbkill_high(wbkill_row_value(rf_wb_row(rf_wb_class_index row)))))(List.seq 0 37)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma dut_isa_mode_not_csr instruction row :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 wbkill_low(wbkill_decode 49 instruction) && wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intros Row Match. rewrite(rf_wb_legal_mode instruction row Row Match).
 pose proof dut_isa_mode_checked as Check.
 apply List.forallb_forall with(x:=row)in Check;[|apply List.in_seq;lia].
 exact(negbTE Check).
Qed.
Theorem cycle_dut_bank_isa_step memory inputs k current next before after row :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_writeback_mode before ->(row<37)%coq_nat ->
 N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 forall index,(index<32)%coq_nat ->cv_dut_bank after index=rf_apply_effect(cv_dut_bank before)(cycle_pending_effect before)index.
Proof.
 intros Transition Reset Before After Mode Row Match.
 apply(cycle_dut_bank_guarded_step memory inputs k current next before after Transition Reset Before After).
 intro Enabled. assert(NonNop:cv_commit_instruction before<>instruction_nop).
 { intro Nop. destruct Transition as[Observe[Legal Rest]].
   rewrite(cycle_destination_observed memory inputs k current before Observe Legal Before)Nop in Enabled.
   change(cv_write_enabled before && false=true)in Enabled. rewrite andbF in Enabled. discriminate Enabled. }
 destruct(Mode NonNop)as[Low High]. rewrite Low High.
 exact(dut_isa_mode_not_csr _ row Row Match).
Qed.
