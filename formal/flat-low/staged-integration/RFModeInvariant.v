Require Import CoreSocModel CycleView CycleInstructionNop RFWritebackModeCycle ControlWritebackKill FormalInstructionResetConstants LoadTypeCorrespondence ReferenceInstructionDecode RFScalarControl FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
(* NOP has rd=0 and is handled by normalized no-write effects. Its mode is
   irrelevant; all instructions with observable writes use this shared relation. *)
Definition cycle_writeback_mode v :Prop :=cv_commit_instruction v<>instruction_nop ->
 cv_write_select_low v=wbkill_low(wbkill_decode 49(cv_commit_instruction v)) /\
 cv_write_select_high v=wbkill_high(wbkill_decode 49(cv_commit_instruction v)).
Theorem cycle_writeback_mode_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_writeback_mode v.
Proof. intros Observe View NonNop. exfalso;apply NonNop;exact(cycle_initial_commit_nop memory inputs observed v Observe View). Qed.
Theorem cycle_writeback_mode_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->cycle_view_at(top_environment next)after ->cycle_writeback_mode after.
Proof. intros Transition Reset After NonNop. exfalso;apply NonNop;exact(cycle_reset_commit_nop memory inputs k current next after Transition Reset After). Qed.
Theorem cycle_writeback_mode_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->cycle_writeback_mode after.
Proof. intros Transition Reset Before After NonNop. exact(cycle_writeback_mode_commit memory inputs k current next before after Transition Reset Before After). Qed.
Lemma rf_load_decode_mode instruction lane :(lane<5)%coq_nat ->load_type_is_load instruction lane ->
 wbkill_low(wbkill_decode 49 instruction)=true /\wbkill_high(wbkill_decode 49 instruction)=false.
Proof.
 intros Lane Load.
 destruct lane as[|lane];[rewrite(rf_wb_legal_mode instruction 33 ltac:(lia) Load);vm_compute;split;reflexivity|].
 destruct lane as[|lane];[rewrite(rf_wb_legal_mode instruction 32 ltac:(lia) Load);vm_compute;split;reflexivity|].
 destruct lane as[|lane];[rewrite(rf_wb_legal_mode instruction 31 ltac:(lia) Load);vm_compute;split;reflexivity|].
 destruct lane as[|lane];[rewrite(rf_wb_legal_mode instruction 30 ltac:(lia) Load);vm_compute;split;reflexivity|].
 destruct lane as[|lane];[rewrite(rf_wb_legal_mode instruction 29 ltac:(lia) Load);vm_compute;split;reflexivity|].
 lia.
Qed.
Theorem cycle_load_writeback_mode v lane :cycle_writeback_mode v ->(lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 cv_write_select_low v=true /\cv_write_select_high v=false.
Proof.
 intros Mode Lane Load.
 assert(NonNop:cv_commit_instruction v<>instruction_nop).
 { intro Nop;rewrite Nop in Load;exact(load_type_nop_not_load lane Lane Load). }
 destruct(Mode NonNop)as[Low High]. rewrite Low High;exact(rf_load_decode_mode _ lane Lane Load).
Qed.
