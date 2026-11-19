from pathlib import Path
base=Path(__file__).resolve().parents[1]/'flat-low/staged-integration'
imports='CycleAddAllBankAdvance CycleCompareImmediateBankAdvance CycleBitwiseBankAdvance CycleShiftBankAdvance CycleUpperBankAdvance CycleCompareBankAdvance CycleSubtractAllBankAdvance CycleLinkBankAdvance CycleLoadAllBankAdvance CycleNonwriteBankAdvance CycleBanksAgreeStep RFModeInvariant RFAddPendingInvariant RFCompareImmediatePendingInvariant RFBitwisePendingInvariant RFShiftPendingInvariant RFUpperPendingInvariant RFComparePendingInvariant RFSubtractPendingInvariant MemoryPendingInvariant PCRelativePendingInvariant CycleRedirectDecision JALRPendingAlignment JALRTakenInvariant CycleView ReferenceInstructionDecode RFScalarControl FormalLocalHistory'
s='Require Import '+imports+'.\n'+'''From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Record cycle_isa_pending v : Prop := {
 cip_mode:cycle_writeback_mode v;
 cip_add:cycle_rf_add_pending v;
 cip_compare_immediate:cycle_rf_compare_immediate_pending v;
 cip_bitwise:cycle_rf_bitwise_pending v;
 cip_shift:cycle_rf_shift_pending v;
 cip_upper:cycle_rf_upper_pending v;
 cip_compare:cycle_rf_compare_pending v;
 cip_subtract:cycle_rf_subtract_pending v;
 cip_memory:cycle_memory_pending v;
 cip_phase:cycle_pc_phase v;
 cip_aligned:cycle_pc_aligned v;
 cip_relative:cycle_pc_relative_pending v;
 cip_redirect:cycle_redirect_decision v;
 cip_jalr:cycle_jalr_pending v;
 cip_jalr_taken:cycle_jalr_taken v
}.
Theorem cycle_isa_reference_advance memory inputs k current next before after row csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_isa_pending before ->
 (row<37)%coq_nat ->N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cycle_reference_effect_step before after.
Proof.
 intros Transition Reset Before After Banks Pending Row Match CSR CSRSize.
 destruct Pending as[Mode Add CompareI Bitwise Shift Upper Compare Subtract Memory Phase Aligned Relative Redirect Jalr Taken].
'''
for row in range(37):
 if row in [0,11]:call=f'cycle_add_reference_advance_all memory inputs k current next before after {1 if row==0 else 0}%nat Transition Reset Before After Banks Mode Add ltac:(lia) Match'
 elif row in [1,2]:call=f'cycle_compare_immediate_reference_advance memory inputs k current next before after {"true" if row==2 else "false"} Transition Reset Before After Banks Mode CompareI Match'
 elif row in [3,4,5,14,15,16]:call=f'cycle_bitwise_reference_advance memory inputs k current next before after {row if row<6 else row-14}%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match'
 elif row in [6,7,8,17,18,20]:
  lane={6:0,7:1,8:2,17:0,18:1,20:2}[row]
  call=f'cycle_shift_reference_advance memory inputs k current next before after {"true" if row<9 else "false"} {lane}%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match'
 elif row in [9,10]:call=f'cycle_upper_reference_advance memory inputs k current next before after {"true" if row==10 else "false"} Transition Reset Before After Banks Mode Upper Phase Match'
 elif row in [12,13]:call=f'cycle_compare_reference_advance memory inputs k current next before after {"true" if row==13 else "false"} Transition Reset Before After Banks Mode Compare Match'
 elif row==19:call='cycle_subtract_reference_advance memory inputs k current next before after Transition Reset Before After Banks Mode Subtract Match'
 elif row in [21,22]:call=f'cycle_link_reference_advance memory inputs k current next before after {row-21}%nat csr Transition Reset Before After Banks Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR CSRSize'
 elif row in range(29,34):call=f'cycle_load_reference_advance memory inputs k current next before after {33-row}%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match'
 else:call=f'cycle_nonwrite_reference_advance memory inputs k current next before after {row}%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)'
 s+=' destruct row as[|row].\n { exact('+call+'). }\n'
s+=' lia.\nQed.\n'
s+="""Theorem cycle_isa_banks_agree memory inputs k current next before after row csr :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_isa_pending before ->
 (row<37)%coq_nat ->N.land(to_N(cv_commit_instruction before))(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 7332(top_environment current)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 cycle_banks_agree after.
Proof.
 intros Transition Reset Before After Banks Pending Row Match CSR CSRSize.
 apply(cycle_banks_agree_isa_step memory inputs k current next before after row Transition Reset Before After Banks(cip_mode _ Pending)).
 - exact(cycle_isa_reference_advance memory inputs k current next before after row csr Transition Reset Before After Banks Pending Row Match CSR CSRSize).
 - exact Row.
 - exact Match.
Qed.
"""
(base/'CycleISAReferenceAdvance.v').write_text(s)
