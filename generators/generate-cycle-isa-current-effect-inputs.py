"""Dispatch current-cycle RF normalized effect agreement over the proved ISA rows."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
header='''Require Import CoreSocModel ComparisonNodes FormalLocalHistory CycleView CycleISAReferenceAdvance CycleInstructionClassReachable ReferenceInstructionDecode ReferenceBankCycleInputs ReferenceMISAConcrete RFAluWritebackObserved RFWriteEffect RFReferenceWriteEffect RFArchitecturalWriteEffect MemoryPendingInvariant RFEffectState
 RFAddEffectAgreement RFCompareImmediateEffectAgreement RFBitwiseEffectAgreement RFShiftEffectAgreement RFUpperEffectAgreement RFCompareEffectAgreement RFSubtractEffectAgreement RFLinkEffectAgreement RFLoadEffectAgreement RFNonwriteEffectAgreement.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.

(* Includes NOP and rd=x0 through the existing per-family zero-destination
   proofs; no bank equality or next-cycle view is needed here. *)
Theorem cycle_isa_current_effect_agreement memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_isa_pending v ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Pending.
 destruct(reference_misa_observed_concrete memory inputs k observed Observe Legal)as[csr[Width CSR]].
 destruct(cycle_commit_instruction_reference_row memory inputs k observed v Observe Legal Reset View)as[row[Row Match]].
 destruct Pending as[Mode Add CompareI Bitwise Shift Upper Compare Subtract Memory Phase Aligned Relative Redirect Jalr Taken].
'''
def call(name,args,pre):return f'{name} memory inputs k observed v {args} Observe Legal Reset View {pre}'
rows=[]
rows.append(call('cycle_add_effect_agreement','1%nat','Mode Add ltac:(lia) Match'))
for u in ['false','true']:rows.append(call('cycle_compare_immediate_effect_agreement',u,'Mode CompareI Match'))
for l in [3,4,5]:rows.append(call('cycle_bitwise_effect_agreement',f'{l}%nat','Bitwise ltac:(lia) Match'))
for l in [0,1,2]:rows.append(call('cycle_shift_effect_agreement',f'true {l}%nat','Mode Shift ltac:(lia) Match'))
for u in ['false','true']:rows.append(call('cycle_upper_effect_agreement',u,'Mode Phase Upper Match'))
rows.append(call('cycle_add_effect_agreement','0%nat','Mode Add ltac:(lia) Match'))
for u in ['false','true']:rows.append(call('cycle_compare_effect_agreement',u,'Mode Compare Match'))
for l in [0,1,2]:rows.append(call('cycle_bitwise_effect_agreement',f'{l}%nat','Bitwise ltac:(lia) Match'))
for l in [0,1]:rows.append(call('cycle_shift_effect_agreement',f'false {l}%nat','Mode Shift ltac:(lia) Match'))
rows.append(call('cycle_subtract_effect_agreement','','Mode Subtract Match'))
rows.append(call('cycle_shift_effect_agreement','false 2%nat','Mode Shift ltac:(lia) Match'))
for l in [0,1]:rows.append(call('cycle_link_effect_agreement',f'{l}%nat csr','Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR Width'))
for r in range(23,29):rows.append(call('cycle_nonwrite_effect_agreement',f'{r}%nat','ltac:(lia) Match (Logic.eq_refl false)'))
for l in [4,3,2,1,0]:rows.append(call('cycle_load_effect_agreement',f'{l}%nat','Memory Mode ltac:(lia) Match'))
for r in [34,35,36]:rows.append(call('cycle_nonwrite_effect_agreement',f'{r}%nat','ltac:(lia) Match (Logic.eq_refl false)'))
assert len(rows)==37
for row in rows:header+=' destruct row as[|row].\n { exact('+row+'). }\n'
header+=' lia.\nQed.\n'
(root/'formal/flat-low/staged-integration/CycleISACurrentEffectInputs.v').write_text(header)
