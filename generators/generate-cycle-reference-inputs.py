from pathlib import Path
root=Path(__file__).resolve().parents[2]
imports='CycleISAReferenceAdvance CycleInstructionClassReachable ReferenceBankConcreteReachable RFAddAllBankInputs RFCompareImmediateAllBankInputs RFBitwiseBankInputs RFShiftBankInputs RFUpperBankInputs RFCompareAllBankInputs RFSubtractAllBankInputs RFLinkBankInputs RFLoadAllBankInputs RFNonwriteBankInputs CycleJALAlignment JALRTakenInvariant RFLinkEffectAgreement RFLinkReferenceEffect RFUpperSemantics RFScalarControl FormalInstructionResetConstants CycleView CoreSocModel FormalLocalHistory ReferenceInstructionDecode'
s=f'''Require Import {imports}.
From Coq Require Import NArith List Bool Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_reference_bank_inputs memory inputs k observed v csr :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_isa_pending v ->
 VM.find 7332(top_environment observed)=Some(Gval(Fuint 32)csr) ->size csr=32%nat ->
 reference_bank_normal_inputs(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending CSR Width.
 pose proof(cva_commit_instruction _ _ View)as Instruction.
 destruct(List.list_eq_dec Bool.bool_dec(cv_commit_instruction v)instruction_nop)as[Nop|NonNop].
 {{ left. rewrite <-Nop. exact Instruction. }}
 right. unfold reference_bank_step_inputs.
 pose proof(cva_reference_bank _ _ View)as Bank.
 destruct(cycle_commit_instruction_reference_row memory inputs k observed v Observe Legal Reset View)as[row[Row Match]].
 destruct Pending as[Mode Add CompareI Bitwise Shift Upper Compare Subtract Memory Phase Aligned Relative Redirect Jalr Taken].
'''
prefix='memory inputs k observed'
i='(cv_commit_instruction v)';bank='(cv_reference_bank v)'
for row in range(37):
 s+=' destruct row as[|row].\n { '
 if row in [0,11]:
  lane=1 if row==0 else 0
  call=f'rf_add_bank_inputs_nonnop {prefix} {i} {lane}%nat {bank} Observe Legal Reset ltac:(lia) Instruction Match NonNop Bank'
 elif row in [1,2,12,13]:
  name='rf_compare_immediate_bank_inputs_all' if row<3 else 'rf_compare_bank_inputs_all'
  unsigned='true' if row in [2,13] else 'false'
  call=f'{name} {prefix} {i} {unsigned} {bank} Observe Legal Reset Instruction Match Bank'
 elif row in [3,4,5,14,15,16]:
  lane=row if row<6 else row-14
  call=f'rf_bitwise_bank_inputs {prefix} {i} {lane}%nat {bank} Observe Legal Reset ltac:(lia) Instruction Match Bank'
 elif row in [6,7,8,17,18,20]:
  lane={6:0,7:1,8:2,17:0,18:1,20:2}[row];imm='true' if row<9 else 'false'
  call=f'rf_shift_bank_inputs {prefix} {i} {imm} {lane}%nat {bank} Observe Legal Reset Instruction ltac:(lia) Match Bank'
 elif row in [9,10]:
  call=f'rf_upper_bank_inputs {prefix} {i} '+('true' if row==10 else 'false')+' (cv_reference_pc v) Observe Legal Reset Instruction Match (cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View)'
 elif row==19:
  call=f'rf_subtract_bank_inputs_all {prefix} {i} {bank} Observe Legal Reset Instruction Match Bank'
 elif row in [21,22]:
  lane=row-21
  if lane==0:
   align=f'cycle_jal_alignment_guard {prefix} v csr Observe Legal Reset View Match (cycle_link_active {prefix} v 0%nat Observe Legal View ltac:(lia)Match) Aligned Relative Redirect CSR Width'
  else:
   align=f'cycle_jalr_alignment_from_invariants {prefix} v csr Observe Legal Reset View Jalr Taken Match CSR Width'
  call=f'cycle_link_bank_inputs {prefix} v {lane}%nat Observe Legal Reset View ltac:(lia) Match ({align})'
 elif row in range(29,34):
  call=f'cycle_load_bank_inputs_all {prefix} v {33-row}%nat Observe Legal Reset View Memory Mode ltac:(lia) Match'
 else:
  call=f'rf_nonwrite_bank_inputs {prefix} {i} {row}%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)'
 s+=f'exact({call}). }}\n'
s+=' lia.\nQed.\n'
(root/'formal/flat-low/staged-integration/CycleReferenceBankInputs.v').write_text(s)
