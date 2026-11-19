Require Import CycleISAReferenceAdvance CycleInstructionClassReachable ReferenceBankConcreteReachable RFAddAllBankInputs RFCompareImmediateAllBankInputs RFBitwiseBankInputs RFShiftBankInputs RFUpperBankInputs RFCompareAllBankInputs RFSubtractAllBankInputs RFLinkBankInputs RFLoadAllBankInputs RFNonwriteBankInputs CycleJALAlignment JALRTakenInvariant RFLinkEffectAgreement RFLinkReferenceEffect RFUpperSemantics RFScalarControl FormalInstructionResetConstants CycleView CoreSocModel FormalLocalHistory ReferenceInstructionDecode.
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
 { left. rewrite <-Nop. exact Instruction. }
 right. unfold reference_bank_step_inputs.
 pose proof(cva_reference_bank _ _ View)as Bank.
 destruct(cycle_commit_instruction_reference_row memory inputs k observed v Observe Legal Reset View)as[row[Row Match]].
 destruct Pending as[Mode Add CompareI Bitwise Shift Upper Compare Subtract Memory Phase Aligned Relative Redirect Jalr Taken].
 destruct row as[|row].
 { exact(rf_add_bank_inputs_nonnop memory inputs k observed (cv_commit_instruction v) 1%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match NonNop Bank). }
 destruct row as[|row].
 { exact(rf_compare_immediate_bank_inputs_all memory inputs k observed (cv_commit_instruction v) false (cv_reference_bank v) Observe Legal Reset Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_compare_immediate_bank_inputs_all memory inputs k observed (cv_commit_instruction v) true (cv_reference_bank v) Observe Legal Reset Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 3%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 4%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 5%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) true 0%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) true 1%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) true 2%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(rf_upper_bank_inputs memory inputs k observed (cv_commit_instruction v) false (cv_reference_pc v) Observe Legal Reset Instruction Match (cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View)). }
 destruct row as[|row].
 { exact(rf_upper_bank_inputs memory inputs k observed (cv_commit_instruction v) true (cv_reference_pc v) Observe Legal Reset Instruction Match (cva_reference_pc_width _ _ View)(cva_reference_pc _ _ View)). }
 destruct row as[|row].
 { exact(rf_add_bank_inputs_nonnop memory inputs k observed (cv_commit_instruction v) 0%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match NonNop Bank). }
 destruct row as[|row].
 { exact(rf_compare_bank_inputs_all memory inputs k observed (cv_commit_instruction v) false (cv_reference_bank v) Observe Legal Reset Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_compare_bank_inputs_all memory inputs k observed (cv_commit_instruction v) true (cv_reference_bank v) Observe Legal Reset Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 0%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 1%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_bitwise_bank_inputs memory inputs k observed (cv_commit_instruction v) 2%nat (cv_reference_bank v) Observe Legal Reset ltac:(lia) Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) false 0%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) false 1%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(rf_subtract_bank_inputs_all memory inputs k observed (cv_commit_instruction v) (cv_reference_bank v) Observe Legal Reset Instruction Match Bank). }
 destruct row as[|row].
 { exact(rf_shift_bank_inputs memory inputs k observed (cv_commit_instruction v) false 2%nat (cv_reference_bank v) Observe Legal Reset Instruction ltac:(lia) Match Bank). }
 destruct row as[|row].
 { exact(cycle_link_bank_inputs memory inputs k observed v 0%nat Observe Legal Reset View ltac:(lia) Match (cycle_jal_alignment_guard memory inputs k observed v csr Observe Legal Reset View Match (cycle_link_active memory inputs k observed v 0%nat Observe Legal View ltac:(lia)Match) Aligned Relative Redirect CSR Width)). }
 destruct row as[|row].
 { exact(cycle_link_bank_inputs memory inputs k observed v 1%nat Observe Legal Reset View ltac:(lia) Match (cycle_jalr_alignment_from_invariants memory inputs k observed v csr Observe Legal Reset View Jalr Taken Match CSR Width)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 23%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 24%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 25%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 26%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 27%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 28%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_load_bank_inputs_all memory inputs k observed v 4%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_bank_inputs_all memory inputs k observed v 3%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_bank_inputs_all memory inputs k observed v 2%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_bank_inputs_all memory inputs k observed v 1%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_bank_inputs_all memory inputs k observed v 0%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 34%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 35%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(rf_nonwrite_bank_inputs memory inputs k observed (cv_commit_instruction v) 36%nat Observe Legal Reset Instruction ltac:(lia) Match (Logic.eq_refl false)). }
 lia.
Qed.
