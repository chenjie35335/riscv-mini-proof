Require Import CoreSocModel ComparisonNodes FormalLocalHistory CycleView CycleISAReferenceAdvance CycleInstructionClassReachable ReferenceInstructionDecode ReferenceBankCycleInputs ReferenceMISAConcrete RFAluWritebackObserved RFWriteEffect RFReferenceWriteEffect RFArchitecturalWriteEffect MemoryPendingInvariant RFEffectState
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
 destruct row as[|row].
 { exact(cycle_add_effect_agreement memory inputs k observed v 1%nat Observe Legal Reset View Mode Add ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_compare_immediate_effect_agreement memory inputs k observed v false Observe Legal Reset View Mode CompareI Match). }
 destruct row as[|row].
 { exact(cycle_compare_immediate_effect_agreement memory inputs k observed v true Observe Legal Reset View Mode CompareI Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 3%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 4%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 5%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v true 0%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v true 1%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v true 2%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_upper_effect_agreement memory inputs k observed v false Observe Legal Reset View Mode Phase Upper Match). }
 destruct row as[|row].
 { exact(cycle_upper_effect_agreement memory inputs k observed v true Observe Legal Reset View Mode Phase Upper Match). }
 destruct row as[|row].
 { exact(cycle_add_effect_agreement memory inputs k observed v 0%nat Observe Legal Reset View Mode Add ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_compare_effect_agreement memory inputs k observed v false Observe Legal Reset View Mode Compare Match). }
 destruct row as[|row].
 { exact(cycle_compare_effect_agreement memory inputs k observed v true Observe Legal Reset View Mode Compare Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 0%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 1%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_effect_agreement memory inputs k observed v 2%nat Observe Legal Reset View Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v false 0%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v false 1%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_subtract_effect_agreement memory inputs k observed v  Observe Legal Reset View Mode Subtract Match). }
 destruct row as[|row].
 { exact(cycle_shift_effect_agreement memory inputs k observed v false 2%nat Observe Legal Reset View Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_link_effect_agreement memory inputs k observed v 0%nat csr Observe Legal Reset View Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR Width). }
 destruct row as[|row].
 { exact(cycle_link_effect_agreement memory inputs k observed v 1%nat csr Observe Legal Reset View Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR Width). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 23%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 24%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 25%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 26%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 27%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 28%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_load_effect_agreement memory inputs k observed v 4%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_effect_agreement memory inputs k observed v 3%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_effect_agreement memory inputs k observed v 2%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_effect_agreement memory inputs k observed v 1%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_effect_agreement memory inputs k observed v 0%nat Observe Legal Reset View Memory Mode ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 34%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 35%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_effect_agreement memory inputs k observed v 36%nat Observe Legal Reset View ltac:(lia) Match (Logic.eq_refl false)). }
 lia.
Qed.
