Require Import CycleAddAllBankAdvance CycleCompareImmediateBankAdvance CycleBitwiseBankAdvance CycleShiftBankAdvance CycleUpperBankAdvance CycleCompareBankAdvance CycleSubtractAllBankAdvance CycleLinkBankAdvance CycleLoadAllBankAdvance CycleNonwriteBankAdvance CycleBanksAgreeStep RFModeInvariant RFAddPendingInvariant RFCompareImmediatePendingInvariant RFBitwisePendingInvariant RFShiftPendingInvariant RFUpperPendingInvariant RFComparePendingInvariant RFSubtractPendingInvariant MemoryPendingInvariant PCRelativePendingInvariant CycleRedirectDecision JALRPendingAlignment JALRTakenInvariant CycleView ReferenceInstructionDecode RFScalarControl FormalLocalHistory.
From Coq Require Import NArith Lia.
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
 destruct row as[|row].
 { exact(cycle_add_reference_advance_all memory inputs k current next before after 1%nat Transition Reset Before After Banks Mode Add ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_compare_immediate_reference_advance memory inputs k current next before after false Transition Reset Before After Banks Mode CompareI Match). }
 destruct row as[|row].
 { exact(cycle_compare_immediate_reference_advance memory inputs k current next before after true Transition Reset Before After Banks Mode CompareI Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 3%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 4%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 5%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after true 0%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after true 1%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after true 2%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_upper_reference_advance memory inputs k current next before after false Transition Reset Before After Banks Mode Upper Phase Match). }
 destruct row as[|row].
 { exact(cycle_upper_reference_advance memory inputs k current next before after true Transition Reset Before After Banks Mode Upper Phase Match). }
 destruct row as[|row].
 { exact(cycle_add_reference_advance_all memory inputs k current next before after 0%nat Transition Reset Before After Banks Mode Add ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_compare_reference_advance memory inputs k current next before after false Transition Reset Before After Banks Mode Compare Match). }
 destruct row as[|row].
 { exact(cycle_compare_reference_advance memory inputs k current next before after true Transition Reset Before After Banks Mode Compare Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 0%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 1%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_bitwise_reference_advance memory inputs k current next before after 2%nat Transition Reset Before After Banks Bitwise ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after false 0%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after false 1%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_subtract_reference_advance memory inputs k current next before after Transition Reset Before After Banks Mode Subtract Match). }
 destruct row as[|row].
 { exact(cycle_shift_reference_advance memory inputs k current next before after false 2%nat Transition Reset Before After Banks Mode Shift ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_link_reference_advance memory inputs k current next before after 0%nat csr Transition Reset Before After Banks Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR CSRSize). }
 destruct row as[|row].
 { exact(cycle_link_reference_advance memory inputs k current next before after 1%nat csr Transition Reset Before After Banks Mode Aligned Relative Redirect Jalr Taken ltac:(lia) Match CSR CSRSize). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 23%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 24%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 25%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 26%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 27%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 28%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_load_reference_advance memory inputs k current next before after 4%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_reference_advance memory inputs k current next before after 3%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_reference_advance memory inputs k current next before after 2%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_reference_advance memory inputs k current next before after 1%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_load_reference_advance memory inputs k current next before after 0%nat Transition Reset Before After Banks Mode Memory ltac:(lia) Match). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 34%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 35%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 destruct row as[|row].
 { exact(cycle_nonwrite_reference_advance memory inputs k current next before after 36%nat Transition Reset Before After Banks Mode ltac:(lia) Match ltac:(reflexivity)). }
 lia.
Qed.
Theorem cycle_isa_banks_agree memory inputs k current next before after row csr :
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
