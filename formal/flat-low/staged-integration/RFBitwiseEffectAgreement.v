Require Import RFBitwisePendingInvariant RFALUReferenceData RFAluWritebackObserved RFArchitecturalWriteEffect RFEffectState RFPipelineEnable RFScalarControl RFALUData CycleView CycleRFExecute RFReadPorts RFWriteEffect ReferenceBankCycleInputs ReferenceInstructionDecode FormalRFDestination FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory LoadTypeCorrespondence CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem cycle_destination_observed memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->cv_destination v=rf_instruction_rd(cv_commit_instruction v).
Proof.
 intros Observe Legal View.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Instruction:VM.find 7750(history 9258%nat)=Some(Gval(Fuint 32)(cv_commit_instruction v))).
 { pose proof(joint_update_register_history_same _ history 9259 7750 32 load_type_instruction_member Steps)as Hold.
 rewrite(Hold 9258%nat ltac:(vm_compute;lia)). rewrite<-(Hold 9259%nat ltac:(vm_compute;lia)). rewrite Last. exact(cva_commit_instruction _ _ View). }
 pose proof(rf_destination_node _ (history 9258%nat)(history 9258%nat)(history 9259%nat)(cv_commit_instruction v)Instruction(Steps 9258%nat ltac:(vm_compute;lia)))as Value.
 rewrite Last(cva_destination _ _ View)in Value.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Value).
Qed.
Theorem cycle_bitwise_effect_agreement memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cycle_rf_bitwise_pending v ->(lane<6)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 rf_effect_normalize(cycle_pending_effect v)=rf_effect_normalize(ref_write_effect(top_environment observed)).
Proof.
 intros Observe Legal Reset View Pending Lane Match.
 rewrite(rf_bitwise_reference_effect_observed memory inputs k observed(cv_commit_instruction v)lane(cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Match(cva_reference_bank _ _ View)).
 unfold cycle_pending_effect.
 rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View).
 change(rf_effect_normalize(if cv_write_enabled v then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cv_write_data v)else RFNoWrite)=
 rf_effect_normalize(if true then RFWrite(to_nat(rf_instruction_rd(cv_commit_instruction v)))(cycle_bitwise_semantics lane(cv_reference_bank v)(cv_commit_instruction v))else RFNoWrite)).
 apply rf_scalar_effect_agreement.
 - pose proof(rf_pipeline_isa_write_enable_observed memory inputs k observed(cv_commit_instruction v)(cv_write_enabled v)(rf_bitwise_class lane)Observe Legal(cva_commit_instruction _ _ View)(cva_write_enabled _ _ View)ltac:(do 6(destruct lane as[|lane];[vm_compute;lia|]);lia)Match)as Enable.
   assert(Writes:rf_isa_writes(rf_bitwise_class lane)=true)by(do 6(destruct lane as[|lane];[reflexivity|]);lia).
   rewrite Writes rf_instruction_nonzero_correct in Enable. exact Enable.
 - intro Enabled. exact(cycle_rf_bitwise_writeback memory inputs k observed v lane Observe Legal View Pending Lane Match).
Qed.
