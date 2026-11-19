Require Import RFUpperSemantics.
Require Import CoreSocModel ComparisonNodes CycleView MemoryCycleStep ReferenceConditionalBranchImmediate ReferenceBranchImmediate DUTImmediateModes RFALUData RFPipelineEnable ReferenceInstructionDecode LoadExecuteControl DUTRedirectDecode ALUOperandTransfer ALUInputStability ALUOutputTransfer LoadEffectiveAddress ReferenceLoadSemantics FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters RFReadPorts ReferenceBankObservation.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_upper_dut_control auipc which :N :=
 match which with 2%nat=>3|3%nat=>if auipc then 0 else 11|_=>0 end.
Lemma rf_upper_dut_decode_control instruction auipc which :(which<4)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(rf_upper_dut_control auipc which).
Proof.
 intros Which Match. pose proof(rf_upper_class_bound auipc)as Row.
 cbn[load_execute_decode].
 repeat match goal with |-context[dut_decode_test(to_N instruction)?stage]=>rewrite(rf_dut_decode_wb_choice instruction stage ltac:(vm_compute;lia))(rf_wb_choice_onehot instruction(rf_upper_class auipc)(Nat.sub 48 stage)Row ltac:(vm_compute;lia)Match)end.
 destruct auipc;do 4(destruct which as[|which];[reflexivity|]);lia.
Qed.
Theorem rf_upper_dut_control_observed memory inputs k observed instruction auipc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->size instruction=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 88(top_environment observed)=Some(Gval(Fuint 3)(from_N 3 3)) /\
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)(from_N 4(if auipc then 0 else 11))).
Proof.
 intros Observe Legal Front Size Match.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Control:forall which,(which<4)%coq_nat ->VM.find(load_execute_wire_target which true)(top_environment observed)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(rf_upper_dut_control auipc which)))).
 { intros which Which. rewrite <-Last.
 rewrite(load_execute_decode_history (generated_observation_input inputs k)nil history 9259 instruction which Which Steps ltac:(rewrite Last;exact Front)Size 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))(rf_upper_dut_decode_control instruction auipc which Which Match);reflexivity. }
 split;[exact(Control 0%nat ltac:(lia))|]. split;[exact(Control 1%nat ltac:(lia))|].
 split;[exact(Control 2%nat ltac:(lia))|exact(Control 3%nat ltac:(lia))].
Qed.
