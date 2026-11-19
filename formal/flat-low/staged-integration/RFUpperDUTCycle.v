Require Import RFUpperSemantics RFUpperDUTControl RFUpperDUTImmediate RFUpperDUTCopyCycle PCRelativeAddressCycle
 ReferenceInstructionDecode LoadImmediateSemantics ObservedJointRegisterConcrete RFReadPorts ReferenceBankObservation CycleView FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_upper_dut_observed_commit memory inputs k observed next instruction auipc pc left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 size pc=32%nat ->VM.find 7749(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(cycle_upper_semantics auipc pc instruction)).
Proof.
 intros Observe Legal Next Reset Instruction Match PcSize Pc Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]].
 rewrite Instruction in Word;inversion Word;subst word.
 destruct(rf_upper_dut_control_observed memory inputs k observed instruction auipc Observe Legal Instruction Size Match)as[A[B[Select Mode]]].
 pose proof(rf_upper_dut_imm_observed 0 memory inputs k observed instruction ltac:(lia)Observe Legal Instruction Size Select)as Immediate.
 pose proof(rf_upper_immediate_size instruction Size)as ImmSize.
 destruct auipc.
 - exact(pc_relative_address_commit_observed memory inputs k observed next pc(rf_upper_immediate instruction)left right
 Observe Legal Next Reset PcSize ImmSize A B Mode Pc Immediate Left Right).
 - exact(rf_upper_dut_copy_commit memory inputs k observed next(rf_upper_immediate instruction)right
 Observe Legal Next Reset ImmSize B Mode Immediate Right).
Qed.
Theorem cycle_upper_step memory inputs k current next before after auipc :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_upper_class auipc))=reference_instruction_code(rf_upper_class auipc) ->
 cv_pending_alu after=cycle_upper_semantics auipc(cv_front_pc before)(cv_front_instruction before).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Match.
 destruct(observed_joint_register_concrete memory inputs k current 7749%nat 32%nat Observe Legal
 ltac:(apply(List.nth_error_In JointBoundaryRegisters.joint_boundary_registers 54%nat);vm_compute;reflexivity))as[pc[PcSize Pc]].
 rewrite(cva_front_pc _ _ Before)in Pc;inversion Pc;subst pc.
 pose proof(rf_upper_dut_observed_commit memory inputs k current committed(cv_front_instruction before)auipc(cv_front_pc before)(cv_left before)(cv_right before)
 Observe Legal Run Reset(cva_front_instruction _ _ Before)Match PcSize(cva_front_pc _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 rf_read_alu_member Run NextObserve)as Copy.
 rewrite Value(cva_pending_alu _ _ After)in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
