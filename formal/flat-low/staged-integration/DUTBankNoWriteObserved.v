Require Import DUTBankNoWriteHistory RFEffectState DUTBankCycleHistory DUTWritebackHistory DUTBankObservation CycleView RFAluWritebackObserved RFBitwiseEffectAgreement RFWriteEffect RFScalarControl RFReadPorts RFArchitecturalNormalRelation RFArchitecturalRelation ReferenceControlRegisters RFNonAluBubbleHazard RFPipelineEnable ObservedLegalNoTrap FormalFetchType JointBoundaryReachable JointBoundaryPreparation ConcreteRegisterInitialization FormalResetPreparation FormalLocalHistory JointUpdateBoundaryHistory JointBoundaryRegisters ObservedJointRegisterConcrete CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem dut_bank_observed_no_write_commit memory inputs k observed v result :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 cv_write_enabled v && (to_nat(cv_destination v)!=0%nat)=false ->
 formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(top_environment observed)true(top_environment observed)flat_statements=Some result ->
 rf_dut_bank_at result(cv_dut_bank v).
Proof.
 intros Observe Legal Reset View Disabled Commit.
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 destruct(fetch9220_run_type memory inputs k committed Run)as[env[value[Env Rest]]].
 destruct(joint_boundary_reachable memory inputs k committed Run Legal)as[Registers Storage].
 unfold top_environment in Registers;rewrite Env in Registers.
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. rewrite First. exact(joint_boundary_prepared_concrete committed env _ initial node width Member(Registers node width Member)Env Prepare). }
 destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[initial_env[InitialEnv InitialReset]].
 assert(Reset0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. unfold top_environment;rewrite InitialEnv;exact InitialReset. }
 pose proof(legal_local_reset_history _ history 9259 false Steps Reset0)as Resets.
 assert(Bank:rf_dut_bank_at(history 0%nat)(cv_dut_bank v)).
 { intros index Bound. destruct(cva_dut_bank _ _ View index Bound)as[Size Value]. split;[exact Size|].
   destruct(rf_architectural_register_properties _ (rf_dut_register_member index Bound))as[Present RestProps].
   rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)). rewrite Last;exact Value. }
 destruct(observed_joint_register_concrete memory inputs k observed 7750 32 Observe Legal rf_pipeline_enable_instruction_member)as[instruction[InstructionSize Instruction]].
 rewrite(cva_commit_instruction _ _ View)in Instruction. inversion Instruction;subst instruction.
 rewrite(cycle_destination_observed memory inputs k observed v Observe Legal View)in Disabled.
 rewrite<-rf_instruction_nonzero_correct in Disabled.
 eapply(dut_bank_no_write_history _ nil history result(cv_dut_bank v)(cv_commit_instruction v)(cv_write_enabled v));
 try exact Boundary;try exact Steps;try exact Resets;try exact NoTrap;try exact Bank;try exact InstructionSize;try exact Disabled.
 - rewrite Last;exact(cva_commit_instruction _ _ View).
 - rewrite Last;exact(cva_write_enabled _ _ View).
 - rewrite Last;exact Commit.
Qed.
Theorem cycle_dut_no_write_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_write_enabled before && (to_nat(cv_destination before)!=0%nat)=false ->
 forall index,(index<32)%coq_nat ->cv_dut_bank after index=cv_dut_bank before index.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Disabled.
 assert(Actual:rf_dut_bank_at(top_environment next)(cv_dut_bank before)).
 { apply(dut_bank_next_observed memory inputs k current committed next _ Observe Run NextObserve).
   intros result Commit. exact(dut_bank_observed_no_write_commit memory inputs k current before result Observe Legal Reset Before Disabled Commit). }
 intros index Bound. pose proof(proj2(Actual index Bound))as Value.
 rewrite(proj2(cva_dut_bank _ _ After index Bound))in Value. inversion Value;reflexivity.
Qed.
