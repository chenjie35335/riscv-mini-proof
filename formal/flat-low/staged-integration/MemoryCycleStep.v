Require Import CoreSocModel CycleView LoadEffectiveAddress StoreEffectiveAddress ReferenceBankObservation ReferenceLoadSemantics LoadImmediateSemantics ReferenceStoreParts LoadTypeCorrespondence StoreTypeCorrespondence RFReadPorts ObservedInstructionNormalTransfer FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_run generated_observe generated_modules generated_top.
Theorem cycle_front_to_commit memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_commit_instruction after=cv_front_instruction before.
Proof.
 intros [Observe[Legal[NextObserve[NextLegal[committed Run]]]]] Reset Before After.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7750 32 load_type_instruction_member Run NextObserve)as Copy.
 rewrite(observed_instruction_normal_equal memory inputs k current committed Observe Legal Run Reset)in Copy.
 rewrite(cva_commit_instruction _ _ After)(cva_front_instruction _ _ Before)in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Definition cycle_memory_instruction writing instruction lane :=
 if writing then store_type_is_store instruction lane else load_type_is_load instruction lane.
Definition cycle_memory_immediate writing instruction :=
 if writing then store_s_immediate instruction else load_i_immediate instruction.
Theorem cycle_memory_address_step writing memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<(if writing then 3 else 5))%coq_nat ->cycle_memory_instruction writing(cv_front_instruction before)lane ->
 cv_commit_instruction after=cv_front_instruction before /\
 cv_pending_alu after=reference_load_address(cv_left before)(cycle_memory_immediate writing(cv_front_instruction before)).
Proof.
 intros Transition Reset Before After Lane Instruction. split.
 - exact(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After).
 - destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 rf_read_alu_member Run NextObserve)as Copy.
 assert(Value:VM.find 7752(top_environment committed)=Some(Gval(Fuint 32)(reference_load_address(cv_left before)(cycle_memory_immediate writing(cv_front_instruction before))))).
 { destruct writing.
 - exact(store_effective_address_commit memory inputs k current committed (cv_front_instruction before)lane(cv_left before)Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Instruction(cva_left_width _ _ Before)(cva_left _ _ Before)).
 - exact(load_effective_address_commit memory inputs k current committed (cv_front_instruction before)lane(cv_left before)Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Instruction(cva_left_width _ _ Before)(cva_left _ _ Before)). }
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
