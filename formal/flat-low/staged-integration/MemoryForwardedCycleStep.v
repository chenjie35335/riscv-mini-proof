Require Import CoreSocModel CycleView MemoryCycleStep RFAluWritebackObserved RFWriteEffect RFReadPorts ReferenceLoadSemantics FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_memory_address_from_current_banks writing memory inputs k current next before after lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->
 (lane<(if writing then 3 else 5))%coq_nat ->cycle_memory_instruction writing(cv_front_instruction before)lane ->
 cv_commit_instruction after=cv_front_instruction before /\
 cv_pending_alu after=reference_load_address
 (rf_apply_effect(cv_reference_bank before)(cycle_pending_effect before)
 (to_nat(rf_instruction_address false(cv_front_instruction before))))
 (cycle_memory_immediate writing(cv_front_instruction before)).
Proof.
 intros Transition Reset Before After Paired Lane Instruction.
 destruct(cycle_memory_address_step writing memory inputs k current next before after lane Transition Reset Before After Lane Instruction)as[Commit Address].
 split;[exact Commit|]. rewrite Address.
 destruct Transition as[Observe[Legal Rest]].
 rewrite(cycle_forwarded_read memory inputs k current before false Observe Legal Before Paired). reflexivity.
Qed.
