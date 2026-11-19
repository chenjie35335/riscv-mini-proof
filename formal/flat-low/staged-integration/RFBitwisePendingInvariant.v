Require Import MemoryPendingInvariant RFWritebackModeCycle CycleRFExecute RFALUData RFReadPorts RFWriteEffect RFAluWritebackObserved CycleRFBitwise ReferenceInstructionDecode ObservedJointRegisterConcrete FormalObservationCommit ComparisonNodes PCRelativeAddressCycle CycleView MemoryCycleStep ReferenceLoadSemantics DUTRedirectReachability ReferenceRedirectSemantics FormalInstructionResetBase FormalInstructionResetCycle FormalInstructionResetConstants FormalLocalHistory ReferenceBankObservation JointBoundaryRegisters JointBoundaryReachable FormalFetchType CoreSocModel.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition cycle_rf_bitwise_pending v :Prop :=forall lane,(lane<6)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 cv_write_select_low v=false /\ cv_write_select_high v=false /\
 cv_pending_alu v=cycle_bitwise_semantics lane(cv_reference_bank v)(cv_commit_instruction v).
Lemma cycle_rf_bitwise_pending_nop v :cv_commit_instruction v=instruction_nop ->cycle_rf_bitwise_pending v.
Proof.
 intros Nop lane Lane Match. rewrite Nop in Match.
 do 6 (destruct lane as[|lane];[vm_compute in Match;discriminate|]);lia.
Qed.
Theorem cycle_rf_bitwise_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_rf_bitwise_pending v.
Proof.
 intros Observe View. pose proof Observe as Prepare.
 unfold generated_observe,generated_observe_cycle in Prepare.
 destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate].
 destruct(instruction_run_zero memory inputs committed Run)as[env[Env[Front Nop]]].
 pose proof(joint_register_run_observed memory inputs 0 committed observed 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run Observe)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ View)in Copy.
 apply cycle_rf_bitwise_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_rf_bitwise_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_rf_bitwise_pending after.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset After.
 pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 destruct(joint_boundary_reachable memory inputs k previous Previous Legal)as[Registers Storage].
 unfold top_environment in Registers;rewrite Old in Registers.
 destruct(Registers 7748%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[front[FrontSize Front]].
 destruct(Registers 7750%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[instruction[Size Instruction]].
 destruct(instruction_real_reset_cycle (generated_observation_input inputs k)previous old committed(Gval(Fuint 32)front)(Gval(Fuint 32)instruction)Old Front(Logic.eq_refl _)Instruction(Logic.eq_refl _)Reset Cycle)as[env[Env[FrontNop Nop]]].
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ After)in Copy.
 apply cycle_rf_bitwise_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Lemma cycle_bitwise_semantics_bank_ext lane instruction left right :
 size instruction=32%nat ->(forall index,(index<32)%coq_nat ->left index=right index) ->
 cycle_bitwise_semantics lane left instruction=cycle_bitwise_semantics lane right instruction.
Proof.
 intros Size Banks. unfold cycle_bitwise_semantics.
 assert(Bound:forall second,(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second instruction))as B.
 rewrite(rf_instruction_address_size second instruction Size)in B. exact(elimT ltP B). }
 rewrite(Banks _ (Bound false))(Banks _ (Bound true)). reflexivity.
Qed.
(* Reference bank advancement is a shared pending obligation, not a new assumption
   on the original assertions. The actual effect cycle proof will discharge it. *)
Theorem cycle_rf_bitwise_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->
 cycle_reference_effect_step before after ->
 cycle_rf_bitwise_pending after.
Proof.
 intros Transition Reset Before After Banks Advance lane Lane Match.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Instruction.
 assert(Class:cycle_bitwise_instruction before lane)by(split;[exact Lane|rewrite Instruction in Match;exact Match]).
 destruct(cycle_bitwise_mode_step memory inputs k current next before after lane Transition Reset Before After Class)as[Low High].
 split;[exact Low|]. split;[exact High|].
 pose proof(cycle_bitwise_pending_forwarded memory inputs k current next before after lane Transition Reset Before After Banks Class)as Data.
 rewrite Instruction. rewrite Data. symmetry. apply cycle_bitwise_semantics_bank_ext;[|exact Advance].
 destruct Transition as[Observe[Legal Rest]].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[word[Size Word]].
 rewrite(cva_front_instruction _ _ Before)in Word. inversion Word;subst word;exact Size.
Qed.
Theorem cycle_rf_bitwise_writeback memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->cycle_rf_bitwise_pending v ->
 (lane<6)%coq_nat ->
 N.land(to_N(cv_commit_instruction v))(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 cv_write_data v=cycle_bitwise_semantics lane(cv_reference_bank v)(cv_commit_instruction v).
Proof.
 intros Observe Legal View Pending Lane Match.
 destruct(Pending lane Lane Match)as[Low[High Data]].
 rewrite -(cycle_alu_writeback memory inputs k observed v Observe Legal View Low High). exact Data.
Qed.
