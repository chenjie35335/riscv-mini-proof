Require Import ComparisonNodes ReferenceBankObservation LoadRequestAddressCycle LoadEffectiveAddress LoadTypeCorrespondence LoadImmediateSemantics
 StoreAddressReachableType StoreAddressInitialization ObservedRFPortsConcrete
 FormalInstructionResetBase FormalInstructionResetCycle FormalInstructionResetConstants JointBoundaryReachable
 ObservedInstructionNormalTransfer CoreSocModel FormalLocalHistory FormalObservationCommit
 JointBoundaryInduction ExternalReset StagedObservedRegister StagedCircuitRegisterHold FormalFetchType RegisterInvariants JointBoundaryRegisters ReferenceLoadSemantics RFReadPorts.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem load_request_address_run memory inputs k states instruction lane :
 generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment states)=Some(Gval(Fuint 32)instruction) ->
 (lane<5)%coq_nat ->load_type_is_load instruction lane ->
 VM.find 8004(top_environment states)=VM.find 7752(top_environment states).
Proof.
 destruct k as[|k];intros Run Legal Instruction Lane Load.
 - destruct(instruction_run_zero memory inputs states Run)as[env[Env[Front Nop]]].
   unfold top_environment in Instruction;rewrite Env Nop in Instruction;inversion Instruction;subst instruction.
   exfalso;exact(load_type_nop_not_load lane Lane Load).
 - assert(PriorLegal:generated_legal_trace memory inputs k).
   { apply(joint_legal_trace_prefix memory inputs(S k)k Legal);lia. }
   destruct(generated_successful_commit memory inputs k states Run)as[observed[Observe Commit]].
   destruct(legal_observation_reset memory inputs k PriorLegal)as[reset Reset].
   destruct reset.
   + pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
     destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
     destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
     destruct(joint_boundary_reachable memory inputs k previous Previous PriorLegal)as[Registers Storage].
     unfold top_environment in Registers;rewrite Old in Registers.
     destruct(Registers 7748%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[front[FrontSize Front]].
     destruct(Registers 7750%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[insn[Size Insn]].
     destruct(instruction_real_reset_cycle (generated_observation_input inputs k)previous old states(Gval(Fuint 32)front)(Gval(Fuint 32)insn)Old Front(Logic.eq_refl _)Insn(Logic.eq_refl _)Reset Cycle)as[env[Env[FrontNop Nop]]].
     unfold top_environment in Instruction;rewrite Env Nop in Instruction;inversion Instruction;subst instruction.
     exfalso;exact(load_type_nop_not_load lane Lane Load).
   + pose proof(observed_instruction_normal_equal memory inputs k observed states Observe PriorLegal Run Reset)as Transfer.
     rewrite Transfer in Instruction.
     destruct(proj1(observed_rf_ports_concrete memory inputs k observed Observe PriorLegal))as[left[Size Left]].
     rewrite(load_request_address_commit memory inputs k observed states instruction lane left Observe PriorLegal Run Reset Lane Instruction Load Size Left).
     rewrite(load_effective_address_commit memory inputs k observed states instruction lane left Observe PriorLegal Run Reset Lane Instruction Load Size Left).
     reflexivity.
Qed.
Theorem load_request_address_observed_equal memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<5)%coq_nat ->load_type_is_load instruction lane ->
 VM.find 8004(top_environment observed)=VM.find 7752(top_environment observed).
Proof.
 intros Observe Legal Instruction Lane Load.
 pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate].
 destruct(fetch9220_run_type memory inputs k committed Run)as[env[value[Env Rest]]].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 8004
 (Logic.eq_refl _)(Logic.eq_refl _)store_address_initial_safe store_address_register_present Run Env Observe)as CopyAddress.
 pose proof(joint_register_run_observed memory inputs k committed observed 7750 32 load_type_instruction_member Run Observe)as CopyInstruction.
 pose proof(joint_register_run_observed memory inputs k committed observed 7752 32 rf_read_alu_member Run Observe)as CopyAlu.
 rewrite CopyInstruction in Instruction.
 pose proof(load_request_address_run memory inputs k committed instruction lane Run Legal Instruction Lane Load)as Equal.
 unfold staged_register_lookup in CopyAddress. unfold top_environment in Equal,CopyAlu |- *.
 rewrite Env in Equal,CopyAlu. destruct(SVM.find nil observed)as[observed_env|]eqn:ObservedEnv.
 - rewrite CopyAddress Equal. exact(Logic.eq_sym CopyAlu).
 - unfold top_environment in Instruction. rewrite Env in Instruction.
   destruct(store_address_run_type memory inputs k committed Run)as[old[word[Old[Word Typed]]]].
   rewrite Env in Old;inversion Old;subst old. rewrite Word in CopyAddress;discriminate.
Qed.
