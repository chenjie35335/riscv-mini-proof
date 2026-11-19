Require Import CoreSocModel CycleView MemoryPendingInvariant MemoryCycleStep LoadResultCorrespondence ReferenceLoadRs1 ReferenceLoadImmediate ReferenceLoadSemantics LoadTypeCorrespondence LoadImmediateSemantics RFReadPorts ObservedJointRegisterConcrete JointBoundaryRegisters FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_load_result_correspondence memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 exists result,VM.find 7904(top_environment observed)=Some(Gval(Fsint 33)result) /\
 VM.find(reference_load_output lane)(top_environment observed)=Some(Gval(Fuint 32)(take 32 result)).
Proof.
 intros Observe Legal Reset View Pending Lane Load.
 pose proof(reference_load_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)lane
 (cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_load_immediate_observed memory inputs k observed(cv_commit_instruction v)lane
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load)as Immediate.
 destruct(observed_joint_register_concrete memory inputs k observed 9222%nat 32%nat Observe Legal
 ltac:(apply(List.nth_error_In joint_boundary_registers 69%nat);vm_compute;reflexivity))as[raw[RawSize Raw]].
 pose proof(Pending false lane Lane Load)as Address.
 cbn [cycle_memory_immediate]in Address.
 pose proof(cva_pending_width _ _ View)as Size.
 pose proof(cva_pending_alu _ _ View)as Value.
 destruct(cv_pending_alu v)as[|b0[|b1 rest]];cbn in Size;try lia.
 eapply(load_instruction_observed_correspondence memory inputs k observed lane(cv_commit_instruction v)b0 b1 rest raw _ _
 Observe Legal Lane RawSize(cva_commit_instruction _ _ View)Load Reset Size ltac:(rewrite <-Address;rewrite !take_cons take0;reflexivity) Value Rs1 Immediate Raw).
Qed.
