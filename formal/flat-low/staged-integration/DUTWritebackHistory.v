Require Import ReferencePCSequentialValues RFWritebackSelection RFAluWritebackObserved RFLoadWriteback RFPCWriteback JointUpdateBoundaryHistory JointBoundaryRegisters ConcreteRegisterInitialization CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem dut_writeback_history_stable invalid history limit low high :
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::low;high])) ->
 low && high=false ->
 exists data,forall t,(17<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 786(history t)=Some(Gval(Fuint 32)data).
Proof.
 intros Boundary Steps Modes NotCSR.
 assert(Held:forall node width,List.In(node,width)joint_boundary_registers ->
 exists word,size word=width /\forall t,(t<=limit)%coq_nat ->VM.find(N.of_nat node)(history t)=Some(Gval(Fuint width)word)).
 { intros node width Member. destruct(Boundary node width Member)as[word[Size Value]].
   exists word;split;[exact Size|]. intros t Bound.
   rewrite(joint_update_register_history_same invalid history limit node width Member Steps t Bound). exact Value. }
 assert(A:List.In(7752%nat,32%nat)joint_boundary_registers)by(apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity).
 assert(P:List.In(7751%nat,32%nat)joint_boundary_registers)by(apply(List.nth_error_In joint_boundary_registers 56%nat);vm_compute;reflexivity).
 assert(M:List.In(7755%nat,3%nat)joint_boundary_registers)by(apply(List.nth_error_In joint_boundary_registers 60%nat);vm_compute;reflexivity).
 assert(R:List.In(9222%nat,32%nat)joint_boundary_registers)by(apply(List.nth_error_In joint_boundary_registers 69%nat);vm_compute;reflexivity).
 destruct low,high;try discriminate NotCSR.
 - destruct(Held 7752 32 A)as[address[AddressSize Addresses]].
   destruct(Held 7755 3 M)as[mode[ModeSize LoadModes]].
   destruct(Held 9222 32 R)as[raw[RawSize Raws]].
   destruct mode as[|a[|b[|c rest]]];try discriminate ModeSize.
   destruct rest;[|discriminate ModeSize].
   destruct address as[|b0[|b1 rest]];try discriminate AddressSize.
   exists(take 32(rf_load_result a b c raw b0 b1)).
   exact(rf_load_writeback_register_history invalid history limit a b c b0 b1 rest raw RawSize Modes LoadModes Addresses Raws Steps).
 - destruct(Held 7751 32 P)as[pc[PCSize PCs]].
   exists(reference_pc_plus_four pc). intros t Lower Upper.
   exact(rf_pc_writeback_history invalid history limit pc Modes PCs Steps t ltac:(lia)Upper).
 - destruct(Held 7752 32 A)as[word[Size Words]]. exists word. intros t Lower Upper.
   exact(rf_alu_writeback_history invalid history limit word Size Modes Words Steps t ltac:(lia)Upper).
Qed.
