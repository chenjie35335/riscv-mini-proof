Require Import CycleView CycleViewConstruction CycleViewObserved RFArchitecturalRelation RFReferenceNopHistory
 ObservedJointRegisterConcrete JointBoundaryRegisters ConcreteRegisterInitialization PipelinePCRelation CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma cycle_dut_register_joint index : (index<32)%coq_nat ->
 List.In((Nat.add 851 index),32%nat)joint_boundary_registers.
Proof.
 intro Bound. apply(List.nth_error_In joint_boundary_registers(Nat.add 21 index)).
 do 32(destruct index as[|index];[vm_compute;reflexivity|]);lia.
Qed.
Theorem cycle_architectural_concrete_from_reference memory inputs k observed bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_reference_bank_at(top_environment observed)bank ->
 rf_architectural_registers_concrete(top_environment observed).
Proof.
 intros Observe Legal Reference node Member.
 assert(Ids:rf_architectural_register_ids=List.flat_map(fun index=>[::Nat.add 851 index;Nat.add 7299 index])(List.seq 0 32))by reflexivity.
 rewrite Ids in Member. apply List.in_flat_map in Member.
 destruct Member as[index[Bound Member]]. apply List.in_seq in Bound.
 cbn in Member. destruct Member as[Equal|[Equal|Impossible]];try contradiction;subst node.
 - exact(observed_joint_register_concrete memory inputs k observed (Nat.add 851 index)32 Observe Legal(cycle_dut_register_joint index ltac:(lia))).
 - exists(bank index). exact(Reference index ltac:(lia)).
Qed.
Theorem cycle_view_from_reference_bank memory inputs k observed bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_reference_bank_at(top_environment observed)bank ->
 map_uint_concrete 7331 32(top_environment observed) ->
 cycle_view_at(top_environment observed)(cycle_snapshot(top_environment observed)).
Proof.
 intros Observe Legal Bank PC.
 apply(cycle_snapshot_from_reference_concrete memory inputs k observed Observe Legal).
 - exact(cycle_architectural_concrete_from_reference memory inputs k observed bank Observe Legal Bank).
 - exact PC.
Qed.
Theorem cycle_view_from_reference_invariants memory inputs k observed bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_reference_bank_at(top_environment observed)bank ->
 pipeline_pc_relation(top_environment observed) ->
 cycle_view_at(top_environment observed)(cycle_snapshot(top_environment observed)).
Proof.
 intros Observe Legal Bank[pc[Size[Aligned[PC Phase]]]].
 apply(cycle_view_from_reference_bank memory inputs k observed bank Observe Legal Bank).
 exists pc. split;assumption.
Qed.
