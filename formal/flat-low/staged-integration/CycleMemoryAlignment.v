Require Import CycleView MemoryPendingInvariant MemoryPendingConsequences MemoryCycleStep ReferenceMemoryAlignment ReferenceLoadRs1 ReferenceLoadImmediate MemoryLoadAddressWidth MemoryRequestObservedSemantics LoadTypeCorrespondence LoadImmediateSemantics ReferenceLoadSemantics RFReadPorts FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_alignment_load_lane index :=nth 0%nat [::0%nat;2%nat;3%nat] index.
Lemma cycle_alignment_load_lane_bound index :(index<3)%coq_nat ->(cycle_alignment_load_lane index<5)%coq_nat.
Proof. do 3(destruct index as[|index];[cbn [cycle_alignment_load_lane nth];lia|]);lia. Qed.
Theorem cycle_load_alignment_from_pending memory inputs k observed v index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (index<3)%coq_nat ->load_type_is_load(cv_commit_instruction v)(cycle_alignment_load_lane index) ->
 VM.find(reference_alignment_node index 14)(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Pending Index Load.
 pose proof(cycle_alignment_load_lane_bound index Index)as Lane.
 pose proof(reference_load_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)(cycle_alignment_load_lane index)
 (cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_load_immediate_observed memory inputs k observed(cv_commit_instruction v)(cycle_alignment_load_lane index)
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load)as Immediate.
 pose proof(reference_alignment_observed memory inputs k observed index _ _ Observe Legal ltac:(lia) Rs1 Immediate)as Align.
 pose proof(memory_load_actual_address_aligned memory inputs k observed(cv_commit_instruction v)(cycle_alignment_load_lane index)
 (cv_pending_alu v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load(cva_pending_width _ _ View)(cva_pending_alu _ _ View))as Safe.
 pose proof(Pending false _ Lane Load)as Address.
 cbn [cycle_memory_immediate]in Address. rewrite Address in Safe.
 do 3(destruct index as[|index];[cbn [memory_request_load_aligned reference_alignment_test cycle_alignment_load_lane nth Nat.eqb]in Safe,Align;rewrite Safe in Align;exact Align|]);lia.
Qed.
