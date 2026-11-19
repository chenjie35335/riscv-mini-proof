Require Import CoreSocModel CycleView CycleMemoryAlignment MemoryPendingInvariant MemoryPendingConsequences MemoryRequestObservedSemantics ReferenceMemoryRequest ReferenceMemoryAlignment LoadTypeCorrespondence StoreTypeCorrespondence FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem memory_active_decode_class memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->(row<8)%coq_nat ->
 VM.find(reference_memory_guard row)(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 N.land(to_N instruction)28799=reference_memory_code row.
Proof.
 intros Observe Legal Reset Instruction Row Active.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 pose proof(memory_reference_decode_observed memory inputs k observed instruction enabled row Observe Legal Row Instruction Enabled)as Decode.
 rewrite Active in Decode.
 assert(Test:N.eqb(reference_memory_code row)(N.land(to_N(memory_reference_instruction instruction enabled))28799)=true)by(congruence).
 destruct enabled.
 - apply N.eqb_eq in Test;symmetry;exact Test.
 - do 8(destruct row as[|row];[discriminate Test|]);lia.
Qed.
Definition cycle_memory_event_pair index :N*N :=nth(0,0)[::(1941,2708);(1946,2723);(1886,2565);(1962,2649);(1966,2664)]index.
Theorem cycle_memory_event_alignment memory inputs k observed v index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->cycle_reset inputs k false ->
 cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->(index<5)%coq_nat ->
 VM.find(fst(cycle_memory_event_pair index))(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find(snd(cycle_memory_event_pair index))(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset View Pending Index Active.
 destruct index as[|index].
 - pose proof(memory_active_decode_class memory inputs k observed(cv_commit_instruction v)7 Observe Legal Reset(cva_commit_instruction _ _ View)ltac:(lia) Active)as Class.
   exact(cycle_store_alignment_from_pending memory inputs k observed v false Observe Legal Reset View Pending Class).
 destruct index as[|index].
 - pose proof(memory_active_decode_class memory inputs k observed(cv_commit_instruction v)6 Observe Legal Reset(cva_commit_instruction _ _ View)ltac:(lia) Active)as Class.
   exact(cycle_store_alignment_from_pending memory inputs k observed v true Observe Legal Reset View Pending Class).
 destruct index as[|index].
 - pose proof(memory_active_decode_class memory inputs k observed(cv_commit_instruction v)0 Observe Legal Reset(cva_commit_instruction _ _ View)ltac:(lia) Active)as Class.
   exact(cycle_load_alignment_from_pending memory inputs k observed v 0 Observe Legal Reset View Pending ltac:(lia) Class).
 destruct index as[|index].
 - pose proof(memory_active_decode_class memory inputs k observed(cv_commit_instruction v)2 Observe Legal Reset(cva_commit_instruction _ _ View)ltac:(lia) Active)as Class.
   exact(cycle_load_alignment_from_pending memory inputs k observed v 1 Observe Legal Reset View Pending ltac:(lia) Class).
 destruct index as[|index].
 - pose proof(memory_active_decode_class memory inputs k observed(cv_commit_instruction v)3 Observe Legal Reset(cva_commit_instruction _ _ View)ltac:(lia) Active)as Class.
   exact(cycle_load_alignment_from_pending memory inputs k observed v 2 Observe Legal Reset View Pending ltac:(lia) Class).
 lia.
Qed.
