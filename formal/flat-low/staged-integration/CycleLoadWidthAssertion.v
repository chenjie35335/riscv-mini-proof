Require Import CoreSocModel CycleView MemoryPendingInvariant MemoryPendingConsequences MemoryWidthAssertionWindow MemoryRequestObservedSemantics ReferenceLoadRs1 ReferenceLoadImmediate ReferenceRequestSpine LoadTypeCorrespondence RFReadPorts ReferenceLoadSemantics LoadImmediateSemantics FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Original assertion 2's local statement, for a load cycle under the pending
   invariant. Global reachability and non-load cycles are separate obligations. *)
Theorem cycle_load_width_assertion memory inputs k observed v lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->cycle_memory_pending v ->
 (lane<5)%coq_nat ->load_type_is_load(cv_commit_instruction v)lane ->
 generated_assert_m0_2_local(top_environment observed).
Proof.
 intros Observe Legal Reset View Pending Lane Load.
 pose proof(reference_load_rs1_bank_observed memory inputs k observed(cv_commit_instruction v)lane
 (cv_reference_bank v)Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load(cva_reference_bank _ _ View))as Rs1.
 pose proof(reference_load_immediate_observed memory inputs k observed(cv_commit_instruction v)lane
 Observe Legal Reset Lane(cva_commit_instruction _ _ View)Load)as Immediate.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 pose proof(memory_request_all_guards_observed memory inputs k observed(cv_commit_instruction v)enabled _ _
 Observe Legal(cva_commit_instruction _ _ View)Enabled Rs1 Immediate)as Guards.
 pose proof(load_type_instruction_observed memory inputs k observed(cv_commit_instruction v)lane
 Observe Legal Lane(cva_commit_instruction _ _ View)Load)as Mode.
 assert(Kind:exists kind,(kind<8)%coq_nat /\load_type_lane_kind lane=N.of_nat kind).
 { exists (N.to_nat(load_type_lane_kind lane)). split.
   - do 5 (destruct lane as[|lane];[vm_compute;lia|]);lia.
   - symmetry;apply N2Nat.id. }
 destruct Kind as[kind[Bound Kind]]. rewrite Kind in Mode.
 destruct(cycle_load_width_from_pending memory inputs k observed v lane Observe Legal Reset View Pending Lane Load)as[Equal Flags].
 exact(memory_read_width_assertion_window memory inputs k observed kind _ Observe Legal Bound Mode Guards Equal).
Qed.
