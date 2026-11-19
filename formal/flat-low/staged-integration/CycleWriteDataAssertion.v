Require Import CycleStoreDataAssertion NonStoreDataAssertion Assertion5Reset StorePendingInvariant MemoryPendingInvariant
 StoreTypeCorrespondence CycleView ExternalReset CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma store_instruction_cases instruction :
 (exists lane,(lane<3)%coq_nat /\store_type_is_store instruction lane) \/
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane).
Proof.
 destruct(N.eq_dec (N.land(to_N instruction)28799)(store_type_lane_code 0))as[S0|N0].
 - left. exists 0%nat. split;[lia|exact S0].
 - destruct(N.eq_dec (N.land(to_N instruction)28799)(store_type_lane_code 1))as[S1|N1].
   + left. exists 1%nat. split;[lia|exact S1].
   + destruct(N.eq_dec (N.land(to_N instruction)28799)(store_type_lane_code 2))as[S2|N2].
     * left. exists 2%nat. split;[lia|exact S2].
     * right. intros[|[|[|lane]]] Bound;[exact N0|exact N1|exact N2|lia].
Qed.
Theorem cycle_write_data_assertion memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->
 cycle_memory_pending v ->cycle_store_pending(top_environment observed)v ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal View Memory Pending.
 destruct(legal_observation_reset memory inputs k Legal)as[reset Reset].
 destruct reset.
 - exact(assertion5_reset_observed memory inputs k observed Observe Reset).
 - destruct(store_instruction_cases(cv_commit_instruction v))as[[lane[Lane Store]]|NonStore].
   + exact(cycle_store_data_assertion memory inputs k observed v lane Observe Legal Reset View Memory Pending Lane Store).
   + exact(nonstore_data_assertion_observed memory inputs k observed(cv_commit_instruction v)
      Observe Legal Reset(cva_commit_instruction _ _ View)NonStore).
Qed.
