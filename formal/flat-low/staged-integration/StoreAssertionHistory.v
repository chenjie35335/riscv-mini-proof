Require Import StoreCheckerDataObserved StoreCheckerDataHistory ReferenceStoreDataHistoryStable ReferenceStoreRequestData FormalAssertionDischarge ComparisonTruth CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_assertion5_history inputs path history reset guards source a0 a1 tail b0 b1 b2 b3 word :
 size word=32%nat ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 8004(history 9259%nat)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(history 9259%nat)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(history 9259%nat)=Some(Gval(Fuint 32)word) ->
 VM.find 2804(history 9259%nat)=Some(Gval(Fuint 32)source) ->
 (forall node,List.In node reference_store_request_data_guards ->VM.find node(history 9259%nat)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 1481(history 9259%nat)=VM.find 1526(history 9259%nat) ->
 generated_assert_m0_5_local(history 9259%nat).
Proof.
 intros Size Resets Steps Address Mask Data Source Guards Agree.
 pose proof(store_checker_data_history_from_last _ history 9259 a0 a1 tail b0 b1 b2 b3 word Size Steps Address Mask Data 9258%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))as DUT.
 pose proof(store_checker_data_history_stable _ history 9259 a0 a1 tail b0 b1 b2 b3 word Size Steps Address Mask Data 9258%nat 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))as DS.
 pose proof(reference_store_data_stable_from_last inputs path history 9259 reset guards source ltac:(vm_compute;lia) Resets Steps Source Guards 9258%nat 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))as RS.
 apply(assertion_5_from_enabled_agreement _ (history 9258%nat)(history 9258%nat)(history 9259%nat)(Steps 9258%nat ltac:(vm_compute;lia))).
 intro Enabled. exists 32%nat,32%nat,(store_checker_data_word a0 a1 b0 b1 b2 b3 word),(store_checker_data_word a0 a1 b0 b1 b2 b3 word).
 split;[exact DUT|]. split;[rewrite RS -Agree -DS;exact DUT|reflexivity].
Qed.
