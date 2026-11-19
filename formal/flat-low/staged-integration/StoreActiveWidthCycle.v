Require Import StoreActiveCompareObserved StoreWidthCycleUpdate StoreTypeCorrespondence MemoryRequestWidth CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition store_width_word lane :=from_N 6(memory_request_width true(N.to_nat(store_type_lane_kind lane))).
Theorem store_active_width_cycle memory inputs k observed next instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 VM.find 8040(top_environment next)=Some(Gval(Fuint 6)(store_width_word lane)).
Proof.
 intros Observe Legal Run Reset Instruction Lane Store.
 exact(store_width_cycle_update memory inputs k observed next(store_width_word lane)false Observe Run Reset
 (store_active_width_observed memory inputs k observed instruction lane Observe Legal Reset Instruction Lane Store)(size_from_N _ _)).
Qed.
