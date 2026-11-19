Require Import StoreAddressObserved StoreAddressSelectObserved StoreAddressCycleUpdate StoreInstructionCycleUpdate StoreTypeCorrespondence ReferenceLoadSemantics ReferenceStoreParts CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_address_instruction_cycle memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 8004(top_environment next)=Some(Gval(Fuint 32)(store_instruction_address left instruction)).
Proof.
 intros Observe Legal Next Reset Lane Instruction Store Left.
 pose proof(store_address_observed memory inputs k observed instruction lane left Observe Legal Lane Instruction Store Left)as Address.
 pose proof(store_instruction_address_size left instruction)as Size.
 pose proof(store_address_select_observed memory inputs k observed (store_instruction_address left instruction) Observe Legal Reset Size Address)as Selected.
 exact(store_address_cycle_update memory inputs k observed next (store_instruction_address left instruction)false Observe Next Reset Selected Size).
Qed.
