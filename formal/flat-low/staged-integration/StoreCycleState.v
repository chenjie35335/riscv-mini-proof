Require Import StoreAddressInstructionCycle StoreRequestMaskCycle StoreInstructionCycleUpdate StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Record store_state_at (env:VM.t hvalue) lane left right instruction : Prop := {
 store_state_address:VM.find 8004 env=Some(Gval(Fuint 32)(store_instruction_address left instruction));
 store_state_mask:VM.find 7924 env=Some(Gval(Fuint 4)(store_instruction_mask lane left instruction));
 store_state_data:VM.find 7925 env=Some(Gval(Fuint 32)(store_instruction_request left right instruction))
}.
Theorem store_cycle_state_update memory inputs k observed next instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 store_state_at(top_environment next)lane left right instruction.
Proof.
 intros Observe Legal Next Reset Lane Instruction Store Left Right. constructor.
 - exact(store_address_instruction_cycle memory inputs k observed next instruction lane left Observe Legal Next Reset Lane Instruction Store Left).
 - exact(store_instruction_mask_cycle memory inputs k observed next instruction lane left Observe Legal Next Reset Lane Instruction Store Left).
 - exact(store_instruction_cycle_update memory inputs k observed next instruction lane left right false Observe Legal Next Reset Lane Instruction Store Left Right).
Qed.
