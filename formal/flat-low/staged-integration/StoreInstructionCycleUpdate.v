Require Import StoreAddressObserved StoreDataCycleUpdate StoreOffsetValue ReferenceLoadSemantics ReferenceStoreParts StoreTypeCorrespondence CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_instruction_address left instruction :=reference_load_address left(store_s_immediate instruction).
Definition store_instruction_offset left instruction :=
 store_offset_word (nth false(store_instruction_address left instruction)0%nat)
                   (nth false(store_instruction_address left instruction)1%nat).
Definition store_instruction_request left right instruction :=
 take 32(zeros(to_nat(store_instruction_offset left instruction))++right).
Lemma store_instruction_address_size left instruction :size(store_instruction_address left instruction)=32%nat.
Proof. unfold store_instruction_address,reference_load_address. rewrite size_take size_from_N. reflexivity. Qed.
Theorem store_instruction_cycle_update memory inputs k observed next instruction lane left right reset :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::reset]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7925(top_environment next)=Some(Gval(Fuint 32)
   (if reset then zeros 32 else store_instruction_request left right instruction)).
Proof.
 intros Observe Legal Next Reset Lane Instruction Store Left Right.
 pose proof(store_address_observed memory inputs k observed instruction lane left Observe Legal Lane Instruction Store Left)as Address.
 change(VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(store_instruction_address left instruction)))in Address.
 pose proof(store_instruction_address_size left instruction)as Size.
 unfold store_instruction_request,store_instruction_offset.
 destruct(store_instruction_address left instruction)as[|b0[|b1 tail]]eqn:Bits;try discriminate Size.
 exact(store_data_cycle_update memory inputs k observed next b0 b1 tail right reset Observe Legal Next Reset Address Right).
Qed.
