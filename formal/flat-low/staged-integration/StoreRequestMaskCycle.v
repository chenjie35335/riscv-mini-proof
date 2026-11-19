Require Import StoreRequestMaskObserved StoreRequestMaskValues StoreMaskCycleUpdate StoreAddressObserved StoreInstructionCycleUpdate StoreTypeCorrespondence ReferenceStoreParts ReferenceLoadSemantics CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_instruction_mask lane left instruction :=
 store_request_mask4 lane (nth false(store_instruction_address left instruction)0%nat)
                          (nth false(store_instruction_address left instruction)1%nat).
Theorem store_instruction_mask_observed memory inputs k observed instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 80(top_environment observed)=Some(Gval(Fuint 4)(store_instruction_mask lane left instruction)).
Proof.
 intros Observe Legal Reset Lane Instruction Store Left.
 pose proof(store_address_observed memory inputs k observed instruction lane left Observe Legal Lane Instruction Store Left)as Address.
 change(VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(store_instruction_address left instruction)))in Address.
 pose proof(store_instruction_address_size left instruction)as Size.
 unfold store_instruction_mask.
 destruct(store_instruction_address left instruction)as[|b0[|b1 tail]]eqn:Bits;try discriminate Size.
 exact(store_request_mask_observed memory inputs k observed instruction lane b0 b1 tail Observe Legal Reset Lane Instruction Store Address).
Qed.
Lemma store_instruction_mask_size lane left instruction :(lane<3)%coq_nat ->size(store_instruction_mask lane left instruction)=4%nat.
Proof. intro Lane. apply store_request_mask4_size. exact Lane. Qed.
Theorem store_instruction_mask_cycle memory inputs k observed next instruction lane left :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7924(top_environment next)=Some(Gval(Fuint 4)(store_instruction_mask lane left instruction)).
Proof.
 intros Observe Legal Next Reset Lane Instruction Store Left.
 exact(store_mask_cycle_update memory inputs k observed next (store_instruction_mask lane left instruction)false Observe Next Reset
 (store_instruction_mask_observed memory inputs k observed instruction lane left Observe Legal Reset Lane Instruction Store Left)
 (store_instruction_mask_size lane left instruction Lane)).
Qed.
