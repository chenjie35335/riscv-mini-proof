Require Import StoreCycleState StoreOutputObserved StoreMaskCorrespondence StoreInstructionCycleUpdate StoreRequestMaskCycle StoreRequestMaskValues StoreMaskValues StoreOffsetValue StoreOutputOffsetValues ReferenceStoreData CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_state_result memory inputs k observed instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->size right=32%nat ->
 store_aligned_lane lane (nth false(store_instruction_address left instruction)0%nat)
 (nth false(store_instruction_address left instruction)1%nat) ->
 store_state_at(top_environment observed)lane left right instruction ->
 VM.find 8039(top_environment observed)=Some(Gval(Fuint 32)(zext_to 32(take(reference_store_data_width lane)right))).
Proof.
 intros Observe Legal Lane Size Aligned [Address Mask Data].
 pose proof(store_instruction_address_size left instruction)as AddressSize.
 unfold store_instruction_mask in Mask.
 unfold store_instruction_request,store_instruction_offset in Data.
 destruct(store_instruction_address left instruction)as[|a0[|a1 tail]]eqn:Bits;try discriminate AddressSize.
 cbn[nth]in Mask,Data,Aligned.
 pose proof(store_request_mask4_size lane a0 a1 Lane)as MaskSize.
 destruct(store_request_mask4 lane a0 a1)as[|b0[|b1[|b2[|b3 rest]]]]eqn:MaskBits;try discriminate MaskSize.
 destruct rest;[|discriminate MaskSize].
 pose proof(store_output_observed memory inputs k observed a0 a1 tail b0 b1 b2 b3 _ Observe Legal Address Mask Data)as Output.
 rewrite store_input_output_offset_equal in Output.
 assert(Expanded:store_mask_word b0 b1 b2 b3=store_expanded_request_mask lane a0 a1).
 { unfold store_expanded_request_mask. rewrite MaskBits. reflexivity. }
 rewrite Expanded (store_instruction_masked_result lane a0 a1 right Lane Aligned Size)in Output.
 exact Output.
Qed.
Require Import StoreStateObserved StoreTypeCorrespondence ObservedRFPortsConcrete.
Theorem store_next_observed_result memory inputs k observed next next_observed instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 generated_observe memory inputs(S k)=Some next_observed ->generated_legal_trace memory inputs(S k) ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 store_aligned_lane lane (nth false(store_instruction_address left instruction)0%nat)
 (nth false(store_instruction_address left instruction)1%nat) ->
 VM.find 8039(top_environment next_observed)=Some(Gval(Fuint 32)(zext_to 32(take(reference_store_data_width lane)right))).
Proof.
 intros Observe Legal Next NextObserve NextLegal Reset Lane Instruction Store Left Right Aligned.
 pose proof(store_cycle_state_update memory inputs k observed next instruction lane left right Observe Legal Next Reset Lane Instruction Store Left Right)as State.
 pose proof(store_state_observed memory inputs(S k)next next_observed lane left right instruction Next NextObserve State)as ObservedState.
 destruct(proj1(proj2(observed_rf_ports_concrete memory inputs k observed Observe Legal)))as[word[Size Word]].
 rewrite Right in Word. inversion Word;subst word.
 exact(store_state_result memory inputs(S k)next_observed instruction lane left right NextObserve NextLegal Lane Size Aligned ObservedState).
Qed.
