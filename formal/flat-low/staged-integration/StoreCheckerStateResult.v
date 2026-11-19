Require Import StoreCheckerDataObserved StoreCheckerDataHistory StoreRequestDataValue.
Require Import StoreCycleState StoreOutputObserved StoreMaskCorrespondence StoreInstructionCycleUpdate StoreRequestMaskCycle StoreRequestMaskValues StoreMaskValues StoreOffsetValue StoreOutputOffsetValues ReferenceStoreData CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_checker_state_result memory inputs k observed instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->size right=32%nat ->
 store_aligned_lane lane (nth false(store_instruction_address left instruction)0%nat)
 (nth false(store_instruction_address left instruction)1%nat) ->
 store_state_at(top_environment observed)lane left right instruction ->
 VM.find 1481(top_environment observed)=Some(Gval(Fuint 32)(zext_to 32(take(reference_store_data_width lane)right))).
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
 assert(RequestSize:size(take 32(zeros(to_nat(store_offset_word a0 a1))++right))=32%nat).
 { rewrite -(store_request_word8_low right (store_offset_word a0 a1) Size).
   apply store_request_word8_size;[exact Size|reflexivity]. }
 pose proof(store_checker_data_observed memory inputs k observed a0 a1 tail b0 b1 b2 b3 _ Observe Legal RequestSize Address Mask Data)as Output.
 unfold store_checker_data_word in Output.
 rewrite store_input_output_offset_equal in Output.
 assert(Expanded:store_mask_word b0 b1 b2 b3=store_expanded_request_mask lane a0 a1).
 { unfold store_expanded_request_mask. rewrite MaskBits. reflexivity. }
 rewrite Expanded (store_instruction_masked_result lane a0 a1 right Lane Aligned Size)in Output.
 exact Output.
Qed.
