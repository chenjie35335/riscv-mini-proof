Require Import StoreOutputValues StoreMaskValues StoreMaskObserved StoreOutputOffsetValues StoreOutputOffsetHistory StoreOutputOffsetObserved StoreDataRegister CoreSocModel ComparisonNodes FormalObservedHistory FormalLocalHistory RegisterInvariants StagedRegisterHold.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_output_observed memory inputs k observed a0 a1 tail b0 b1 b2 b3 word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 8004(top_environment observed)=Some(Gval(Fuint 32)(a0::a1::tail)) ->
 VM.find 7924(top_environment observed)=Some(Gval(Fuint 4)[::b0;b1;b2;b3]) ->
 VM.find 7925(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 8039(top_environment observed)=Some(Gval(Fuint 32)
 (zext_to 32(drop(to_nat(store_output_offset_word a0 a1))(andB word(store_mask_word b0 b1 b2 b3))))).
Proof.
 intros Observe Legal Address Mask Word.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Held:forall node,has_register node flat_statements=true ->forall t,(t<=9259)%coq_nat ->
 VM.find node(history t)=VM.find node(top_environment observed)).
 { intros node Register.
   assert(H:forall t,(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(history 0%nat)).
   { intros t. induction t as[|t IH];intro Bound;[reflexivity|].
     rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements node Register(Steps t ltac:(lia))). apply IH;lia. }
   intros t Bound. rewrite(H t Bound) -(H 9259%nat ltac:(lia)) Last. reflexivity. }
 assert(MaskValue:VM.find 8018(history 9257%nat)=Some(Gval(Fuint 32)(store_mask_word b0 b1 b2 b3))).
 { eapply(store_mask_four_steps _ (history 9253%nat)(history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)b0 b1 b2 b3).
   - rewrite(Held 7924 store_mask_register 9253%nat ltac:(vm_compute;lia)). exact Mask.
   - apply Steps;vm_compute;lia.
   - apply Steps;vm_compute;lia.
   - apply Steps;vm_compute;lia.
   - apply Steps;vm_compute;lia. }
 assert(Offset:VM.find 8037(history 9258%nat)=Some(Gval(Fuint 5)(store_output_offset_word a0 a1))).
 { apply(store_output_offset_history _ history 9259 0 a0 a1 tail Steps).
   - intros t Lower Upper. rewrite(Held 8004 store_output_address_register t Upper). exact Address.
   - vm_compute;lia.
   - vm_compute;lia. }
 rewrite <-Last.
 eapply(store_output_two_steps _ (history 9257%nat)(history 9258%nat)(history 9259%nat)word(store_mask_word b0 b1 b2 b3)(store_output_offset_word a0 a1)).
 - rewrite(Held 7925 store_data_register 9257%nat ltac:(vm_compute;lia)). exact Word.
 - exact MaskValue.
 - exact Offset.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
Qed.
