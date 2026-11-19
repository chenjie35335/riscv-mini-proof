Require Import RFShiftCycle RFReadPorts.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Definition cycle_shift_semantics immediate lane bank instruction :=
 rf_shift_result immediate lane instruction (bank(to_nat(rf_instruction_address false instruction)))(bank(to_nat(rf_instruction_address true instruction))).
Lemma cycle_shift_semantics_bank_ext immediate lane instruction left right :
 size instruction=32%nat ->(forall index,(index<32)%coq_nat ->left index=right index) ->
 cycle_shift_semantics immediate lane left instruction=cycle_shift_semantics immediate lane right instruction.
Proof.
 intros Size Banks. unfold cycle_shift_semantics.
 assert(Bound:forall second,(to_nat(rf_instruction_address second instruction)<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second instruction))as B.
 rewrite(rf_instruction_address_size second instruction Size)in B. exact(elimT ltP B). }
 rewrite(Banks _ (Bound false))(Banks _ (Bound true)). reflexivity.
Qed.
