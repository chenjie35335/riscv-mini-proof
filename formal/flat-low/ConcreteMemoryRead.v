From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Fixpoint concrete_uint_array width (values : array_value) : Prop :=
 match values with
 | Anil => True
 | Acons value rest => (exists bits, value = Gval (Fuint width) bits) /\ concrete_uint_array width rest
 end.
Lemma concrete_uint_array_read width values index value :
 concrete_uint_array width values -> array_nth index values = Some value ->
 exists bits, value = Gval (Fuint width) bits.
Proof.
 revert index. induction values as [|head tail IH]; intros index Concrete Read.
 - destruct index; discriminate.
 - destruct Concrete as [Head Tail]. destruct index as [|index].
   + inversion Read; subst value. exact Head.
   + exact (IH index Tail Read).
Qed.
Lemma initial_uint_array_concrete contents width count location :
 exists values,
 memory_initial_value contents (Atyp (Gtyp (Fuint width)) count) location = Aval (Gtyp (Fuint width)) values /\
 concrete_uint_array width values.
Proof.
 unfold memory_initial_value. cbn [input_value_of_type].
 eexists. split; [reflexivity|].
 generalize 0%nat as start. induction count as [|count IH]; intro start.
 - exact I.
 - cbn [concrete_uint_array]. split; [eexists; reflexivity|apply IH].
Qed.
Lemma enabled_concrete_memory_read mm mem port old current layout reader values width address_width enable_bits address_bits value :
 VM.find mem mm = Some layout ->
 find_mem_port port (ml_readers layout) = Some reader ->
 VM.find (ml_storage_id layout) old = Some (Aval (Gtyp (Fuint width)) values) ->
 read_memory_port_field old mem port (en reader) = Some (Gval (Fuint 1) enable_bits) ->
 is_zero enable_bits = false ->
 read_memory_port_field old mem port (addr reader) = Some (Gval (Fuint address_width) address_bits) ->
 concrete_uint_array width values ->
 eval_memory_reader_data mm mem port old current = Some value ->
 exists bits, value = Gval (Fuint width) bits.
Proof.
 intros Memory Reader Storage Enable Enabled Address Concrete Read.
 unfold eval_memory_reader_data in Read.
 rewrite Memory Reader Storage Enable Enabled Address in Read.
 exact (concrete_uint_array_read width values (to_nat address_bits) value Concrete Read).
Qed.
Print Assumptions initial_uint_array_concrete.
Print Assumptions enabled_concrete_memory_read.
