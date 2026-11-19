Require Import ConcreteMemoryRead RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma concrete_uint_array_update width values index bits updated :
 concrete_uint_array width values ->
 array_update_memory index (Gval (Fuint width) bits) values = Some updated ->
 concrete_uint_array width updated.
Proof.
 revert index updated. induction values as [|head tail IH]; intros index updated Concrete Update.
 - destruct index; discriminate Update.
 - destruct Concrete as [Head Tail]. destruct index as [|index].
   + inversion Update; subst. split; [eexists; reflexivity|exact Tail].
   + cbn [array_update_memory] in Update.
     destruct (array_update_memory index (Gval (Fuint width) bits) tail) as [rest|] eqn:Rest; [|discriminate Update].
     inversion Update; subst. split; [exact Head|exact (IH index rest Tail Rest)].
Qed.
Theorem concrete_enabled_memory_write mm mem port old current result layout writer width source_width bits values address_width address_bits :
 VM.find mem mm = Some layout ->
 find_mem_port port (ml_writers layout) = Some writer ->
 VM.find (ml_storage_id layout) current = Some (Aval (Gtyp (Fuint width)) values) ->
 concrete_uint_array width values ->
 memory_write_gate old mem port writer = Some MemoryOn ->
 read_memory_port_field old mem port (addr writer) = Some (Gval (Fuint address_width) address_bits) ->
 write_memory_data mm mem port (Gval (Fuint source_width) bits) true old current = Some result ->
 exists updated, VM.find (ml_storage_id layout) result = Some (Aval (Gtyp (Fuint width)) updated) /\ concrete_uint_array width updated.
Proof.
 intros Layout Writer Storage Concrete Gate Address Write.
 unfold write_memory_data in Write. rewrite Layout Writer Storage Gate in Write.
 cbn [adapt_hvalue_as_type] in Write. unfold write_memory_address in Write. rewrite Address in Write.
 destruct (array_update_memory (to_nat address_bits) (Gval (Fuint width) (zext_to width (take width bits))) values) as [updated|] eqn:Update; [|discriminate Write].
 inversion Write; subst result. exists updated. split.
 - apply RegisterMapFacts.find_add_eq. reflexivity.
 - exact (concrete_uint_array_update width values (to_nat address_bits) (zext_to width (take width bits)) updated Concrete Update).
Qed.
Print Assumptions concrete_enabled_memory_write.
