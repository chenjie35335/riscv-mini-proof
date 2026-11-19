Require Import ConcreteMemoryWrite ConcreteMemoryRead.
From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem concrete_memory_write_known_gate mm mem port old current result layout writer width value values gate :
 VM.find mem mm = Some layout ->
 find_mem_port port (ml_writers layout) = Some writer ->
 VM.find (ml_storage_id layout) current = Some (Aval (Gtyp (Fuint width)) values) ->
 concrete_uint_array width values ->
 memory_write_gate old mem port writer = Some gate ->
 (gate = MemoryOff \/ gate = MemoryOn) ->
 (gate = MemoryOn -> exists source_width bits address_width address_bits,
   value = Gval (Fuint source_width) bits /\
   read_memory_port_field old mem port (addr writer) = Some (Gval (Fuint address_width) address_bits)) ->
 write_memory_data mm mem port value true old current = Some result ->
 exists updated, VM.find (ml_storage_id layout) result = Some (Aval (Gtyp (Fuint width)) updated) /\ concrete_uint_array width updated.
Proof.
 intros Layout Writer Storage Concrete Gate Known Active Write.
 destruct Known as [Off|On].
 - subst gate. unfold write_memory_data in Write. rewrite Layout Writer Storage Gate in Write.
   inversion Write; subst result. exists values. split; assumption.
 - subst gate. destruct (Active (Logic.eq_refl _)) as [source_width [bits [address_width [address_bits [Value Address]]]]].
   subst value. eapply concrete_enabled_memory_write; eauto.
Qed.
Lemma concrete_memory_gate_known sem mem port writer enable_width enable_bits mask_width mask_bits :
 read_memory_port_field sem mem port (en writer) = Some (Gval (Fuint enable_width) enable_bits) ->
 read_memory_port_field sem mem port (mask writer) = Some (Gval (Fuint mask_width) mask_bits) ->
 exists gate, memory_write_gate sem mem port writer = Some gate /\ (gate = MemoryOff \/ gate = MemoryOn).
Proof.
 intros Enable Mask. unfold memory_write_gate, classify_memory_gate.
 rewrite Enable Mask. destruct (is_zero enable_bits); [exists MemoryOff; auto|].
 destruct (is_zero mask_bits); [exists MemoryOff|exists MemoryOn]; auto.
Qed.
Print Assumptions concrete_memory_write_known_gate.
Print Assumptions concrete_memory_gate_known.
