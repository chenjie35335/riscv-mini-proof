Require Import CoreSocModel ComparisonNodes ConcreteMemoryRead ConcreteMemoryWriteGate.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_memory_layout : memory_layout :=
 {| ml_storage_id := 9179; ml_data_type := Gtyp (Fuint 32); ml_depth := 16;
 ml_readers := [:: @mk_mem_port VarOrder.T 2 0 1 2 3;
 @mk_mem_port VarOrder.T 3 0 1 2 3; @mk_mem_port VarOrder.T 4 0 1 2 3;
 @mk_mem_port VarOrder.T 5 0 1 2 3; @mk_mem_port VarOrder.T 1 0 1 2 3];
 ml_writers := [:: @mk_mem_port VarOrder.T 0 0 1 2 3]; ml_read_write := undefined |}.
Lemma data_memory_layout_exact : VM.find 9178 flat_memories = Some data_memory_layout.
Proof. vm_compute. reflexivity. Qed.
Theorem data_memory_write_concrete old current result value values gate :
 VM.find 9179 current = Some (Aval (Gtyp (Fuint 32)) values) ->
 concrete_uint_array 32 values ->
 memory_write_gate old 9178 0 (@mk_mem_port VarOrder.T 0 0 1 2 3) = Some gate ->
 (gate = MemoryOff \/ gate = MemoryOn) ->
 (gate = MemoryOn -> exists source_width bits address_width address_bits,
   value = Gval (Fuint source_width) bits /\
   read_memory_port_field old 9178 0 0 = Some (Gval (Fuint address_width) address_bits)) ->
 write_memory_data flat_memories 9178 0 value true old current = Some result ->
 exists updated, VM.find 9179 result = Some (Aval (Gtyp (Fuint 32)) updated) /\ concrete_uint_array 32 updated.
Proof.
 intros Storage Concrete Gate Known Active Write.
 exact (concrete_memory_write_known_gate flat_memories 9178 0 old current result
 data_memory_layout (@mk_mem_port VarOrder.T 0 0 1 2 3) 32 value values gate
 data_memory_layout_exact (Logic.eq_refl _) Storage Concrete Gate Known Active Write).
Qed.
Theorem data_memory_read_concrete old current values enable_bits address_bits address_width value :
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 read_memory_port_field old 9178 1 1 = Some (Gval (Fuint 1) enable_bits) ->
 is_zero enable_bits = false ->
 read_memory_port_field old 9178 1 0 = Some (Gval (Fuint address_width) address_bits) ->
 concrete_uint_array 32 values ->
 eval_memory_reader_data flat_memories 9178 1 old current = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Storage Enable Enabled Address Concrete Read.
 exact (enabled_concrete_memory_read flat_memories 9178 1 old current data_memory_layout
 (@mk_mem_port VarOrder.T 1 0 1 2 3) values 32 address_width enable_bits address_bits value
 data_memory_layout_exact (Logic.eq_refl _) Storage Enable Enabled Address Concrete Read).
Qed.
Print Assumptions data_memory_write_concrete.
Print Assumptions data_memory_read_concrete.
