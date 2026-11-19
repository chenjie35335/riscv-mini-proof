Require Import CoreSocModel ComparisonNodes ConcreteMemoryRead.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition instruction_memory_layout : memory_layout :=
 {| ml_storage_id := 9177; ml_data_type := Gtyp (Fuint 32); ml_depth := 16;
 ml_readers := [:: @mk_mem_port VarOrder.T 0 0 1 2 3]; ml_writers := [::]; ml_read_write := undefined |}.
Lemma instruction_memory_layout_exact : VM.find 9176 flat_memories = Some instruction_memory_layout.
Proof. vm_compute. reflexivity. Qed.
Theorem instruction_memory_read_concrete old current values enable_bits address_bits address_width value :
 VM.find 9177 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 read_memory_port_field old 9176 0 1 = Some (Gval (Fuint 1) enable_bits) ->
 is_zero enable_bits = false ->
 read_memory_port_field old 9176 0 0 = Some (Gval (Fuint address_width) address_bits) ->
 concrete_uint_array 32 values ->
 eval_memory_reader_data flat_memories 9176 0 old current = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Storage Enable Enabled Address Concrete Read.
 exact (enabled_concrete_memory_read flat_memories 9176 0 old current instruction_memory_layout
 (@mk_mem_port VarOrder.T 0 0 1 2 3) values 32 address_width enable_bits address_bits value
 instruction_memory_layout_exact (Logic.eq_refl _) Storage Enable Enabled Address Concrete Read).
Qed.
Print Assumptions instruction_memory_read_concrete.
