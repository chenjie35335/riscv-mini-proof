Require Import DataMemoryConcrete ConcreteMemoryRead ComparisonNodes.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_reader_exact port :
 List.In port [:: 1;2;3;4;5] ->
 find_mem_port port (ml_readers data_memory_layout) = Some (@mk_mem_port VarOrder.T port 0 1 2 3).
Proof.
 intro Member. cbn [List.In] in Member.
 repeat destruct Member as [Same|Member]; try (subst port; reflexivity).
 contradiction.
Qed.
Theorem data_memory_any_reader_concrete port old current values enable_bits address_bits address_width value :
 List.In port [:: 1;2;3;4;5] ->
 VM.find 9179 old = Some (Aval (Gtyp (Fuint 32)) values) ->
 read_memory_port_field old 9178 port 1 = Some (Gval (Fuint 1) enable_bits) ->
 is_zero enable_bits = false ->
 read_memory_port_field old 9178 port 0 = Some (Gval (Fuint address_width) address_bits) ->
 concrete_uint_array 32 values ->
 eval_memory_reader_data ComparisonNodes.flat_memories 9178 port old current = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Member Storage Enable Enabled Address Concrete Read.
 exact (enabled_concrete_memory_read ComparisonNodes.flat_memories 9178 port old current data_memory_layout
 (@mk_mem_port VarOrder.T port 0 1 2 3) values 32 address_width enable_bits address_bits value
 data_memory_layout_exact (data_reader_exact port Member) Storage Enable Enabled Address Concrete Read).
Qed.
Print Assumptions data_memory_any_reader_concrete.
