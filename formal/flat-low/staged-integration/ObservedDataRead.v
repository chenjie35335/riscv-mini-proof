Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalDataStorageInitialization FormalDataReadersInvariant ObservedDataReaders DataMemoryReaders ConcreteMemoryRead.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem observed_data_read_concrete memory inputs k states port address width value :
 generated_observe memory inputs k = Some states ->
 List.In port [::1;2;3;4;5] ->
 data_storage_concrete states ->
 read_memory_port_field (top_environment states) 9178 port 0 = Some (Gval (Fuint width) address) ->
 eval_memory_reader_data flat_memories 9178 port (top_environment states) (top_environment states) = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Observe Member [values [Storage Concrete]] Address Read.
 destruct (observed_data_readers memory inputs k states Observe) as [_ Enabled].
 exact (data_memory_any_reader_concrete port (top_environment states) (top_environment states)
 values [::true] address width value Member Storage (Enabled port Member) (Logic.eq_refl _) Address Concrete Read).
Qed.
Print Assumptions observed_data_read_concrete.
