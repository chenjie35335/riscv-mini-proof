Require Import CoreSocModel ComparisonNodes RegisterInvariants UIntRegisterCertificate ConcreteRegisterInitialization.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths FormalInitialization.
Lemma store_write_valid_uint1_declaration : uint_register_declarations (N.of_nat 8028) 1 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute;reflexivity. Qed.
Lemma store_write_valid_register_present : has_register (N.of_nat 8028) flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Theorem store_write_valid_symbolic_initial inputs path state :
 map_uint_concrete (N.of_nat 8028) 1(initialize_symbolic_registers inputs path flat_statements state).
Proof. apply initialize_establishes_uint_concrete;[exact store_write_valid_uint1_declaration|exact store_write_valid_register_present]. Qed.
Require Import StagedObservedRegister FormalSingletonSymbolic StagedFlatCircuitIteration FormalLocalHistory.
From firrtl Require Import Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements.
Theorem store_write_valid_circuit_initial memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs=Some states ->
 map_uint_concrete (N.of_nat 8028) 1(top_environment states).
Proof.
 intro Init.
 destruct(singleton_symbolic_property generated_modules generated_top (N.of_nat 0) staged_top_ports flat_statements
 memory inputs states (map_uint_concrete (N.of_nat 8028) 1) flat_instance_map_exact flat_module_exact)as[env[Env Concrete]].
 - intro initial. exact(store_write_valid_symbolic_initial inputs nil initial).
 - exact Init.
 - unfold top_environment. rewrite Env. exact Concrete.
Qed.
