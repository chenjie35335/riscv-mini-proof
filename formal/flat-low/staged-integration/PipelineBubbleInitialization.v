Require Import CoreSocModel StagedFlatCircuitIteration StagedObservedRegister RegisterInvariants RegisterPreparationFrames FormalSingletonSymbolic ConcreteRegisterInitialization UIntRegisterCertificate.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma bubble7945_present : has_register 7945 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bubble7945_initial_safe : initial_register_safe 7945 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Lemma bubble7945_uint_declarations : uint_register_declarations 7945 1 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble7945_symbolic_init inputs path state :
 map_uint_concrete 7945 1 (initialize_symbolic_registers inputs path flat_statements state).
Proof. apply initialize_establishes_uint_concrete; [exact bubble7945_uint_declarations|exact bubble7945_present]. Qed.
Local Opaque generated_modules generated_top.
Theorem bubble7945_initial_state_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ map_uint_concrete 7945 1 env.
Proof.
 intro Init.
 exact (singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements
 memory inputs states (map_uint_concrete 7945 1) flat_instance_map_exact flat_module_exact
 (bubble7945_symbolic_init inputs nil) Init).
Qed.
Print Assumptions bubble7945_initial_state_concrete.

Lemma bubble7947_present : has_register 7947 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma bubble7947_initial_safe : initial_register_safe 7947 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Lemma bubble7947_uint_declarations : uint_register_declarations 7947 1 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute. reflexivity. Qed.
Lemma bubble7947_symbolic_init inputs path state :
 map_uint_concrete 7947 1 (initialize_symbolic_registers inputs path flat_statements state).
Proof. apply initialize_establishes_uint_concrete; [exact bubble7947_uint_declarations|exact bubble7947_present]. Qed.
Local Opaque generated_modules generated_top.
Theorem bubble7947_initial_state_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ map_uint_concrete 7947 1 env.
Proof.
 intro Init.
 exact (singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements
 memory inputs states (map_uint_concrete 7947 1) flat_instance_map_exact flat_module_exact
 (bubble7947_symbolic_init inputs nil) Init).
Qed.
Print Assumptions bubble7947_initial_state_concrete.

