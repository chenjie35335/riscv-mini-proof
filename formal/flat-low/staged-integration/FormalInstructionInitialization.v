Require Import CoreSocModel RegisterInvariants StagedFlatCircuitIteration StagedObservedRegister FormalSingletonSymbolic ConcreteRegisterInitialization UIntRegisterCertificate FormalInstructionResetCycle.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma instruction_7748_uint_declarations : uint_register_declarations 7748 32 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_7750_uint_declarations : uint_register_declarations 7750 32 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute. reflexivity. Qed.
Definition instruction_initial_property env := map_uint_concrete 7748 32 env /\ map_uint_concrete 7750 32 env.
Lemma instruction_symbolic_init inputs path state :
 instruction_initial_property (initialize_symbolic_registers inputs path flat_statements state).
Proof.
 split; apply initialize_establishes_uint_concrete.
 - exact instruction_7748_uint_declarations.
 - exact (proj2 (instruction_register_shape 7748 ltac:(vm_compute; reflexivity))).
 - exact instruction_7750_uint_declarations.
 - exact (proj2 (instruction_register_shape 7750 ltac:(vm_compute; reflexivity))).
Qed.
Local Opaque generated_modules generated_top.
Theorem instruction_initial_state_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ instruction_initial_property env.
Proof.
 intro Init.
 exact (singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements
 memory inputs states instruction_initial_property flat_instance_map_exact flat_module_exact
 (instruction_symbolic_init inputs nil) Init).
Qed.
Print Assumptions instruction_initial_state_concrete.
