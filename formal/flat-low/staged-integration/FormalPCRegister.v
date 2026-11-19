Require Import StagedRegisterHold FormalSingletonSymbolic ExternalReset StagedFlatCircuitIteration FormalLocalHistory CoreSocModel ComparisonNodes RegisterInvariants ConcreteRegisterInitialization UIntRegisterCertificate.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma pc_register_present : has_register 7768 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pc_register_declarations : uint_register_declarations 7768 33 flat_statements.
Proof. apply uint_register_declarations_b_sound. vm_compute. reflexivity. Qed.
Theorem symbolic_pc_register inputs path state :
 map_uint_concrete 7768 33 (initialize_symbolic_registers inputs path flat_statements state).
Proof. apply initialize_establishes_uint_concrete; [exact pc_register_declarations|exact pc_register_present]. Qed.
Theorem pc_register_combinational_hold invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7768 result = VM.find 7768 old.
Proof. intro Step. exact (staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7768 pc_register_present Step). Qed.
Print Assumptions pc_register_combinational_hold.
Local Opaque generated_modules generated_top.
Theorem circuit_symbolic_pc_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 map_uint_concrete 7768 33 (top_environment states).
Proof.
 intro Step.
 destruct (singleton_symbolic_property generated_modules generated_top 0 top_ports flat_statements memory inputs states
 (map_uint_concrete 7768 33) flat_instance_map_exact flat_module_exact (symbolic_pc_register inputs nil) Step)
 as [env [Env Value]]. unfold top_environment. rewrite Env. exact Value.
Qed.
Print Assumptions circuit_symbolic_pc_concrete.
