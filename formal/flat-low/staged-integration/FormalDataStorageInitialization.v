Require Import CoreSocModel ComparisonNodes RegisterInvariants MemorySeedProjection ConcreteMemoryRead FormalSingletonSeededInitialization StagedFlatCircuitIteration ExternalReset FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma data_storage_nonregister : has_register 9179 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Lemma data_seed_description : memory_seed_description 9179 flat_statements None = Some (9178, Gtyp (Fuint 32), 16%nat).
Proof. vm_compute. reflexivity. Qed.
Lemma data_storage_seeded contents path state :
 VM.find 9179 (initialize_module_memories contents path flat_statements state) =
 Some (memory_initial_value (contents path 9178) (Atyp (Gtyp (Fuint 32)) 16) [::]).
Proof.
 pose proof (memory_seed_projection flat_statements contents path state 9179 None (VM.find 9179 state) (Logic.eq_refl _)) as Seed.
 rewrite data_seed_description in Seed. exact Seed.
Qed.
Definition data_storage_concrete states := exists values,
 VM.find 9179 (top_environment states) = Some (Aval (Gtyp (Fuint 32)) values) /\ concrete_uint_array 32 values.
Local Opaque generated_modules generated_top.
Theorem symbolic_data_storage_concrete contents inputs states :
 circuit_symbolic_initial_state generated_modules generated_top contents inputs = Some states ->
 data_storage_concrete states.
Proof.
 intro Step.
 destruct (initial_uint_array_concrete (contents nil 9178) 32 16 nil) as [values [Seed Concrete]].
 destruct (singleton_seeded_symbolic_property generated_modules generated_top 0 top_ports flat_statements
 contents inputs states (fun env => VM.find 9179 env = Some (Aval (Gtyp (Fuint 32)) values))
 flat_instance_map_exact flat_module_exact) as [env [Env Value]].
 - intro initial.
   rewrite (symbolic_initialization_preserves_nonregister flat_statements inputs nil _ 9179 data_storage_nonregister).
   rewrite data_storage_seeded Seed. reflexivity.
 - exact Step.
 - exists values. unfold top_environment. rewrite Env. split; assumption.
Qed.
Print Assumptions symbolic_data_storage_concrete.
