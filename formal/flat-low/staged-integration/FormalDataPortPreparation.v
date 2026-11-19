Require Import CoreSocModel ComparisonNodes MemoryPortPreparation FormalSingletonAnyPreparation StagedFlatCircuitIteration ExternalReset FormalLocalHistory RegisterInvariants DataReaderEnableConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_port_memory := @mk_fmem VarOrder.T 9179 (Gtyp (Fuint 32)) 16
 [:: @mk_mem_port VarOrder.T 2 0 1 2 3; @mk_mem_port VarOrder.T 3 0 1 2 3;
 @mk_mem_port VarOrder.T 4 0 1 2 3; @mk_mem_port VarOrder.T 5 0 1 2 3;
 @mk_mem_port VarOrder.T 1 0 1 2 3]
 [:: @mk_mem_port VarOrder.T 0 0 1 2 3] 0 1 undefined.
Definition data_port_initial_fields := data_port_fields
 (Needtobedefined (Gtyp (Fuint 16))) (Needtobedefined (Gtyp (Fuint 1)))
 (Needtobedefined (Gtyp Fclock)) (Needtobedefined (Gtyp (Fuint 1)))
 (Needtobedefined (Gtyp (Fuint 32))).
Lemma data_port_initial_shape : memory_bundle_initial data_port_memory =
 data_ports data_port_initial_fields data_port_initial_fields data_port_initial_fields
 data_port_initial_fields data_port_initial_fields data_port_initial_fields.
Proof. reflexivity. Qed.
Lemma data_port_initial_safe : initial_port_safe 9178 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Lemma data_port_initial_description : port_seed_description 9178 flat_statements None = Some data_port_memory.
Proof. vm_compute. reflexivity. Qed.
Theorem data_port_statements_prepared modules previous current result :
 statements_initial_map_with_memory modules flat_statements previous current = Some result ->
 VM.find 9178 result = Some (memory_bundle_initial data_port_memory).
Proof.
 intro Step.
 pose proof (initial_port_projection flat_statements modules previous current result 9178 None (VM.find 9178 current)
 data_port_initial_safe (Logic.eq_refl _) Step) as Value.
 rewrite data_port_initial_description in Value. exact Value.
Qed.
Lemma external_ports_preserve_data_port initial external result :
 update_external_ports initial external top_ports = Some result ->
 VM.find 9178 result = VM.find 9178 initial.
Proof.
 intro Step.
 change (match VM.find 0 external with
 | Some clock => match VM.find 1 external with
 | Some reset => Some (VM.add 1 reset (VM.add 0 clock initial))
 | None => None end | None => None end = Some result) in Step.
 destruct (VM.find 0 external); [|discriminate Step].
 destruct (VM.find 1 external); [|discriminate Step].
 inversion Step; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite RegisterMapFacts.find_add_neq; [|discriminate]. reflexivity.
Qed.
Local Opaque generated_modules generated_top.
Theorem circuit_data_port_prepared previous external prepared :
 circuit_initial_map_with_memory generated_modules generated_top previous external = Some prepared ->
 VM.find 9178 (top_environment prepared) = Some (memory_bundle_initial data_port_memory).
Proof.
 intro Prepare.
 destruct (singleton_any_prepared_property generated_modules generated_top 0 top_ports flat_statements previous external prepared
 (fun env => VM.find 9178 env = Some (memory_bundle_initial data_port_memory))
 flat_instance_map_exact flat_module_exact (Logic.eq_refl _)) as [env [Env Value]].
 - intros old initial Init. exact (data_port_statements_prepared generated_modules old _ initial Init).
 - intros initial result Value Update. rewrite (external_ports_preserve_data_port initial external result Update). exact Value.
 - exact Prepare.
 - unfold top_environment. rewrite Env. exact Value.
Qed.
Print Assumptions circuit_data_port_prepared.
