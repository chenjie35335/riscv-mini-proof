Require Import CoreSocModel RegisterInvariants RegisterPreparationFrames StagedSingletonPreparation StagedFlatCircuitIteration StagedCircuitRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition staged_top_ports := match generated_module_0 with FInmod _ ps _ | FExmod _ ps _ => ps end.
Lemma staged_external_preserves_register initial external result id :
 id != 0 -> id != 1 ->
 update_external_ports initial external staged_top_ports = Some result ->
 VM.find id result = VM.find id initial.
Proof.
 intros NotClock NotReset Step.
 change (match VM.find 0 external with
 | Some clock => match VM.find 1 external with
 | Some reset => Some (VM.add 1 reset (VM.add 0 clock initial))
 | None => None end | None => None end = Some result) in Step.
 destruct (VM.find 0 external); [|discriminate Step].
 destruct (VM.find 1 external); [|discriminate Step].
 inversion Step; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|move/negP: NotReset; exact].
 rewrite RegisterMapFacts.find_add_neq; [reflexivity|move/negP: NotClock; exact].
Qed.
Local Opaque generated_modules generated_top.
Lemma staged_prepared_register_copies previous old external prepared id :
 id != 0 -> id != 1 ->
 initial_register_safe id flat_statements -> has_register id flat_statements = true ->
 SVM.find nil previous = Some old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some prepared ->
 staged_register_lookup id prepared = VM.find id old.
Proof.
 intros NotClock NotReset Safe Register Old Prepare.
 destruct (singleton_prepared_property generated_modules generated_top 0 staged_top_ports flat_statements
 previous old external prepared (fun env => VM.find id env = VM.find id old)
 flat_instance_map_exact flat_module_exact (Logic.eq_refl _) Old) as [result [Result Property]].
 - intros initial Init. eapply initial_register_copies; eassumption.
 - intros initial result Same Update.
   rewrite (staged_external_preserves_register initial external result id NotClock NotReset Update).
   exact Same.
 - exact Prepare.
 - unfold staged_register_lookup. rewrite Result. exact Property.
Qed.
Theorem staged_observed_register_copies memory inputs k committed old observed id :
 id != 0 -> id != 1 ->
 initial_register_safe id flat_statements -> has_register id flat_statements = true ->
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 staged_register_lookup id observed = VM.find id old.
Proof.
 intros NotClock NotReset Safe Register Run Old Observe.
 unfold generated_observe, generated_observe_cycle in Observe. rewrite Run in Observe.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare;
 [|discriminate Observe].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count)
 as [n|]; [|discriminate Observe].
 rewrite (staged_iterations_hold_register _ n prepared observed id Register Observe).
 eapply staged_prepared_register_copies; eassumption.
Qed.
Print Assumptions staged_observed_register_copies.
