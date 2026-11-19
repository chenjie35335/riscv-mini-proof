Require Import CoreSocModel ExternalReset StagedFlatCircuitIteration RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma top_external_reset top external result value :
 VM.find 1 external = Some value ->
 update_external_ports top external top_ports = Some result ->
 VM.find 1 result = Some value.
Proof.
 intros Reset Step.
 change (match VM.find 0 external with
 | Some clock => match VM.find 1 external with
 | Some reset => Some (VM.add 1 reset (VM.add 0 clock top))
 | None => None end | None => None end = Some result) in Step.
 rewrite Reset in Step. destruct (VM.find 0 external); [|discriminate Step].
 inversion Step; subst result. apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Lemma prepared_top_property modules top previous external prepared mi ports stmts (P : VM.t hvalue -> Prop) :
 find_module modules top = Some (@FInmod VarOrder.T mi ports stmts) ->
 (forall initial result, update_external_ports initial external ports = Some result -> P result) ->
 circuit_initial_map_with_memory modules top previous external = Some prepared ->
 exists env, SVM.find nil prepared = Some env /\ P env.
Proof.
 intros Module Update Prepare. unfold circuit_initial_map_with_memory in Prepare.
 destruct (find_circuit_instances modules top) as [instances|]; [|discriminate Prepare].
 rewrite Module in Prepare.
 match type of Prepare with context [SVM.fold ?f ?im ?seed] =>
 destruct (SVM.fold f im seed) as [initial|] end; [|discriminate Prepare].
 destruct (SVM.find nil initial) as [initial_top|]; [|discriminate Prepare].
 destruct (update_external_ports initial_top external ports) as [result|] eqn:Applied; [|discriminate Prepare].
 inversion Prepare; subst prepared. exists result. split.
 - apply FlatStateFacts.find_add_eq. reflexivity.
 - exact (Update initial_top result Applied).
Qed.
Theorem top_reset_prepared previous external prepared value :
 VM.find 1 external = Some value ->
 circuit_initial_map_with_memory generated_modules generated_top previous external = Some prepared ->
 exists env, SVM.find nil prepared = Some env /\ VM.find 1 env = Some value.
Proof.
 intros Reset Prepare.
 eapply (prepared_top_property generated_modules generated_top previous external prepared
  0 top_ports StagedFlatCircuitIteration.flat_statements (fun env => VM.find 1 env = Some value));
 [reflexivity| |exact Prepare].
 intros initial result Update. exact (top_external_reset initial external result value Reset Update).
Qed.
Print Assumptions top_reset_prepared.
