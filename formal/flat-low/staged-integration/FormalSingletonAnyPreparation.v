Require Import RegisterInvariants StagedFlatCircuitIteration.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma singleton_any_prepared_property modules top mi ports stmts previous external prepared
 (P : VM.t hvalue -> Prop) :
 find_circuit_instances modules top = Some (SVM.add nil mi (SVM.empty VarOrder.T)) ->
 find_module modules mi = Some (@FInmod VarOrder.T mi ports stmts) ->
 find_module modules top = Some (@FInmod VarOrder.T mi ports stmts) ->
 (forall old initial, statements_initial_map_with_memory modules stmts old
 (ports_initial_map ports) = Some initial -> P initial) ->
 (forall initial result, P initial -> update_external_ports initial external ports = Some result -> P result) ->
 circuit_initial_map_with_memory modules top previous external = Some prepared ->
 exists result, SVM.find nil prepared = Some result /\ P result.
Proof.
 intros Instances Module Top Statements Update Step.
 unfold circuit_initial_map_with_memory in Step. rewrite Instances in Step.
 rewrite SVM.fold_1 in Step.
 assert (Entries : SVM.elements (SVM.add nil mi (SVM.empty VarOrder.T)) = [:: (nil,mi)]) by reflexivity.
 rewrite Entries in Step. cbn [List.fold_left fst snd] in Step.
 unfold module_initial_map_with_memory in Step. rewrite Module in Step.
 destruct (statements_initial_map_with_memory modules stmts (match previous with Some pm => SVM.find nil pm | None => None end) (ports_initial_map ports))
 as [initial|] eqn:Init; [|discriminate Step].
 rewrite (FlatStateFacts.find_add_eq (eqxx nil)) Top in Step.
 destruct (update_external_ports initial external ports) as [result|] eqn:Applied; [|discriminate Step].
 inversion Step; subst prepared. exists result. split.
 - apply FlatStateFacts.find_add_eq. reflexivity.
 - apply (Update initial result); [eapply Statements; exact Init|exact Applied].
Qed.
