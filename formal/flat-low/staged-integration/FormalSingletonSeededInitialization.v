Require Import StagedFlatCircuitIteration.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Lemma singleton_seeded_symbolic_property modules top mi ports stmts memory inputs states
 (P : VM.t hvalue -> Prop) :
 find_circuit_instances modules top = Some (SVM.add nil mi (SVM.empty VarOrder.T)) ->
 find_module modules mi = Some (@FInmod VarOrder.T mi ports stmts) ->
 (forall env, P (initialize_symbolic_registers inputs nil stmts (initialize_module_memories memory nil stmts env))) ->
 circuit_symbolic_initial_state modules top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ P env.
Proof.
 intros Instances Module Property Step. unfold circuit_symbolic_initial_state in Step.
 rewrite Instances in Step.
 destruct (circuit_initial_map_with_memory modules top None (formal_external_inputs inputs))
 as [initial|]; [|discriminate Step].
 rewrite SVM.fold_1 in Step.
 assert (Entries : SVM.elements (SVM.add nil mi (SVM.empty VarOrder.T)) = [:: (nil,mi)]) by reflexivity.
 rewrite Entries in Step. cbn [List.fold_left fst snd] in Step. rewrite Module in Step.
 destruct (SVM.find nil initial) as [env|]; [|discriminate Step].
 inversion Step; subst states.
 eexists. split; [apply FlatStateFacts.find_add_eq; reflexivity|apply Property].
Qed.
