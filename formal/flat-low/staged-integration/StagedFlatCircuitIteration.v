Require Import CoreSocModel RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var FMaps.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition flat_statements :=
 match generated_module_0 with FInmod _ _ s | FExmod _ _ s => s end.
Definition flat_memories := memory_map_of_stmts flat_statements.
Definition flat_instance_map := SVM.add [::] (N.of_nat 0) (SVM.empty VarOrder.T).
Lemma flat_instance_map_exact : find_circuit_instances generated_modules generated_top = Some flat_instance_map.
Proof. vm_compute. reflexivity. Qed.
Lemma flat_module_exact : find_module generated_modules (N.of_nat 0) = Some generated_module_0.
Proof. reflexivity. Qed.
Lemma flat_memories_exact : memory_map_for_module generated_modules (N.of_nat 0) = Some flat_memories.
Proof. reflexivity. Qed.
Lemma flat_sync_identity states : sync_circuit_ports generated_modules flat_instance_map states = Some states.
Proof. reflexivity. Qed.
Lemma flat_iteration_exact invalid states set_regs :
 formal_circuit_value_iter invalid generated_modules generated_top states set_regs =
 match SVM.find [::] states with
 | Some old =>
   match formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements with
   | Some next => Some (SVM.add [::] next states)
   | None => None end
 | None => None end.
Proof.
 unfold formal_circuit_value_iter.
 rewrite flat_instance_map_exact.
 rewrite SVM.fold_1.
 assert (Entries : SVM.elements flat_instance_map = [:: ([::], N.of_nat 0)]) by reflexivity.
 rewrite Entries. cbn [List.fold_left].
 rewrite flat_module_exact flat_memories_exact.
 cbn [fst snd].
 destruct (SVM.find [::] states) as [old|] eqn:Old.
 - change (match
      (match formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements with
       | Some next => Some (SVM.add [::] next states) | None => None end)
     with Some evaluated => sync_circuit_ports generated_modules flat_instance_map evaluated | None => None end =
     match formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements with
       | Some next => Some (SVM.add [::] next states) | None => None end).
   destruct (formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements) as [next|];
     [apply flat_sync_identity|reflexivity].
 - reflexivity.
Qed.
Print Assumptions flat_iteration_exact.
Module FlatStateFacts := FMapLemmas SVM.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma flat_iteration_projection invalid states set_regs result :
 formal_circuit_value_iter invalid generated_modules generated_top states set_regs = Some result ->
 exists old next,
 SVM.find [::] states = Some old /\
 formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements = Some next /\
 SVM.find [::] result = Some next.
Proof.
 rewrite flat_iteration_exact.
 destruct (SVM.find [::] states) as [old|] eqn:Old; [|discriminate].
 destruct (formal_value_iter (invalid [::]) flat_memories old set_regs old flat_statements)
   as [next|] eqn:Next; [|discriminate].
 intro Step. inversion Step; subst result.
 exists old, next. split; [reflexivity|]. split; [exact Next|].
 apply FlatStateFacts.find_add_eq. reflexivity.
Qed.
Lemma flat_iterations_last inputs n states result :
 circuit_formal_iterations generated_modules generated_top inputs (S n) states = Some result ->
 exists previous,
 circuit_formal_iterations generated_modules generated_top inputs n states = Some previous /\
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top previous false = Some result.
Proof.
 revert states result. induction n as [|n IH]; intros states result Step.
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter _ _ _ _ _) as [next|] eqn:Next;
     [|discriminate Step]. inversion Step; subst result.
   exists states. split; [reflexivity|exact Next].
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter _ _ _ _ _) as [next|] eqn:Next;
     [|discriminate Step].
   destruct (IH next result Step) as [previous [Prior Last]].
   exists previous. split; [|exact Last].
   cbn [circuit_formal_iterations]. rewrite Next. exact Prior.
Qed.
Print Assumptions flat_iteration_projection.
Print Assumptions flat_iterations_last.
