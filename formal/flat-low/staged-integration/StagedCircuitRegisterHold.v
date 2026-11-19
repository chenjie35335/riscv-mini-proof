Require Import CoreSocModel RegisterInvariants StagedRegisterHold StagedFlatCircuitIteration.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition staged_register_lookup id (states : SVM.t (VM.t hvalue)) :=
 match SVM.find nil states with Some env => VM.find id env | None => None end.
Lemma staged_circuit_holds_register invalid states result id :
 has_register id flat_statements = true ->
 formal_circuit_value_iter invalid generated_modules generated_top states false = Some result ->
 staged_register_lookup id result = staged_register_lookup id states.
Proof.
 intros Register Step.
 destruct (flat_iteration_projection invalid states false result Step)
   as [old [next [Old [Next State]]]].
 unfold staged_register_lookup. rewrite Old State.
 eapply staged_combinational_holds_registers; eassumption.
Qed.
Theorem staged_iterations_hold_register inputs n states result id :
 has_register id flat_statements = true ->
 circuit_formal_iterations generated_modules generated_top inputs n states = Some result ->
 staged_register_lookup id result = staged_register_lookup id states.
Proof.
 revert states result. induction n as [|n IH]; intros states result Register Step.
 - cbn [circuit_formal_iterations] in Step. inversion Step. reflexivity.
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs)
     generated_modules generated_top states false) as [next|] eqn:Next;
     [|discriminate Step].
   rewrite (IH next result Register Step).
   eapply staged_circuit_holds_register; eassumption.
Qed.
Print Assumptions staged_iterations_hold_register.
