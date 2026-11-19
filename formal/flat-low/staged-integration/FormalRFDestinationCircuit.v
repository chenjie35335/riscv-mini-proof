Require Import CoreSocModel StagedFlatCircuitIteration StagedCircuitRegisterHold StagedIterationLemmas FormalInstructionResetCycle FormalRFDestination.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem rf_destination_circuit_two inputs initial result instruction :
 size instruction = 32%nat ->
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction) ->
 circuit_formal_iterations generated_modules generated_top inputs 2 initial = Some result ->
 exists env, SVM.find nil result = Some env /\
 VM.find 785 env = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))).
Proof.
 intros Size Instruction Steps. cbn [circuit_formal_iterations] in Steps.
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top initial false) as [s1|] eqn:First; [|discriminate Steps].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s1 false) as [s2|] eqn:Second; [|discriminate Steps].
 inversion Steps; subst result.
 destruct (flat_iteration_projection _ initial false s1 First) as [e0 [e1 [Old0 [Local1 New1]]]].
 destruct (flat_iteration_projection _ s1 false s2 Second) as [f1 [e2 [Old1 [Local2 New2]]]].
 rewrite New1 in Old1. inversion Old1; subst f1.
 unfold staged_register_lookup in Instruction. rewrite Old0 in Instruction.
 exists e2. split; [exact New2|].
 exact (rf_destination_port_after_two _ e0 e1 e2 instruction Size Instruction Local1 Local2).
Qed.
Theorem rf_destination_circuit_settled inputs n initial result instruction :
 size instruction = 32%nat ->
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction) ->
 circuit_formal_iterations generated_modules generated_top inputs (Nat.add n 2) initial = Some result ->
 exists env, SVM.find nil result = Some env /\
 VM.find 785 env = Some (Gval (Fuint 5) (drop 7 (take 12 instruction))).
Proof.
 intros Size Instruction Steps. rewrite formal_iterations_append in Steps.
 destruct (circuit_formal_iterations generated_modules generated_top inputs n initial) as [middle|] eqn:Prefix; [|discriminate Steps].
 apply (rf_destination_circuit_two inputs middle result instruction); [exact Size| |exact Steps].
 rewrite (staged_iterations_hold_register inputs n initial middle 7750
 (proj2 (instruction_register_shape 7750 ltac:(vm_compute; reflexivity))) Prefix).
 exact Instruction.
Qed.
Print Assumptions rf_destination_circuit_settled.
