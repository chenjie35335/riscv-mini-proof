Require Import CoreSocModel StagedFlatCircuitIteration StagedCircuitRegisterHold StagedIterationLemmas FormalInstructionResetCycle FormalInstructionResetConstants FormalRFDestinationCircuit FormalRFEnableShape FormalRFWriteEnable.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem rf_nop_disables_after_four inputs initial result :
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction_nop) ->
 circuit_formal_iterations generated_modules generated_top inputs 4 initial = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 954 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Instruction Steps.
 change (circuit_formal_iterations generated_modules generated_top inputs (Nat.add 2 2) initial = Some result) in Steps.
 rewrite formal_iterations_append in Steps.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 2 initial) as [s2|] eqn:First; [|discriminate Steps].
 destruct (rf_destination_circuit_two inputs initial s2 instruction_nop (Logic.eq_refl _) Instruction First) as [e2 [E2 Address]].
 cbn [circuit_formal_iterations] in Steps.
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s2 false) as [s3|] eqn:Third; [|discriminate Steps].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s3 false) as [s4|] eqn:Fourth; [|discriminate Steps].
 inversion Steps; subst result.
 destruct (flat_iteration_projection _ s2 false s3 Third) as [f2 [e3 [Old2 [Local3 New3]]]].
 destruct (flat_iteration_projection _ s3 false s4 Fourth) as [f3 [e4 [Old3 [Local4 New4]]]].
 rewrite E2 in Old2. inversion Old2; subst f2.
 rewrite New3 in Old3. inversion Old3; subst f3.
 pose proof (rf_address_nonzero_node _ e2 e2 e3 (drop 7 (take 12 instruction_nop)) Address Local3) as Zero.
 destruct (rf_input_enable_normalized _ e2 e2 e3 Local3) as [value [Value Normal]].
 exists e4. split; [exact New4|].
 exact (rf_zero_address_disables_write _ e3 e3 e4 value Value Normal Zero Local4).
Qed.
Theorem rf_nop_disables_settled inputs n initial result :
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction_nop) ->
 circuit_formal_iterations generated_modules generated_top inputs (Nat.add n 4) initial = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 954 env = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Instruction Steps. rewrite formal_iterations_append in Steps.
 destruct (circuit_formal_iterations generated_modules generated_top inputs n initial) as [middle|] eqn:Prefix; [|discriminate Steps].
 apply (rf_nop_disables_after_four inputs middle result); [|exact Steps].
 rewrite (staged_iterations_hold_register inputs n initial middle 7750
 (proj2 (instruction_register_shape 7750 ltac:(vm_compute; reflexivity))) Prefix). exact Instruction.
Qed.
Print Assumptions rf_nop_disables_settled.
