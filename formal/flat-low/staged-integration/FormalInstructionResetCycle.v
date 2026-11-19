Require Import CoreSocModel RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount ObservedArchitecturalRegisters FormalResetPreparation FormalCoreResetControl FormalInstructionResetConstants FormalInstructionWordsResetCommit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma instruction_register_shape id :
 id \in architectural_register_ids ->
 initial_register_safe id flat_statements /\ has_register id flat_statements = true.
Proof.
 intro Member. pose proof (allP architectural_register_structure id Member) as Shape.
 move/andP: Shape => [/andP [_ Safe] Present]. split; assumption.
Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem instruction_real_reset_cycle inputs previous old result ex ew :
 SVM.find nil previous = Some old ->
 VM.find 7748 old = Some ex -> type_of_val ex = Gtyp (Fuint 32) ->
 VM.find 7750 old = Some ew -> type_of_val ew = Gtyp (Fuint 32) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\
 VM.find 7748 env = Some (Gval (Fuint 32) instruction_nop) /\
 VM.find 7750 env = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Previous Ex ExType Ew EwType Reset Cycle.
 destruct (instruction_register_shape 7748 ltac:(vm_compute; reflexivity)) as [ExSafe ExPresent].
 destruct (instruction_register_shape 7750 ltac:(vm_compute; reflexivity)) as [EwSafe EwPresent].
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs))
 as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Steps; [|discriminate Cycle].
 pose proof (top_reset_prepared (Some previous) _ initial _ Reset Prepare) as PreparedReset.
 destruct (core_control_9259 inputs initial stable true PreparedReset Steps) as [control [Control CoreReset]].
 destruct (flat_iterations_last inputs 9258 initial stable Steps) as [penultimate [Prefix Last]].
 destruct (flat_iteration_projection _ penultimate false stable Last) as [before_last [after_last [BeforeLast [LocalLast AfterLast]]]].
 rewrite Control in AfterLast. inversion AfterLast; subst after_last.
 pose proof (instruction_reset_node_8158 _ before_last before_last control LocalLast) as ExConstant.
 pose proof (instruction_reset_node_8160 _ before_last before_last control LocalLast) as EwConstant.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 7748 ExPresent Steps) as ExHold.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 7750 EwPresent Steps) as EwHold.
 rewrite (staged_prepared_register_copies previous old _ initial 7748 (Logic.eq_refl _) (Logic.eq_refl _) ExSafe ExPresent Previous Prepare) Ex in ExHold.
 rewrite (staged_prepared_register_copies previous old _ initial 7750 (Logic.eq_refl _) (Logic.eq_refl _) EwSafe EwPresent Previous Prepare) Ew in EwHold.
 unfold staged_register_lookup in ExHold, EwHold. rewrite Control in ExHold, EwHold.
 destruct (flat_iteration_projection _ stable true result Cycle) as [before [after [Before [Commit After]]]].
 rewrite Control in Before. inversion Before; subst before.
 exists after. split; [exact After|]. split.
 - exact (instruction_7748_formal_reset_commit _ control control after ex instruction_nop ExHold ExType CoreReset ExConstant (Logic.eq_refl _) Commit).
 - exact (instruction_7750_formal_reset_commit _ control control after ew instruction_nop EwHold EwType CoreReset EwConstant (Logic.eq_refl _) Commit).
Qed.
Print Assumptions instruction_real_reset_cycle.
