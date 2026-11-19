Require Import CoreSocModel ComparisonNodes FormalFetchRegisterCommit InstructionMemoryRead FormalObservedInstructionRead FormalObservationCommit StagedFlatCircuitIteration FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma fetch_reference_reads_memory old current :
 eval_href_with_memory flat_memories fetch_register_reference old current =
 eval_memory_reader_data flat_memories 9176 0 old current.
Proof.
 unfold fetch_register_reference. cbn [eval_href_with_memory].
 unfold is_memory_data_port. rewrite instruction_memory_layout_exact. reflexivity.
Qed.
Local Opaque generated_modules generated_top.
Theorem observed_fetch_commit_concrete memory inputs k observed committed old_value address width :
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some committed ->
 VM.find 9220 (top_environment observed) = Some old_value ->
 type_of_val old_value = Gtyp (Fuint 32) ->
 read_memory_port_field (top_environment observed) 9176 0 0 = Some (Gval (Fuint width) address) ->
 exists word, VM.find 9220 (top_environment committed) = Some (Gval (Fuint 32) word).
Proof.
 intros Observe Run Old Typed Address.
 rewrite (observation_then_commit memory inputs k observed Observe) in Run.
 destruct (flat_iteration_projection _ observed true committed Run) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 rewrite Top in Old.
 destruct (fetch_register_formal_commit_source _ before before after old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 rewrite fetch_reference_reads_memory in Source.
 assert (SourceObserved : eval_memory_reader_data flat_memories 9176 0 (top_environment observed) (top_environment observed) = Some source).
 { rewrite Top. exact Source. }
 destruct (observed_instruction_read_concrete memory inputs k observed address width source Observe Address SourceObserved)
 as [bits Concrete]. subst source.
 cbn [adapt_hvalue_as_type] in Adapt. inversion Adapt; subst value.
 eexists. unfold top_environment. rewrite After. exact Value.
Qed.
Print Assumptions observed_fetch_commit_concrete.
