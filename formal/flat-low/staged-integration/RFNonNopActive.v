Require Import LoadPipelineClassification ReferenceIllegalObserved FormalInstructionResetConstants FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma rf_nonnop_reference_active memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->instruction<>instruction_nop ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Instruction NonNop.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 destruct bubble.
 - specialize(Nop(Logic.eq_refl true)). rewrite Instruction in Nop. exfalso;apply NonNop;inversion Nop;reflexivity.
 - exact(reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Bubble).
Qed.
