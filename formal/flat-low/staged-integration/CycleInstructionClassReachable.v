Require Import LegalInstructionClass ReferenceInstructionDecode LoadPipelineClassification LoadTypeCorrespondence
 ObservedJointRegisterConcrete FormalInstructionResetConstants CycleView CoreSocModel FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma legal_instruction_reference_row instruction : legal_instruction_classified instruction ->
 exists row,(row<37)%coq_nat /\N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros[mask[code[Member Match]]].
 assert(Classes:legal_instruction_classes=List.map(fun row=>(reference_instruction_mask row,reference_instruction_code row))(List.seq 0 37))by reflexivity.
 rewrite Classes in Member. apply List.in_map_iff in Member.
 destruct Member as[row[Pair Bound]]. apply List.in_seq in Bound.
 exists row. split;[lia|]. injection Pair as Mask Code. rewrite Mask Code. exact Match.
Qed.
Theorem observed_commit_instruction_reference_row memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 exists row,(row<37)%coq_nat /\N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros Observe Legal Reset Instruction.
 destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bubble[Bubble Nop]].
 destruct bubble.
 - specialize(Nop(Logic.eq_refl _)). rewrite Instruction in Nop;inversion Nop;subst instruction.
   exists 0%nat. split;[lia|vm_compute;reflexivity].
 - apply legal_instruction_reference_row.
   destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal load_type_instruction_member)as[word[Size Word]].
   rewrite Instruction in Word;inversion Word;subst word.
   exact(legal_active_commit_instruction_classified_observed memory inputs k observed instruction Observe Legal Reset Bubble Instruction Size).
Qed.
Theorem cycle_commit_instruction_reference_row memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)v ->
 exists row,(row<37)%coq_nat /\N.land(to_N(cv_commit_instruction v))(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros Observe Legal Reset View.
 exact(observed_commit_instruction_reference_row memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)).
Qed.
