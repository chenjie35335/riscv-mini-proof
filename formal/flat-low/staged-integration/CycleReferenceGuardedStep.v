Require Import CycleView MemoryPendingInvariant RFAluWritebackObserved RFArchitecturalWriteEffect RFWriteEffect ReferenceBankGuardedObserved ReferenceBankCycleInputs ReferenceBankCycleControls ReferenceBankSelectedData FormalLocalHistory.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem cycle_reference_guarded_effect_step memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_reference_bank before 0%nat=nseq 32 false ->
 ref_bank_guarded_controls(top_environment current) ->ref_write_selected_data_concrete(top_environment current) ->
 VM.find 3221(top_environment current)=Some(Gval(Fuint 5)(ref_write_destination(top_environment current))) ->
 rf_effect_normalize(cycle_pending_effect before)=rf_effect_normalize(ref_write_effect(top_environment current)) ->
 cycle_reference_effect_step before after.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After Zero Controls Data Destination Agreement.
 pose proof(reference_bank_guarded_effect_next memory inputs k current committed next(cv_reference_bank before)
 Observe Legal Run NextObserve Reset(cva_reference_bank _ _ Before)Zero Controls Data Destination)as Actual.
 intros index Bound.
 pose proof(proj2(Actual index Bound))as Value.
 pose proof(proj2(cva_reference_bank _ _ After index Bound))as ViewValue.
 rewrite ViewValue in Value. inversion Value.
 rewrite(rf_normalized_effect_agreement(cv_reference_bank before)_ _ Agreement index).
 congruence.
Qed.
