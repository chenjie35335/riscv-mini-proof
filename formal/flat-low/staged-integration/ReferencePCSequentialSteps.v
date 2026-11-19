Require Import CoreSocModel ComparisonNodes ReferencePCSequentialNodes ReferencePCSequentialValues ReferencePCUpdateNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ReferencePCNextConnections ReferencePCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma reference_pc_seq_mux_6804 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 6780 old = Some (Gval (Fuint 1) [::false]) -> VM.find 6507 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 6804 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_sequential_6804_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 6780 _ _ false base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_sequential_6804_value invalid old current result width _ Eval Step).
Qed.
Lemma reference_pc_seq_mux_6805 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) -> VM.find 6804 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 6805 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_sequential_6805_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 1707 _ _ true base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_sequential_6805_value invalid old current result width _ Eval Step).
Qed.
Lemma reference_pc_seq_mux_6810 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 6807 old = Some (Gval (Fuint 1) [::true]) -> VM.find 6809 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 6810 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_sequential_6810_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 6807 _ _ true base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_sequential_6810_value invalid old current result width _ Eval Step).
Qed.
Lemma reference_pc_seq_mux_7094 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 6780 old = Some (Gval (Fuint 1) [::false]) -> VM.find 6810 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7094 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_sequential_7094_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 6780 _ _ false base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_sequential_7094_value invalid old current result width _ Eval Step).
Qed.
Lemma reference_pc_seq_mux_7109 invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) -> VM.find 7094 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7109 result = Some value /\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct (reference_pc_update_7109_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 { eapply (reference_pc_seq_mux flat_memories old 1707 _ _ true base input value Ext Cond); [|exact Eval]. exact Input. }
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact (reference_pc_update_7109_value invalid old current result width _ Eval Step).
Qed.
Lemma reference_pc_seq_alias_6806 invalid old current result base input :
 reference_pc_seq_extension base input -> VM.find 6805 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6806 result = Some input.
Proof.
 intros [width [Width Value]] Input Step. subst input.
 apply (reference_pc_sequential_6806_value invalid old current result width _); [|exact Step].
 cbn [reference_pc_sequential_6806_expr eval_hfexpr_with_memory eval_href_with_memory]. exact Input.
Qed.
Lemma reference_pc_seq_zero_test invalid old current result input :
 reference_pc_seq_extension [::false] input -> VM.find 6806 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6807 result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros [width [Width Value]] Input Step. subst input.
 apply (reference_pc_sequential_6807_value invalid old current result 1 [::true]); [|exact Step].
 cbn [reference_pc_sequential_6807_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Input.
 change (eval_binop (Bcomp Beq) (Gval (Fuint width) (zext_to width [::false])) (Gval (Fuint 1) [::false]) = Some (Gval (Fuint 1) [::true])).
 unfold eval_binop, absorbing_bit, refine_boolean_result. cbn [eval_binop_basic]. rewrite reference_pc_seq_zero. repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.
Lemma reference_pc_seq_add invalid old current result pc :
 VM.find 2812 old = Some (Gval (Fuint 32) pc) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6808 result = Some (Gval (Fuint 33) (from_N 33 (to_N pc + 4))).
Proof.
 intros PC Step. apply (reference_pc_sequential_6808_value invalid old current result 33 _); [|exact Step].
 cbn [reference_pc_sequential_6808_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite PC. reflexivity.
Qed.
Lemma reference_pc_seq_tail invalid old current result pc :
 VM.find 6808 old = Some (Gval (Fuint 33) (from_N 33 (to_N pc + 4))) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 6809 result = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros PC Step. apply (reference_pc_sequential_6809_value invalid old current result 32 _); [|exact Step].
 cbn [reference_pc_sequential_6809_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite PC. reflexivity.
Qed.
