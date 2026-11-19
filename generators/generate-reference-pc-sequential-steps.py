from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration/ReferencePCSequentialSteps.v'
s='''Require Import CoreSocModel ComparisonNodes ReferencePCSequentialNodes ReferencePCSequentialValues ReferencePCUpdateNodes ExceptionPCPayloadNodes ExceptionPCPayloadConnections ReferencePCNextConnections ReferencePCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold FormalRFResetPropagation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
'''
for n,c,selected,bit in [(6804,6780,6507,'false'),(6805,1707,6804,'true'),(6810,6807,6809,'true'),(7094,6780,6810,'false'),(7109,1707,7094,'true')]:
 name=f'reference_pc_sequential_{n}' if n!=7109 else 'reference_pc_update_7109'
 s+=f'''Lemma reference_pc_seq_mux_{n} invalid old current result base input :
 reference_pc_seq_extension base input ->
 VM.find {c} old = Some (Gval (Fuint 1) [::{bit}]) -> VM.find {selected} old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find {n} result = Some value /\\ reference_pc_seq_extension base value.
Proof.
 intros Ext Cond Input Step.
 destruct ({name}_evaluation invalid old current result Step) as [value Eval].
 assert (Extended : reference_pc_seq_extension base value).
 {{ eapply (reference_pc_seq_mux flat_memories old {c} _ _ {bit} base input value Ext Cond); [|exact Eval]. exact Input. }}
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 exact ({name}_value invalid old current result width _ Eval Step).
Qed.
'''
s+='''Lemma reference_pc_seq_alias_6806 invalid old current result base input :
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
'''
p.write_text(s)
