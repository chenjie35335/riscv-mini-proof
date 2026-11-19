"""Shared stable-value interface for the existing 304-node immediate plan."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
p = root / 'formal/flat-low/staged-integration'
src = (p / 'ReferenceImmediateTypes.v').read_text()
ids = list(map(int, re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.', src).group(1).split(';')))
assert len(ids) == 304
out = '''Require Import CoreSocModel ComparisonNodes ReferenceImmediateTypes ReferenceLoadImmediate ReferenceRedirectSpine ReferenceControlStabilityHistory ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 SelectedNodeSafety.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_immediate_same_history i inputs path history limit reset time :
 (i < 304)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find (reference_immediate_node i) (history time) = VM.find (reference_immediate_node i) (history (S time)).
Proof.
 intros Bound Resets Steps Lower Upper.
'''
for node in ids:
    out += f' destruct i as [|i];[change (VM.find {node} (history time) = VM.find {node} (history (S time)));apply (reference_control_stable_{node}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
out += ''' lia.
Qed.
Theorem reference_immediate_value_history i inputs path history limit reset time width word :
 (i < 304)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (reference_immediate_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (reference_immediate_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 rewrite (reference_immediate_same_history i inputs path history limit reset time Bound Resets Steps Lower Upper).
 eapply (reference_redirect_ground_step (reference_immediate_offsets i) (reference_immediate_nodes i) _ (reference_immediate_expression i));
 [unfold reference_immediate_offsets,reference_immediate_nodes;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold reference_immediate_offsets;destruct (nth 2%nat reference_immediate_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]
 |apply reference_immediate_member;exact Bound|exact Eval|apply Steps;lia].
Qed.
'''
file = p / 'ReferenceBranchImmediate.v'
marker = '(* Branch and JAL composition. *)'
manual = file.read_text().split(marker, 1)[1] if file.exists() and marker in file.read_text() else '\n'
file.write_text(out + marker + manual)
print('reused immediate entries:', len(ids))
