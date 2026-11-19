"""Connect every x0 node certificate to its actual formal iteration output."""
import contextlib
import io
from pathlib import Path
import runpy
root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    data = runpy.run_path(str(root / 'formal/generators/generate-x0-position-certificate.py'))
nodes = data['expressions']['nodes']
indices = {node: i for i, (_, node) in enumerate(data['positions'])}
out = '''Require Import CoreSocModel ComparisonNodes SelectedNodeConcreteOutput X0ConcretePositionCertificate X0ConcreteExpressionCertificates X0UIntExpressionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node, entry in sorted(nodes.items()):
    refs = entry['dependencies']
    out += f'Lemma x0_node_output_{node} inputs path old current result :\n'
    for ref in refs:
        out += f' (exists width bits, VM.find {ref} old = Some (Gval (Fuint width) bits)) ->\n'
    out += ' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->\n'
    out += f' exists width bits, VM.find {node} result = Some (Gval (Fuint width) bits).\nProof.\n'
    out += ' intros ' + ' '.join(f'H{r}' for r in refs) + ' Step.\n'
    out += f' apply (x0_selected_node_concrete_output {node} x0_concrete_expr_{node} inputs path old current result).\n'
    out += f' - unfold x0_expected_nodes. do {indices[node]} right. left. reflexivity.\n'
    out += f' - apply x0_concrete_ready_{node}.\n'
    for ref in refs:
        out += f'   + destruct H{ref} as [w [b H]]. exists (Fuint w), b. exact H.\n'
    out += ' - intros site value Eval.\n'
    out += f'   destruct (x0_uint_result_{node} _ site flat_memories old value ' + ' '.join(f'H{r}' for r in refs) + ' Eval) as [w [b V]].\n'
    out += '   subst value. exists w. reflexivity.\n - exact Step.\nQed.\n'
out += 'Print Assumptions x0_node_output_7941.\n'
generated_path = root / 'formal/flat-low/staged-integration/X0ConcreteOutputCertificates.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(f'Generated {len(nodes)} actual node output theorems.')
