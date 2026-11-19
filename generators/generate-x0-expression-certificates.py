"""Generate readiness certificates for actual x0 cone node expressions.
These certify expressions, not statement membership or reachable invariants.
"""
import contextlib
import io
from pathlib import Path
import runpy

root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    audit = runpy.run_path(str(root / 'scripts/audit-x0-concrete-cone.py'))
pending, seen, nodes = [784, 785], set(), {}
while pending:
    node = pending.pop()
    if node in seen or node in audit['registers']:
        continue
    seen.add(node)
    entries = audit['drivers'].get(node, [])
    if len(entries) > 1:
        raise ValueError(f'Multiple drivers: {node}')
    for entry in entries:
        pending.extend(entry['dependencies'])
        if entry['kind'] == 'Snode':
            if entry['aggregate_reference'] or 'Evalidif' in entry['expression']:
                raise ValueError(f'Unsupported expression: {node}')
            nodes[node] = entry
out = '''Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Generated expressions; circuit membership and history propagation are separate obligations. *)
Ltac solve_x0_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
       | apply closure_mux; solve_x0_ready
       | apply closure_unary; solve_x0_ready
       | apply closure_binary; solve_x0_ready].
'''
for node, entry in sorted(nodes.items()):
    refs = entry['dependencies']
    out += f"Definition x0_concrete_expr_{node} : hfexpr VarOrder.T := {entry['expression']}.\n"
    out += f'Lemma x0_concrete_ready_{node} old :\n'
    for ref in refs:
        out += f' (exists g bits, VM.find {ref} old = Some (Gval g bits)) ->\n'
    out += f' concrete_expression_ready old x0_concrete_expr_{node}.\nProof.\n'
    for ref in refs:
        out += f' intros [g{ref} [b{ref} H{ref}]].\n'
    out += f' unfold x0_concrete_expr_{node}. solve_x0_ready.\nQed.\n'
out += f'Print Assumptions x0_concrete_ready_{max(nodes)}.\n'
path = root / 'formal/flat-low/staged-integration/X0ConcreteExpressionCertificates.v'
generated_path = path
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(f'Generated {len(nodes)} expression readiness certificates; no assertions discharged.')
