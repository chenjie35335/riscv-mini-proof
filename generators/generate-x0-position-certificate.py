"""Generate a single sequential scan certificate for x0 node expressions."""
import contextlib
import io
from pathlib import Path
import re
import runpy

root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    expressions = runpy.run_path(str(root / 'formal/generators/generate-x0-expression-certificates.py'))
source = (root / 'formal/flat-low/CoreSocModel.v').read_text()
positions = []
for node in expressions['nodes']:
    matches = list(re.finditer(r'\(@Snode VarOrder.T ' + str(node) + r' ', source))
    if len(matches) != 1:
        raise ValueError(f'Ambiguous node: {node}')
    pos = len(re.findall(r'\(@Qcons VarOrder.T ', source[:matches[0].start()])) - 1
    positions.append((pos, node))
positions.sort()
previous = -1
offsets = []
for pos, node in positions:
    offsets.append(pos - previous - 1)
    previous = pos
out = '''Require Import CoreSocModel ComparisonNodes ScalarNodeFrames X0ConcreteExpressionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
(* Offsets count from the tail of the previous selected statement. *)
Fixpoint select_node_offsets (offsets : seq nat) (stmts : @hfstmt_seq VarOrder.T)
 : option (seq (VarOrder.T * hfexpr VarOrder.T)) :=
 match offsets with
 | [::] => Some [::]
 | offset :: rest =>
   match straight_drop offset stmts with
   | Some (Qcons (Snode id expression) tail) =>
       match select_node_offsets rest tail with
       | Some entries => Some ((id, expression) :: entries)
       | None => None
       end
   | _ => None
   end
 end.
'''
out += 'Definition x0_node_offsets : seq nat := [::' + ';'.join(map(str, offsets)) + '].\n'
out += 'Definition x0_expected_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::' + ';'.join(f'(N.of_nat {n}, x0_concrete_expr_{n})' for _, n in positions) + '].\n'
out += '''Theorem x0_actual_node_expressions :
 select_node_offsets x0_node_offsets flat_statements = Some x0_expected_nodes.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions x0_actual_node_expressions.
'''
generated_path = root / 'formal/flat-low/staged-integration/X0ConcretePositionCertificate.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(f'Generated single-scan position certificate for {len(positions)} nodes.')
