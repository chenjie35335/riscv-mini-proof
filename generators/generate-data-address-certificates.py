"""Generate address-cone rank and expression readiness certificates, not reachability proofs."""
import contextlib
import io
import json
import runpy
from pathlib import Path
root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    audit = runpy.run_path(str(root / 'scripts/audit-x0-concrete-cone.py'))
targets = [9186, 9194, 9202, 9210, 9221]
ranks, dependencies, nodes, visiting = {}, {}, {}, set()
def visit(node):
    if node in ranks:
        return ranks[node]
    if node in visiting:
        raise ValueError(f'Combinational cycle at {node}')
    visiting.add(node)
    entries = audit['drivers'].get(node, [])
    if node in audit['registers'] or not entries:
        ranks[node], dependencies[node] = 0, []
    else:
        if len(entries) != 1 or entries[0]['aggregate_reference']:
            raise ValueError(f'Unsupported driver at {node}')
        entry = entries[0]
        dependencies[node] = entry['dependencies']
        ranks[node] = 1 + max((visit(n) for n in dependencies[node]), default=0)
        if entry['kind'] == 'Snode':
            nodes[node] = entry
    visiting.remove(node)
    return ranks[node]
for node in targets:
    visit(node)
entries = sorted(ranks, key=lambda n: (ranks[n], n))
def write(relative, text):
    path = root / relative
    if not path.exists() or path.read_text() != text:
        path.write_text(text)
report = {'status': 'rank_and_readiness_certificates_not_reachability_proof',
          'targets': {str(n): ranks[n] for n in targets},
          'boundaries': [n for n in entries if ranks[n] == 0],
          'nodes': [{'id': n, 'rank': ranks[n], 'dependencies': dependencies[n]} for n in entries]}
write('formal/flat-low/data-address-dependency-ranks.json', json.dumps(report, indent=2) + '\n')
out = '''Require Import X0DependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Definition data_address_dependency_ranks : list (nat * (nat * list nat)) := [
'''
out += ';\n'.join(f'({n}, ({ranks[n]}, [' + ';'.join(map(str, dependencies[n])) + ']))' for n in entries) + '\n].\n'
out += '''Theorem data_address_dependency_ranks_checked : dependency_ranks_valid data_address_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions data_address_dependency_ranks_checked.
'''
write('formal/flat-low/staged-integration/DataAddressDependencyRanks.v', out)
out = '''Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_address_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
       | apply closure_mux; solve_address_ready
       | apply closure_unary; solve_address_ready
       | apply closure_binary; solve_address_ready].
'''
for node, entry in sorted(nodes.items()):
    refs = entry['dependencies']
    out += f"Definition address_expr_{node} : hfexpr VarOrder.T := {entry['expression']}.\n"
    out += f'Lemma address_ready_{node} old :\n'
    for ref in refs:
        ground = '(Fuint width)' if ref == 851 and 'Evalidif' in entry['expression'] else 'width'
        out += f' (exists width bits, VM.find {ref} old = Some (Gval {ground} bits)) ->\n'
    out += f' concrete_expression_ready old address_expr_{node}.\nProof.\n'
    for ref in refs:
        out += f' intros [w{ref} [b{ref} H{ref}]].\n'
    out += f' unfold address_expr_{node}.\n'
    if 'Evalidif' in entry['expression']:
        if node not in (884, 919):
            raise ValueError(f'Unsupported validif at {node}')
        out += ''' eapply closure_validif with (width := w851); [solve_address_ready|solve_address_ready|].
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H851. reflexivity.
'''
    else:
        out += ' solve_address_ready.\n'
    out += 'Qed.\n'
out += f'Print Assumptions address_ready_{max(nodes)}.\n'
write('formal/flat-low/staged-integration/DataAddressExpressionCertificates.v', out)
print(json.dumps({'nodes': len(entries), 'expressions': len(nodes), 'targets': report['targets'], 'boundaries': report['boundaries']}))
# One linear scan of the actual flattened statement sequence certifies membership.
import re
source = (root / 'formal/flat-low/CoreSocModel.v').read_text()
positions = []
for node in nodes:
    matches = list(re.finditer(r'\(@Snode VarOrder.T ' + str(node) + r' ', source))
    if len(matches) != 1:
        raise ValueError(f'Ambiguous node: {node}')
    position = len(re.findall(r'\(@Qcons VarOrder.T ', source[:matches[0].start()])) - 1
    positions.append((position, node))
positions.sort()
previous, offsets = -1, []
for position, node in positions:
    offsets.append(position - previous - 1)
    previous = position
out = '''Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate DataAddressExpressionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
'''
out += 'Definition data_address_node_offsets : seq nat := [::' + ';'.join(map(str, offsets)) + '].\n'
out += 'Definition data_address_expected_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::' + ';'.join(f'(N.of_nat {node}, address_expr_{node})' for _, node in positions) + '].\n'
out += '''Theorem data_address_actual_node_expressions :
 select_node_offsets data_address_node_offsets flat_statements = Some data_address_expected_nodes.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions data_address_actual_node_expressions.
'''
write('formal/flat-low/staged-integration/DataAddressPositionCertificate.v', out)
# UInt-valued results under the production symbolic invalid policy.
out = '''Require Import DataAddressExpressionCertificates ConcreteUIntOperations ConcreteUIntScalarExpressions ConcreteUIntValidIf.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_address_uint_ready :=
 repeat first [eapply uint_ready_ref; eassumption | apply uint_ready_const
 | apply uint_ready_unary; [reflexivity|] | apply uint_ready_binary].
'''
unsupported_uint_nodes = []
for node, entry in sorted(nodes.items()):
    if any(op in entry['expression'] for op in ('Ucvt', 'Utail', 'Ecast')):
        unsupported_uint_nodes.append(node)
        continue
    refs = entry['dependencies']
    out += f'Lemma address_uint_result_{node} inputs path site mm old result :\n'
    for ref in refs:
        out += f' (exists width bits, VM.find {ref} old = Some (Gval (Fuint width) bits)) ->\n'
    out += f' eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site mm address_expr_{node} old old = Some result ->\n concrete_uint_value result.\nProof.\n'
    for ref in refs:
        out += f' intros [w{ref} [b{ref} H{ref}]].\n'
    if 'Evalidif' in entry['expression']:
        out += f' unfold address_expr_{node}. eapply formal_uint_validif_concrete with (width := w851); [solve_address_uint_ready|solve_address_uint_ready|].\n'
        out += " unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite H851. reflexivity.\n"
    elif 'Emux' not in entry['expression']:
        out += f' apply formal_uint_scalar_concrete. unfold address_expr_{node}. solve_address_uint_ready.\n'
    else:
        out += f' intro Eval. unfold address_expr_{node} in Eval.\n'
        out += ' cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.\n'
        out += ' rewrite ' + ' '.join('?' + f'H{r}' for r in refs) + ' in Eval.\n'
        out += " unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.\n"
        out += ' rewrite ' + ' '.join('?' + f'H{r}' for r in refs) + ' in Eval.\n'
        out += ' cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval. cbn in Eval. cbn [eval_binop eval_binop_basic refine_boolean_result absorbing_bit] in Eval.\n'
        out += ' try unfold eval_binop, eval_binop_basic in Eval. try unfold refine_boolean_result, absorbing_bit in Eval. cbn in Eval.\n'
        out += ' repeat match type of Eval with context [if ?condition then _ else _] => destruct condition; cbn in Eval end;\n'
        out += ' cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;\n'
        out += ' inversion Eval; subst; do 2 eexists; reflexivity.\n'
    out += 'Qed.\n'
out += f'Print Assumptions address_uint_result_{max(nodes)}.\n'
write('formal/flat-low/staged-integration/DataAddressUIntCertificates.v', out)

write('formal/flat-low/data-address-uint-limitations.json', json.dumps({'status': 'conditional_UInt_reference_subset_not_full_cone', 'excluded_nodes': unsupported_uint_nodes, 'remaining': 'Mixed UInt/SInt intermediate values require ground-value propagation; these subset certificates cannot prove full address cone.'}, indent=2) + '\n')

# Reuse the single position/suffix scan for mixed-ground node propagation.
indices = {node: i for i, (_, node) in enumerate(positions)}
out = '''Require Import CoreSocModel ComparisonNodes SelectedNodeConcreteGroundOutput DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node, entry in sorted(nodes.items()):
    refs = entry['dependencies']
    out += f'Lemma data_address_node_output_{node} inputs path old current result :\n'
    for ref in refs:
        ground = '(Fuint ground)' if ref == 851 and 'Evalidif' in entry['expression'] else 'ground'
        out += f' (exists ground bits, VM.find {ref} old = Some (Gval {ground} bits)) ->\n'
    out += ' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->\n'
    out += f' exists ground bits, VM.find {node} result = Some (Gval ground bits).\nProof.\n'
    out += ' intros ' + ' '.join(f'H{r}' for r in refs) + ' Step.\n'
    out += f' eapply (selected_node_concrete_ground_output data_address_node_offsets flat_statements data_address_expected_nodes {node} address_expr_{node} inputs path flat_memories old current result).\n'
    out += ' - exact data_address_actual_node_expressions.\n - exact data_address_actual_nodes_safe.\n'
    out += f' - apply (@List.nth_error_In _ data_address_expected_nodes {indices[node]} ({node}, address_expr_{node})). vm_compute. reflexivity.\n'
    out += f' - apply address_ready_{node}; assumption.\n - exact Step.\nQed.\n'
out += f'Print Assumptions data_address_node_output_{max(nodes)}.\n'
write('formal/flat-low/staged-integration/DataAddressOutputCertificates.v', out)
