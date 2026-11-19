"""Certify direct address-cone connections against the unchanged flat model."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[2]
model = (root / 'formal/flat-low/CoreSocModel.v').read_text()
rank = json.loads((root / 'formal/flat-low/data-writer-dependency-ranks.json').read_text())
old_nodes = {r['id'] for r in json.loads((root / 'formal/flat-low/data-address-dependency-ranks.json').read_text())['nodes']}
connections = []
for entry in rank['nodes']:
    node = entry['id']
    if node in old_nodes: continue
    if re.search(r'\(@Snode VarOrder.T ' + str(node) + r' ', model) or not entry['dependencies']:
        continue
    assert len(entry['dependencies']) == 1, entry
    source = entry['dependencies'][0]
    declaration = re.search(r'\(@Swire VarOrder.T ' + str(node) + r' \(Gtyp \(Fuint (\d+)\)\)\)', model)
    pattern = r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T ' + str(node) + r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T ' + str(source) + r'\)\)\)'
    matches = list(re.finditer(pattern, model))
    op = None
    if not matches:
        pattern = r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T ' + str(node) + r'\) \(@Eprim_unop VarOrder.T \(Uextr (\d+) (\d+)\) \(@Eref VarOrder.T \(@Eid VarOrder.T ' + str(source) + r'\)\)\)\)'
        matches = list(re.finditer(pattern, model))
        if matches: op = f'(Uextr {matches[0][1]} {matches[0][2]})'
    assert declaration and len(matches) == 1, (node, source)
    position = lambda match: len(re.findall(r'\(@Qcons VarOrder.T ', model[:match.start()])) - 1
    start, end = position(declaration), position(matches[0])
    assert start < end
    connections.append((node, source, int(declaration[1]), start, end, op))
out = '''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection FormalDeclaredConcreteUnaryConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for node, source, width, start, end, op in connections:
    rhs = f'(@Eref VarOrder.T (@Eid VarOrder.T {source}))'
    if op: rhs = f'(@Eprim_unop VarOrder.T {op} {rhs})'
    rule = 'declared_unary_connection_concrete' if op else 'declared_connection_concrete'
    op_arg = op + ' ' if op else ''
    name = f'data_writer_connection_{node}'
    out += f'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {node} (Gtyp (Fuint {width}))) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {node}) {rhs}) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {node} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {node} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {node} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_output invalid old current result :
 (exists ground bits, VM.find {source} old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists bits, VM.find {node} result = Some (Gval (Fuint {width}) bits).
Proof.
 intros [ground [bits Source]] Step.
 exact ({rule} {start} flat_statements {name}_decl {name}_mid {name}_tail
 {node} {source} {op_arg}{width} ground bits invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe
 {name}_nonregister (Logic.eq_refl _) Source Step).
Qed.
'''
out += f'Print Assumptions data_writer_connection_{connections[-1][0]}_output.\n'
p = root / 'formal/flat-low/staged-integration/DataWriterConnectionCertificates.v'
if not p.exists() or p.read_text() != out:
    p.write_text(out)
print(f'Generated {len(connections)} writer connection certificates.')
