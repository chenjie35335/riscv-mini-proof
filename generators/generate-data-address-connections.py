"""Certify direct address-cone connections against the unchanged flat model."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[2]
model = (root / 'formal/flat-low/CoreSocModel.v').read_text()
rank = json.loads((root / 'formal/flat-low/data-address-dependency-ranks.json').read_text())
connections = []
for entry in rank['nodes']:
    node = entry['id']
    if re.search(r'\(@Snode VarOrder.T ' + str(node) + r' ', model) or not entry['dependencies']:
        continue
    assert len(entry['dependencies']) == 1, entry
    source = entry['dependencies'][0]
    declaration = re.search(r'\(@Swire VarOrder.T ' + str(node) + r' \(Gtyp \(Fuint (\d+)\)\)\)', model)
    pattern = r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T ' + str(node) + r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T ' + str(source) + r'\)\)\)'
    matches = list(re.finditer(pattern, model))
    if node == 78:
        assert source == 7826 and not matches
        continue  # Unary Uextr connection is proved separately.
    assert declaration and len(matches) == 1, (node, source)
    position = lambda match: len(re.findall(r'\(@Qcons VarOrder.T ', model[:match.start()])) - 1
    start, end = position(declaration), position(matches[0])
    assert start < end
    connections.append((node, source, int(declaration[1]), start, end))
out = '''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConcreteConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for node, source, width, start, end in connections:
    name = f'data_address_connection_{node}'
    out += f'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {node} (Gtyp (Fuint {width}))) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {node}) (@Eref VarOrder.T (@Eid VarOrder.T {source}))) {name}_tail).
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
 exact (declared_connection_concrete {start} flat_statements {name}_decl {name}_mid {name}_tail
 {node} {source} {width} ground bits invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe
 {name}_nonregister (Logic.eq_refl _) Source Step).
Qed.
'''
out += f'Print Assumptions data_address_connection_{connections[-1][0]}_output.\n'
p = root / 'formal/flat-low/staged-integration/DataAddressConnectionCertificates.v'
if not p.exists() or p.read_text() != out:
    p.write_text(out)
print(f'Generated {len(connections)} direct connection certificates.')
# The remaining connection is a unary extraction, with a separate certificate.
node, source, width = 78, 7826, 32
declaration = re.search(r'\(@Swire VarOrder.T 78 \(Gtyp \(Fuint 32\)\)\)', model)
connection = re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T 78\) \(@Eprim_unop VarOrder.T \(Uextr 31 0\) \(@Eref VarOrder.T \(@Eid VarOrder.T 7826\)\)\)\)', model)
assert declaration and connection
start, end = position(declaration), position(connection)
# Reuse the declaration/suffix certificate schema; preserve the unary expression.
base = next(c for c in connections if c[0] == 37)
old_start, old_end = base[3:]
block = out[out.index('Definition data_address_connection_37_decl'):]
block = block[:block.index('Print Assumptions')]
block = block.replace('data_address_connection_37', 'data_address_connection_78')
block = block.replace('VM.find 78 old', 'VM.find 7826 old').replace('VM.find 37 result', 'VM.find 78 result')
block = block.replace('(@Eid VarOrder.T 37) (@Eref VarOrder.T (@Eid VarOrder.T 78))', '(@Eid VarOrder.T 78) (@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 7826)))')
block = block.replace('(@Swire VarOrder.T 37 ', '(@Swire VarOrder.T 78 ')
block = block.replace('flat_memories 37 ', 'flat_memories 78 ').replace('has_register 37 ', 'has_register 78 ')
block = block.replace(f'straight_drop {old_start+1} ', f'straight_drop {start+1} ').replace(f'straight_drop {old_end+1} ', f'straight_drop {end+1} ')
block = block.replace(f'take_statements {old_end-old_start-1} ', f'take_statements {end-start-1} ').replace(f'straight_drop {old_start} ', f'straight_drop {start} ')
block = block.replace(f'declared_connection_concrete {old_start} ', f'declared_unary_connection_concrete {start} ').replace(' 37 78 32 ground bits', ' 78 7826 (Uextr 31 0) 32 ground bits')
header = out[:out.index('Definition ')]
header = 'Require Import FormalDeclaredConcreteUnaryConnection.\nFrom firrtl Require Import Firrtl_with_implicit_widths.\n' + header
unary = header + block + 'Print Assumptions data_address_connection_78_output.\n'
p = root / 'formal/flat-low/staged-integration/DataAddressUnaryConnection.v'
if not p.exists() or p.read_text() != unary:
    p.write_text(unary)
