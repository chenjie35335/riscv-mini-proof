"""Certify direct scalar paths of original assertion 44, without changing the model."""
import json
import argparse
import re
from pathlib import Path
parser = argparse.ArgumentParser()
parser.add_argument('--payload', action='store_true')
parser.add_argument('--event', action='store_true')
parser.add_argument('--pc', action='store_true')
parser.add_argument('--pc-payload', action='store_true')
parser.add_argument('--pc-next', action='store_true')
parser.add_argument('--pc-reset', action='store_true')
args = parser.parse_args()
assert sum([args.payload, args.event, args.pc, args.pc_payload, args.pc_next, args.pc_reset]) <= 1
width = 1 if (args.event or args.pc_reset) else 32
root = Path(__file__).resolve().parents[2]
base = root / 'formal/flat-low'
model = (base / 'CoreSocModel.v').read_text()
item = next(x for x in json.loads((base / 'assertion-cone-audit.json').read_text())['items'] if x['assertion'] == (43 if args.pc else 44))
entries = {e['id']: e for key in ['implementation_path', 'reference_path'] for e in item[key]
           if re.fullmatch(r'\(@Eref VarOrder.T \(@Eid VarOrder.T \d+\)\)', e.get('expression', ''))}
if args.payload:
    entries = {}
    for ident, src, kind in [(1396,7750,'Sfcnct'), (1516,1396,'Sfcnct'), (1706,1516,'Sfcnct'), (1884,1883,'Snode')]:
        entries[ident] = dict(kind=kind, expression=f'(@Eref VarOrder.T (@Eid VarOrder.T {src}))', dependencies=[src])
if args.event:
    entries = {}
    for ident, src, kind in [(139,128,'Sfcnct'), (134,773,'Sfcnct'), (1469,8242,'Sfcnct'), (773,128,'Snode'), (8153,134,'Snode'), (8242,8153,'Snode')]:
        entries[ident] = dict(kind=kind, expression=f'(@Eref VarOrder.T (@Eid VarOrder.T {src}))', dependencies=[src])
if args.pc_payload:
    entries = {}
    for ident, src, kind in [(121,7751,'Sfcnct'), (1749,7331,'Sfcnct'), (2812,1749,'Snode')]:
        entries[ident] = dict(kind=kind, expression=f'(@Eref VarOrder.T (@Eid VarOrder.T {src}))', dependencies=[src])
if args.pc_next:
    entries = {1819: dict(kind='Sfcnct', expression='(@Eref VarOrder.T (@Eid VarOrder.T 7149))', dependencies=[7149])}
if args.pc_reset:
    entries = {1515: dict(kind='Sfcnct', expression='(@Eref VarOrder.T (@Eid VarOrder.T 1394))', dependencies=[1394])}
header = '''Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def position(match):
    return len(re.findall(r'\(@Qcons VarOrder.T ', model[:match.start()])) - 1
nodes, connections = header, header
for ident, e in sorted(entries.items()):
    src, = e['dependencies']
    prefix = 'exception_pc' if (args.pc or args.pc_payload or args.pc_next or args.pc_reset) else ('exception_event' if args.event else 'exception_instruction')
    name = f'{prefix}_{ident}'
    if e['kind'] == 'Snode':
        pos = position(re.search(r'\(@Snode VarOrder.T '+str(ident)+r' ', model))
        nodes += f'''Definition {name}_expr : hfexpr VarOrder.T := {e['expression']}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {ident} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {ident} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {ident} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_value invalid old current result bits :
 VM.find {src} old = Some (Gval (Fuint {width}) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {ident} result = Some (Gval (Fuint {width}) bits).
Proof.
 intros Source Step. eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonregister| |reflexivity|exact Step].
 unfold {name}_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory]. exact Source.
Qed.
'''
    else:
        decl = re.search(r'\(@Swire VarOrder.T '+str(ident)+r' \(Gtyp \(Fuint (\d+)\)\)\)', model)
        assert decl and decl[1] == str(width)
        pos = position(decl)
        end = position(re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(ident)+r'\) ', model))
        connections += f'''Definition {name}_decl := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-pos-1} {name}_decl.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {ident} (Gtyp (Fuint {width}))) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {ident}) (@Eref VarOrder.T (@Eid VarOrder.T {src}))) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {ident} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {ident} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {ident} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_value invalid old current result source value :
 VM.find {src} old = Some source ->
 adapt_hvalue_as_type source (Gtyp (Fuint {width})) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {ident} result = Some value.
Proof.
 intros Source Adapt Step.
 exact (declared_connection_value {pos} flat_statements {name}_decl {name}_mid {name}_tail
 {ident} {src} {width} source value invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe {name}_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
'''
for name, text in [('ExceptionInstructionNodes',nodes), ('ExceptionInstructionConnections',connections)]:
    matching = [n for n,e in entries.items() if (e['kind']=='Snode') == (name=='ExceptionInstructionNodes')]
    if not matching:
        continue
    last = max(matching)
    prefix = 'exception_pc' if (args.pc or args.pc_payload or args.pc_next or args.pc_reset) else ('exception_event' if args.event else 'exception_instruction')
    text += f'Print Assumptions {prefix}_{last}_value.\n'
    if args.payload:
        name = name.replace('ExceptionInstruction', 'ExceptionPayload')
    if args.event:
        name = name.replace('ExceptionInstruction', 'ExceptionEvent')
    if args.pc:
        name = name.replace('ExceptionInstruction', 'ExceptionPC')
    if args.pc_payload:
        name = name.replace('ExceptionInstruction', 'ExceptionPCPayload')
    if args.pc_next:
        name = name.replace('ExceptionInstruction', 'ReferencePCNext')
    if args.pc_reset:
        name = name.replace('ExceptionInstruction', 'ReferencePCReset')
    path = base / 'staged-integration' / (name+'.v')
    if not path.exists() or path.read_text()!=text:
        path.write_text(text)
print('Generated direct path certificates:',len(entries))
