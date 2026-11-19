"""Actual constant-zero paths for original interrupt-number assertion41."""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text();paths=json.loads((root/'formal/flat-low/interrupt-zero-frontier.json').read_text())['paths_from_comparison_operands'];entries={e['id']:e for path in paths for e in path}
header='''Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
pos=lambda m:len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
out=header+'Definition interrupt_zero : seq bool := nseq 32 false.\n'
for n,e in sorted(entries.items()):
 if e['kind']!='Snode':continue
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);start=pos(m);name=f'interrupt_{n}'
 out+=f'''Definition {name}_expr : hfexpr VarOrder.T := {e['expression']}.
Definition {name}_tail := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_zero invalid old current result :
'''
 if e['dependencies']:out+=f" VM.find {e['dependencies'][0]} old = Some (Gval (Fuint 32) interrupt_zero) ->\n"
 out+=f''' formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros '''+('Source ' if e['dependencies'] else '')+f'''Step.
 eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonregister| |reflexivity|exact Step].
 unfold {name}_expr. cbn [eval_hfexpr_with_memory eval_href_with_memory].
'''+(' exact Source.\n' if e['dependencies'] else ' reflexivity.\n')+'Qed.\n'
out+='Print Assumptions interrupt_8243_zero.\n'
def write(n,s):
 f=p/n
 if not f.exists() or f.read_text()!=s:f.write_text(s)
write('InterruptZeroNodes.v',out)
out='Require Import InterruptZeroNodes.\n'+header
for n,e in sorted(entries.items()):
 if e['kind']!='Sfcnct':continue
 source=e['dependencies'][0];d=re.search(r'\(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint (\d+)\)\)\)',model);assert d and d[1]=='32'
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) ',model);start,end=pos(d),pos(m);name=f'interrupt_{n}'
 out+=f'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {n} (Gtyp (Fuint 32))) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) (@Eref VarOrder.T (@Eid VarOrder.T {source}))) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {n} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_zero invalid old current result :
 VM.find {source} old = Some (Gval (Fuint 32) interrupt_zero) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Source Step.
 exact (declared_connection_value {start} flat_statements {name}_decl {name}_mid {name}_tail {n} {source} 32
 (Gval (Fuint 32) interrupt_zero) (Gval (Fuint 32) interrupt_zero) invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe {name}_nonregister
 (Logic.eq_refl _) Source (Logic.eq_refl _) Step).
Qed.
'''
out+='Print Assumptions interrupt_1858_zero.\n';write('InterruptZeroConnections.v',out)
print('Generated5 nodes and4 connections for assertion41.')
