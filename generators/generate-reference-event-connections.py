"""Checked forward and observational rules for the reference event wires."""
import re
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
out='''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def position(m):return len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
for n,source in [(1857,7202),(1667,1857)]:
 decl=re.search(r'\(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint 1\)\)\)',model);assert decl
 connect=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(source)+r'\)\)\)',model);assert connect
 start,end=position(decl),position(connect);name=f'reference_event_connection_{n}'
 out+=fr'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {n} (Gtyp (Fuint 1))) {name}_decl).
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
Theorem {name}_observation invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists source_value value, VM.find {source} old = Some source_value /\
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value /\ VM.find {n} result = Some value.
Proof.
 intro Step. exact (declared_connection_observation {start} flat_statements {name}_decl {name}_mid {name}_tail
 {n} {source} 1 invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe {name}_nonregister
 (Logic.eq_refl _) Step).
Qed.
Theorem {name}_value invalid old current result source_value value :
 VM.find {source} old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint 1)) = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some value.
Proof.
 intros Source Adapt Step. exact (declared_connection_value {start} flat_statements {name}_decl {name}_mid {name}_tail
 {n} {source} 1 source_value value invalid flat_memories old current result
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe {name}_nonregister
 (Logic.eq_refl _) Source Adapt Step).
Qed.
'''
out+='Print Assumptions reference_event_connection_1667_observation.\n'
p=base/'staged-integration/ReferenceEventConnections.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
