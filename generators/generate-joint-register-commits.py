"""Actual scalar register commit certificates, split into small build units."""
import contextlib,io,json,re,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text()
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
ids=[n for n in a['report']['joint_register_candidates'] if n not in (9220,9222)]
def term_at(start):
 depth=0
 for end in range(start,len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if depth==0:return model[start:end+1]
def args(expr,prefix):
 s=expr[len(prefix):-1].strip();out=[]
 while s:
  if s[0]=='(':
   depth=0
   for i,c in enumerate(s):
    depth+=(c=='(')-(c==')')
    if not depth:break
   out.append(s[:i+1]);s=s[i+1:].strip()
  else:
   v,_,s=s.partition(' ');out.append(v);s=s.strip()
 return out
header='''Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def write(n,s):
 f=p/n
 if not f.exists() or f.read_text()!=s:f.write_text(s)
units=[]
for batch in range(0,len(ids),8):
 unit=f'JointRegisterCommits{batch//8}';units.append(unit);out=header
 for n in ids[batch:batch+8]:
  d=re.search(r'\(@Sreg VarOrder.T '+str(n)+r' ',model);c=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) ',model);assert d and c
  reg=term_at(d.end());width=int(re.search(r'\(Fuint (\d+)\)',reg)[1]);e=a['drivers'][n][0];expr=e['expression']
  pos=lambda m:len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
  start,end=pos(d),pos(c);assert start<end
  name=f'joint_register_{n}'
  out+=f'''Definition {name}_reg := {reg}.
Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T {n} {name}_reg) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) joint_register_update_{n}) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {n} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_identity : register_identity_b {n} flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_commit inputs path old current result old_value :
 VM.find {n} old = Some old_value -> type_of_val old_value = Gtyp (Fuint {width}) ->
'''
  for dep in e['dependencies']:out+=f' (exists ground bits, VM.find {dep} old = Some (Gval ground bits)) ->\n'
  out+=f''' formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 exists word, size word = {width}%nat /\\ VM.find {n} result = Some (Gval (Fuint {width}) word).
Proof.
 intros Old Typed '''+' '.join(f'H{d}' for d in e['dependencies'])+' Step.\n'
  certs=f'{name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe'
  common=f'{start} flat_statements {name}_decl {name}_mid {name}_tail'
  if expr.startswith('(@Eref '):
   dep=e['dependencies'][0];out+=f''' destruct H{dep} as [ground [bits Source]].
 exact (concrete_register_direct_commit {common} {n} {dep} {name}_reg {width} ground bits old_value (formal_invalid_policy inputs path) flat_memories old current result
 {certs} {name}_identity Old Typed (Logic.eq_refl _) Source Step).
'''
  else:
   mux=expr.startswith('(@Emux ');assert mux or expr.startswith('(@Eprim_unop '),expr
   tag='mux' if mux else 'unary';terms=args(expr,'(@Emux VarOrder.T ' if mux else '(@Eprim_unop VarOrder.T ')
   out+=f''' eapply (concrete_register_{tag}_commit {common} {n} {name}_reg '''+' '.join(terms)+f''' inputs path flat_memories old current result old_value {width}
 {certs} Old Typed {name}_identity).
 - apply joint_register_ready_{n}; assumption.
 - exact Step.
'''
  out+='Qed.\n'
 out+=f'Print Assumptions joint_register_{n}_commit.\n';write(unit+'.v',out)
write('JointRegisterCommitCertificates.v','Require Export '+' '.join(units)+'.\n')
print('Generated68 commit certificates in',len(units),'batches:', ' '.join(units))
