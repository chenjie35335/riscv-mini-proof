"""Exact NOP decode propagation, checked against actual expressions by Coq."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
model=(base/'CoreSocModel.v').read_text();plan=json.loads((base/'early-bubble-stability-plan.json').read_text());rows={r['id']:r for r in plan['nodes']}
seen=set()
def visit(n):
 if n in seen:return
 seen.add(n)
 for d in rows[n]['dependencies']:visit(d)
visit(85)
visit(90)
order=sorted(seen,key=lambda n:(rows[n]['rank'],n))
registers=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+) ',model)))
assert seen&registers=={7748}
exprs={};wires={}
for n in order:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model)
 if m:
  depth=0
  for end in range(m.start(),len(model)):
   depth+=(model[end]=='(')-(model[end]==')')
   if not depth:break
  exprs[n]=model[m.end():end]
 elif n not in registers:
  m=re.search(r'\(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint (\d+)\)\)',model);assert m,n
  wires[n]=(rows[n]['dependencies'][0],int(m[1]))
def parse(s):
 toks=re.findall(r'\(|\)|\[::|\]|;|[^\s()\[\];]+',s);i=0
 def go():
  nonlocal i
  t=toks[i];i+=1
  if t in ('(','[::'):
   end=')' if t=='(' else ']';out=[]
   while toks[i]!=end:
    if toks[i]==';':i+=1;continue
    out.append(go())
   i+=1;return out
  return t
 a=go();assert i==len(toks);return a
values={7748:(32,0x13)}
def calc(a):
 k=a[0]
 if k=='@Eref':return values[int(a[2][2])]
 if k=='@Econst':
  assert a[2][0]=='Fuint';w=int(a[2][1]);bs=a[3];return w,sum((b=='true')<<i for i,b in enumerate(bs))
 if k=='@Eprim_binop':
  op=a[2];wa,va=calc(a[3]);wb,vb=calc(a[4])
  if op=='Band':return max(wa,wb),va&vb
  if op==['Bcomp','Beq']:return 1,int(va==vb)
  raise ValueError(op)
 if k=='@Emux':
  _,c=calc(a[2]);wa,va=calc(a[3]);wb,vb=calc(a[4]);return max(wa,wb),va if c else vb
 if k=='@Eprim_unop':
  op=a[2];w,v=calc(a[3]);assert op[0]=='Uextr';hi,lo=map(int,op[1:]);return hi-lo+1,(v>>lo)&((1<<(hi-lo+1))-1)
 raise ValueError(a)
for n in order:
 if n==7748:continue
 if n in exprs:values[n]=calc(parse(exprs[n]))
 else:
  src,w=wires[n];values[n]=(w,values[src][1]&((1<<w)-1))
assert values[85]==(1,0)
assert values[90]==(3,0)
def bits(w,v):return '[::'+';'.join('true' if (v>>i)&1 else 'false' for i in range(w))+']'
header='''Require Import CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalDeclaredConnection DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates JointUpdateNodePositions JointUpdateExpressionCertificates DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
dataids=list(map(int,re.findall(r'\(N.of_nat (\d+), address_expr_', (proof/'DataAddressPositionCertificate.v').read_text())))
jointids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (proof/'JointUpdateNodePositions.v').read_text())))
conns={name:(proof/(name+'.v')).read_text() for name in ['DataAddressConnectionCertificates','JointUpdateConnectionCertificates']}
out=header
for n in order:
 w,v=values[n];out+=f'Definition nop_kill_value_{n} := Gval (Fuint {w}) {bits(w,v)}.\n'
 if n==7748:continue
 deps=rows[n]['dependencies']
 out+=f'Theorem nop_kill_step_{n} invalid old current result :\n'
 for d in deps:out+=f' VM.find {d} old = Some nop_kill_value_{d} ->\n'
 out+=' formal_value_iter invalid flat_memories old false current flat_statements = Some result ->\n'+f' VM.find {n} result = Some nop_kill_value_{n}.\nProof.\n intros '+' '.join(f'H{d}' for d in deps)+' Step.\n'
 if n in exprs:
  if n in dataids:entries,offsets,positions,safety,expression,index='data_address_expected_nodes','data_address_node_offsets','data_address_actual_node_expressions','data_address_actual_nodes_safe',f'address_expr_{n}',dataids.index(n)
  else:
   assert n in jointids,n
   entries,offsets,positions,safety,expression,index='joint_update_expected_nodes','joint_update_node_offsets','joint_update_node_positions','joint_update_node_safety',f'joint_update_expr_{n}',jointids.index(n)
  out+=f''' assert (Member : List.In ({n},{expression}) {entries}).
 {{ apply (List.nth_error_In {entries} {index}%nat). vm_compute. reflexivity. }}
 destruct (selected_node_safe_position flat_memories flat_statements {offsets} flat_statements
 {entries} {n} {expression} {positions} {safety} Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [{expression} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
  for d in deps:out+=f' rewrite H{d}.\n'
  out+=' vm_compute. reflexivity.\n'
 else:
  src,width=wires[n];matches=[]
  for name,t in conns.items():matches.extend((m[1],int(m[2])) for m in re.finditer(r'Lemma (\w+)_position\s*:\s*straight_drop (\d+) flat_statements = Some \(@Qcons VarOrder.T \(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint '+str(width)+r'\)\)\)',t))
  assert len(matches)==1,(n,matches)
  p,pos=matches[0]
  out+=f''' apply (declared_connection_value {pos} flat_statements {p}_decl {p}_mid {p}_tail
 {n} {src} {width} nop_kill_value_{src} nop_kill_value_{n} invalid flat_memories old current result
 {p}_position {p}_split {p}_straight {p}_mid_safe {p}_tail_safe {p}_nonregister (Logic.eq_refl _) H{src});
 [vm_compute;reflexivity|exact Step].
'''
 out+='Qed.\n'
out+='Print Assumptions nop_kill_step_85.\nPrint Assumptions nop_kill_step_90.\n'
p=proof/'NopKillValues.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
(base/'nop-kill-values.json').write_text(json.dumps({'targets':{str(n):rows[n]['rank'] for n in [85,90]},'nodes':order,'values':{str(n):{'width':values[n][0],'unsigned':values[n][1]} for n in order},'status':'generated_constant_candidates_checked_by_Coq_steps'},indent=2)+'\n')
print('Generated',len(order)-1,'exact propagation lemmas, kill value',values[85])
