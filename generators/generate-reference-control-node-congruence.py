from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration';plan=json.loads((base/'reference-control-stability-plan.json').read_text());nodes=sorted([r for r in plan['nodes'] if r['kind']=='Snode'],key=lambda r:r['position'])
def parse(s):
 ts=re.findall(r'\(|\)|\[::|\]|;|[^\s()\[\];]+',s);i=0
 def go():
  nonlocal i
  t=ts[i];i+=1
  if t in ('(','[::'):
   stop=')' if t=='(' else ']';a=[]
   while ts[i]!=stop:
    if ts[i]==';':i+=1;continue
    a.append(go())
   i+=1;return a
  return t
 a=go();assert i==len(ts);return a
asts={r['id']:parse(r['expression']) for r in nodes}
def deps(a):
 if a[0]=='@Eref':return {int(a[2][2])}
 if a[0]=='@Emux':return deps(a[3])|deps(a[4])
 if a[0]=='@Evalidif':return deps(a[3])
 return set()
def ready(a):
 k=a[0]
 if k=='@Eref':
  n=int(a[2][2]);return f'eapply rc_ref; [exact V{n}|exists G{n}; exact T{n}].\n'
 if k=='@Emux':return 'apply rc_mux.\n{ '+ready(a[3])+'}\n{ '+ready(a[4])+'}\n'
 if k=='@Evalidif':return 'apply rc_validif.\n'+ready(a[3])
 return 'apply '+{'@Econst':'rc_const','@Eprim_binop':'rc_binary','@Eprim_unop':'rc_unary','@Ecast':'rc_cast'}[k]+'.\n'
shape={r['id']:sorted(deps(asts[r['id']])) for r in nodes}
(base/'reference-control-shape-dependencies.json').write_text(json.dumps(shape,indent=2)+'\n')
header='''Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric SelectedNodeSafety.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for block in range(4):
 chunk=nodes[block*300:(block+1)*300];s=header+f'Require Import ReferenceControlNodeCertificates{block}.\n';cat=f'reference_control_{block}'
 for i,r in enumerate(chunk):
  n=r['id'];ds=shape[n];ex=f'reference_control_expr_{n}'
  premises=lambda env:''.join(f' (exists value ground, VM.find {d} {env} = Some value /\\ type_of_val value = Gtyp ground) ->\n' for d in ds)
  args=' '.join('H'+str(d) for d in ds)
  s+=f'Lemma reference_control_ready_{n} old :\n'+premises('old')+f' reference_control_ready old {ex}.\nProof.\n'
  if ds:s+=' intros '+args+'.\n'
  for d in ds:s+=f' destruct H{d} as [v{d} [G{d} [V{d} T{d}]]].\n'
  s+=f' unfold {ex}.\n'+ready(asts[n])+'Qed.\n'
  s+=f'''Lemma reference_control_member_{n} : List.In ({n},{ex}) {cat}_nodes.
Proof. apply (List.nth_error_In {cat}_nodes {i}%nat). vm_compute. reflexivity. Qed.
'''
  position=f''' destruct (selected_node_safe_position flat_memories flat_statements {cat}_offsets flat_statements
 {cat}_nodes {n} {ex} {cat}_positions {cat}_safety reference_control_member_{n}) as [count [tail [Position [Safe Nonreg]]]].
'''
  s+=f'Theorem reference_control_node_{n}_ground inputs path old current result :\n'+premises('old')+f''' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find {n} result = Some value /\\ type_of_val value = Gtyp ground.
Proof.
 intros {args} Step.
'''+position+f''' exact (reference_control_node_ground count tail {n} {ex} inputs path old current result Position Safe Nonreg (reference_control_ready_{n} old {args}) Step).
Qed.
'''
  s+=f'Theorem reference_control_node_{n}_congruent inputs path left right next_left next_right :\n'+premises('left')
  for d in r['dependencies']:s+=f' VM.find {d} left = VM.find {d} right ->\n'
  s+=f''' formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find {n} next_left = VM.find {n} next_right.
Proof.
 intros {args} {' '.join('E'+str(d) for d in r['dependencies'])} L R.
'''+position+f''' apply (reference_control_node_congruent count tail {n} {ex} inputs path left right next_left next_right Position Safe Nonreg (reference_control_ready_{n} left {args})); [|exact L|exact R].
 intro site. cbn [{ex} eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
  for d in r['dependencies']:s+=f' rewrite E{d}.\n'
  s+=' reflexivity.\nQed.\n'
 s+=f"Print Assumptions reference_control_node_{chunk[-1]['id']}_congruent.\n"
 p=proof/f'ReferenceControlNodeCongruence{block}.v'
 if not p.exists() or p.read_text()!=s:p.write_text(s)
print('generated',len(nodes),'ground outputs and congruences; shape deps on registers:',sorted({d for ds in shape.values() for d in ds}&{r['id'] for r in plan['nodes'] if r['kind']=='register'}))
