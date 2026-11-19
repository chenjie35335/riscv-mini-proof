"""Certify normalization of the actual assumption's Boolean cone."""
import re,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
entries={};pending=[9139]
while pending:
 n=pending.pop()
 if n in entries:continue
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);assert m
 depth=0
 for end in range(m.start(),len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if not depth:break
 expr=model[m.end():end];deps=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',expr)))
 leaf='(Bcomp Beq)' in expr
 assert leaf or expr.startswith('(@Eprim_binop VarOrder.T Bor ')
 entries[n]=dict(expression=expr,dependencies=deps,leaf=leaf,position=len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1)
 if not leaf:pending+=deps
out='''Require Import CoreSocModel ComparisonNodes FormalSuccessfulNode FormalTypedNodeEquation FormalTypedNodeFrames ScalarNodeFrames RegisterInvariants ComparisonConstantBitShape NormalizedBit NormalizedOr.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n,e in sorted(entries.items()):
 name=f'legal_bool_{n}';pos=e['position']
 out+=f'''Definition {name}_expr := {e['expression']}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonregister : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem {name}_normalized invalid old current result :
'''
 if not e['leaf']:
  for src in e['dependencies']:out+=f' (exists value, VM.find {src} old = Some value /\\ normalized_bit value) ->\n'
 out+=f''' formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find {n} result = Some value /\ normalized_bit value.
Proof.
'''
 if e['leaf']:
  src,=e['dependencies']
  side='left' if '(Bcomp Beq) (@Econst ' in e['expression'] else 'right'
  out+=f''' intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result {name}_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories {name}_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 {{ cbn [{name}_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find {src} old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_{side}_normalized; exact Eval. }}
'''
 else:
  a,b=e['dependencies']
  out+=f''' intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories {name}_expr old old = Some value).
 {{ cbn [{name}_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }}
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
'''
 out+=f''' exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
'''
rank={}
for n,e in sorted(entries.items()):rank[n]=1 if e['leaf'] else 1+max(rank[x] for x in e['dependencies'])
out+='Print Assumptions legal_bool_9139_normalized.\n'
p=base/'staged-integration/LegalBooleanCone.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
report=dict(status='certificates_generated_not_yet_compiled',root=9139,rank=rank[9139],nodes=[dict(id=n,rank=rank[n],**e) for n,e in sorted(entries.items())])
(base/'legal-boolean-cone.json').write_text(json.dumps(report,indent=2)+'\n')
print('Boolean nodes:',len(entries),'root rank:',rank[9139])
