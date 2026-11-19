"""Check and certify coverage of legal instruction masks by actual reference decode."""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
s=(base/'staged-integration/ReferenceControlExpressions.v').read_text();e={int(n):x for n,x in re.findall(r'Definition reference_control_expr_(\d+) := (.*)\.',s)}
def literal(x):
 w,b=re.findall(r'\(Fuint (\d+)\) \[::([^]]*)\]',x)[0]
 return int(w),sum((v.strip()=='true')<<i for i,v in enumerate(b.split(';')))
rows=[]
for node in range(2993,3041):
 g=int(re.findall(r'Eid VarOrder.T (\d+)',e[node])[0]);m=int(re.findall(r'Eid VarOrder.T (\d+)',e[g])[0]);assert re.findall(r'Eid VarOrder.T (\d+)',e[m])==['1884']
 mw,mask=literal(e[m]);cw,code=literal(e[g]);rows.append([g,m,mw,mask,cw,code])
classes=json.loads((base/'legal-instruction-class-map.json').read_text())['rows']
indexes=[next(i for i,r in enumerate(rows) if (r[3],r[5])==(c[2],c[4])) for c in classes]
assert len(indexes)==37
out='''Require Import LegalInstructionClass.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
'''
out+='Definition reference_instruction_codes : seq (N*N) := [::'+ ';'.join(f'({r[3]},{r[5]})' for r in rows)+'].\n'
out+='''Theorem legal_reference_mask_coverage mask code :
 List.In (mask,code) legal_instruction_classes ->
 exists row, (row < 48)%coq_nat /\ seq.nth (0,0) reference_instruction_codes row = (mask,code).
Proof.
 intro Member. cbn [legal_instruction_classes List.In] in Member.
'''
for i in indexes:
 out+=f' destruct Member as [Equal|Member];[inversion Equal;subst;exists {i}%nat;split;[lia|reflexivity]|].\n'
out+=' contradiction.\nQed.\n'
out+='''Theorem classified_reference_decode instruction :
 legal_instruction_classified instruction ->
 exists row, (row < 48)%coq_nat /\\
 N.eqb (snd (seq.nth (0,0) reference_instruction_codes row))
 (N.land (to_N instruction) (fst (seq.nth (0,0) reference_instruction_codes row))) = true.
Proof.
 intros [mask [code [Member Match]]].
 destruct (legal_reference_mask_coverage mask code Member) as [row [Bound Row]].
 exists row;split;[exact Bound|]. rewrite Row. cbn. rewrite Match. apply N.eqb_refl.
Qed.
'''
(base/'staged-integration/ReferenceInstructionCoverage.v').write_text(out)
(base/'reference-instruction-coverage-map.json').write_text(json.dumps({'rows':rows,'legal_rows':indexes,'source':'actual reference decoder nodes2993..3040; mask source1884'},indent=2)+'\n')
