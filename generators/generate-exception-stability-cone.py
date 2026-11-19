"""Dependency plan for source128; ranks remain diagnostic until Coq composition."""
import re,json,hashlib
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
registers=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+) ',model)))
entries={};visiting=set()
def visit(n):
 if n in visiting:raise ValueError(f'cycle:{n}')
 if n in entries:return entries[n]['rank']
 if n in registers:
  entries[n]=dict(id=n,kind='register',rank=0,dependencies=[]);return 0
 visiting.add(n)
 found=[]
 for kind,pat in [('Snode',rf'\(@Snode VarOrder.T {n} '),('Sfcnct',rf'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T {n}\) ')]:
  for m in re.finditer(pat,model):
   depth=0
   for end in range(m.start(),len(model)):
    depth+=(model[end]=='(')-(model[end]==')')
    if not depth:break
   found.append((kind,model[m.end():end]))
 assert len(found)==1,(n,found)
 kind,expr=found[0];deps=sorted(set(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',expr))))
 assert not any(x in expr for x in ['Evalidif','Esubfield','Esubindex','Esubaccess'])
 rank=1+max((visit(d) for d in deps),default=0)
 entries[n]=dict(id=n,kind=kind,expression=expr,dependencies=deps,rank=rank)
 visiting.remove(n);return rank
visit(128)
expected=(base/'staged-integration/X0ConcretePositionCertificate.v').read_text()
for e in entries.values():
 if e['kind']=='Snode':
  e['existing_x0_expression']=bool(re.search(r'\(N.of_nat '+str(e['id'])+r', x0_concrete_expr_',expected))
report=dict(status='diagnostic_dependency_plan',model_sha256=hashlib.sha256(model.encode()).hexdigest(),target=128,rank=entries[128]['rank'],registers=sorted(n for n,e in entries.items() if e['kind']=='register'),nodes=sorted(entries.values(),key=lambda e:(e['rank'],e['id'])))
(base/'exception-stability-cone.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(nodes=len(entries),rank=report['rank'],registers=report['registers'],missing_x0_nodes=[e['id'] for e in entries.values() if e['kind']=='Snode' and not e['existing_x0_expression']]),indent=2))
