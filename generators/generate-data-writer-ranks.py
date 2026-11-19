"""Writer dependency ranks; RAM reads remain explicit semantic premises."""
import contextlib,io,json,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()): a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
ranks={};deps={};active=set(); memory_nodes={9187,9195,9203,9211}
def visit(n):
 if n in ranks:return ranks[n]
 assert n not in active, n
 active.add(n)
 entries=a['drivers'].get(n,[])
 if n in a['registers'] or not entries:
  assert n in a['registers'] or n==1, n
  deps[n]=[];ranks[n]=0
 else:
  assert len(entries)==1,(n,entries)
  e=entries[0]
  assert not e['aggregate_reference'] or n in memory_nodes,n
  deps[n]=[d for d in e['dependencies'] if not(n in memory_nodes and d==9178)]
  ranks[n]=1+max((visit(d) for d in deps[n]),default=0)
 active.remove(n);return ranks[n]
targets=[9230,9232,9233,9234]
for n in targets:visit(n)
rows=[dict(id=n,rank=ranks[n],dependencies=deps[n]) for n in sorted(ranks,key=lambda n:(ranks[n],n))]
report={'status':'rank_certificate_not_semantic_propagation','targets':{str(n):ranks[n] for n in targets},'nodes':rows,'register_boundaries':[n for n in ranks if n in a['registers']],'memory_read_nodes':sorted(memory_nodes),'memory_obligations':'For each RAM mux step: concrete RAM storage, reader enabled, concrete address. Bundle9178 is not treated as an ordinary scalar dependency. These semantic premises remain to be discharged from earlier address history.'}
def write(name,s):
 p=root/name
 if not p.exists() or p.read_text()!=s:p.write_text(s)
write('formal/flat-low/data-writer-dependency-ranks.json',json.dumps(report,indent=2)+'\n')
s='''Require Import X0DependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Definition data_writer_dependency_ranks : list (nat * (nat * list nat)) := [
'''
s+=';\n'.join(f"({r['id']}, ({r['rank']}, ["+';'.join(map(str,r['dependencies']))+']))' for r in rows)+'\n].\n'
s+='''Theorem data_writer_dependency_ranks_checked : dependency_ranks_valid data_writer_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions data_writer_dependency_ranks_checked.
'''
write('formal/flat-low/staged-integration/DataWriterDependencyRanks.v',s)
print(json.dumps({'nodes':len(rows),'registers':len(report['register_boundaries']),'targets':report['targets']}))
