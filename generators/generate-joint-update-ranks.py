"""Check scalar update-cone ranks; load-register memory reads remain separate."""
import contextlib,io,json,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
registers=a['report']['joint_register_candidates'];targets=set()
for n in registers:
 if n not in (9220,9222):
  for e in a['drivers'][n]:targets.update(e['dependencies'])
ranks={};deps={};active=set()
def visit(n):
 if n in ranks:return ranks[n]
 assert n not in active,n
 active.add(n);es=a['drivers'].get(n,[])
 if n in a['registers'] or not es:
  assert n in registers or n==1,n
  deps[n]=[];ranks[n]=0
 else:
  assert len(es)==1 and not es[0]['aggregate_reference'],n
  deps[n]=es[0]['dependencies'];ranks[n]=1+max((visit(d) for d in deps[n]),default=0)
 active.remove(n);return ranks[n]
for n in sorted(targets):visit(n)
rows=[{'id':n,'rank':ranks[n],'dependencies':deps[n]} for n in sorted(ranks,key=lambda n:(ranks[n],n))]
def write(path,s):
 p=root/path
 if not p.exists() or p.read_text()!=s:p.write_text(s)
report={'status':'rank_certificate_only_not_semantic_proof','targets':{str(n):ranks[n] for n in sorted(targets)},'nodes':rows,'register_boundaries':sorted(n for n in ranks if n in a['registers']),'separate_memory_registers':[9220,9222],'remaining':'Prove scalar propagation, actual register commit transfer, memory-load steps and forced-reset/run induction.'}
write('formal/flat-low/joint-update-dependency-ranks.json',json.dumps(report,indent=2)+'\n')
s='Require Import X0DependencyRanks.\nFrom Coq Require Import List Arith Bool.\nImport ListNotations.\nDefinition joint_update_dependency_ranks : list (nat * (nat * list nat)) := [\n'
s+=';\n'.join(f"({r['id']}, ({r['rank']}, ["+';'.join(map(str,r['dependencies']))+']))' for r in rows)+'\n].\n'
s+='Lemma joint_update_dependency_ranks_checked : dependency_ranks_valid joint_update_dependency_ranks = true.\nProof. vm_compute. reflexivity. Qed.\nPrint Assumptions joint_update_dependency_ranks_checked.\n'
write('formal/flat-low/staged-integration/JointUpdateDependencyRanks.v',s)
print('nodes',len(rows),'targets',len(targets),'maximum rank',max(ranks.values()))
