"""Build ranks for the x0 combinational graph; register boundaries remain explicit."""
import contextlib
import io
import json
from pathlib import Path
import runpy
root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    audit = runpy.run_path(str(root / 'scripts/audit-x0-concrete-cone.py'))
rank, deps, visiting = {}, {}, set()
def visit(node):
    if node in rank:
        return rank[node]
    if node in visiting:
        raise ValueError(f'Combinational cycle at {node}')
    visiting.add(node)
    entries = audit['drivers'].get(node, [])
    if node in audit['registers'] or not entries:
        deps[node] = []
        rank[node] = 0
    else:
        if len(entries) != 1:
            raise ValueError(f'Multiple drivers: {node}')
        deps[node] = entries[0]['dependencies']
        rank[node] = 1 + max((visit(d) for d in deps[node]), default=0)
    visiting.remove(node)
    return rank[node]
for target in [784,785]: visit(target)
entries = sorted(rank, key=lambda n:(rank[n],n))
report = {'status':'rank_certificate_not_reachability_proof', 'targets':{str(n):rank[n] for n in [784,785]},
          'boundaries':[n for n in entries if rank[n]==0],
          'nodes':[{'id':n,'rank':rank[n],'dependencies':deps[n]} for n in entries]}
generated_path = root/'formal/flat-low/x0-dependency-ranks.json'
generated_text = json.dumps(report,indent=2)+'\n'
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
out = '''From Coq Require Import List Arith Bool.
Import ListNotations.
Fixpoint dependency_rank_lookup (node : nat) (table : list (nat * (nat * list nat))) : option nat :=
 match table with
 | [] => None
 | (id, (rank, _)) :: rest => if Nat.eqb node id then Some rank else dependency_rank_lookup node rest
 end.
Definition dependency_ranks_valid (table : list (nat * (nat * list nat))) : bool :=
 forallb (fun entry => forallb (fun source =>
   match dependency_rank_lookup source table with
   | Some source_rank => Nat.ltb source_rank (fst (snd entry))
   | None => false end) (snd (snd entry))) table.
'''
out += 'Definition x0_dependency_ranks : list (nat * (nat * list nat)) := [\n'
out += ';\n'.join(f'({n}, ({rank[n]}, ['+';'.join(map(str,deps[n]))+']))' for n in entries) + '\n].\n'
out += '''Theorem x0_dependency_ranks_checked : dependency_ranks_valid x0_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions x0_dependency_ranks_checked.
'''
generated_path = root/'formal/flat-low/staged-integration/X0DependencyRanks.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(json.dumps({'nodes':len(entries),'targets':report['targets'],'boundaries':report['boundaries']}))
