"""Generate a shared pure reduction of reference exception safety conditions."""
from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
p=base/'staged-integration/ReferenceEventConditions.v'
s=p.read_text();s=s[:s.index('Proof.')]
sp=(base/'staged-integration/ReferenceEventSpine.v').read_text()
vals=re.findall(r' set v(\d+) := \((.*?)\)\.',sp)
entries=json.load((base/'event-proof-frontier.json').open())['reference_event_flag_spine'];by={e['node']:e for e in entries}
check={6332,6366,6390,6414,6438,6462,6486,6510,6533,6557,6582,6595,6623,6640,6672,6696,6701,6709,6778,6779,6780}
s+='Proof.\n unfold reference_event_safe. intro H.\n repeat match type of H with _ /\\ _ => destruct H as [? H] end.\n'
prev=[]
for ns,v in vals:
 n=int(ns);s+=f' set v{n} := ({v.replace("guards", "g")}).\n'
 if n not in check:continue
 deps=[];gs=set()
 def visit(m):
  deps.append(m)
  for d in by[m]['dependencies']:
   if d not in by:gs.add(d)
   elif d not in prev:visit(d)
 visit(n);deps=list(dict.fromkeys(deps))
 s+=f' assert (F{n} : v{n} = false).\n {{ unfold '+', '.join('v'+str(d) for d in deps)+'.\n'
 if prev:s+=' rewrite '+' '.join('?F'+str(d) for d in prev)+'.\n'
 s+=' destruct '+', '.join(f'(g {d}) eqn:G{n}_{d}' for d in sorted(gs))+'; simpl; try reflexivity; exfalso; first [congruence | match goal with H : _ -> _ |- _ => solve [pose proof (H Logic.eq_refl); congruence] | H : _ -> _ -> _ |- _ => solve [pose proof (H Logic.eq_refl Logic.eq_refl); congruence] end]. }\n' if gs else ' reflexivity. }\n'
 prev.append(n)
s+=' change (v6780 = false). exact F6780.\nQed.\n'
p.write_text(s)
