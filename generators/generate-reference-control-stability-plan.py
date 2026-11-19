"""Parse actual flat statements once; plan the 6507/6780 stability cone."""
from pathlib import Path
from bisect import bisect_right
import re,json,hashlib
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
positions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
regs={int(n):int(w) for n,w in re.findall(r'\(@Sreg VarOrder.T (\d+) \(@mk_freg VarOrder.T \(Gtyp \(Fuint (\d+)\)\)',s)}
wires={int(n):int(w) for n,w in re.findall(r'\(@Swire VarOrder.T (\d+) \(Gtyp \(Fuint (\d+)\)\)',s)}
writers={};decls={}
pat=r'\(@(?P<kind>Snode|Sfcnct|Swire) VarOrder.T (?:\(@Eid VarOrder.T )?(?P<id>\d+)\)? '
for m in re.finditer(pat,s):
 n=int(m['id']);kind=m['kind'];pos=bisect_right(positions,m.start())-1
 if kind=='Swire':decls[n]=pos;continue
 depth=0
 for end in range(m.start(),len(s)):
  depth+=(s[end]=='(')-(s[end]==')')
  if depth==0:break
 expr=s[m.end():end];row=dict(id=n,kind=kind,expression=expr,position=pos,dependencies=sorted(set(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',expr)))))
 writers.setdefault(n,[]).append(row)
rows={};vis=set()
def visit(n):
 if n in rows:return rows[n]['rank']
 assert n not in vis,n
 if n in regs:rows[n]=dict(id=n,kind='register',width=regs[n],rank=0,dependencies=[]);return 0
 if n==1:rows[n]=dict(id=n,kind='reset',width=1,rank=0,dependencies=[]);return 0
 vis.add(n);assert len(writers.get(n,[]))==1,(n,writers.get(n));row=writers[n][0].copy()
 row['rank']=1+max((visit(d) for d in row['dependencies']),default=0)
 if row['kind']=='Sfcnct':row.update(width=wires[n],declaration_position=decls[n])
 rows[n]=row;vis.remove(n);return row['rank']
for n in [6507,6780]:visit(n)
report=dict(status='diagnostic_until_Coq_composition',model_sha256=hashlib.sha256(s.encode()).hexdigest(),targets={str(n):rows[n]['rank'] for n in [6507,6780]},nodes=sorted(rows.values(),key=lambda x:(x['rank'],x['id'])))
p=base/'reference-control-stability-plan.json';text=json.dumps(report,indent=2)+'\n'
if not p.exists() or p.read_text()!=text:p.write_text(text)
print('nodes',len(rows),'targets',report['targets'],'wires',sum(x['kind']=='Sfcnct' for x in rows.values()),'registers',sum(x['kind']=='register' for x in rows.values()))
print('wire expressions',sorted(set(re.sub(r'\d+','N',x['expression']) for x in rows.values() if x['kind']=='Sfcnct')))
print('constructors',sorted(set(re.findall(r'@E\w+', '\n'.join(x.get('expression','') for x in rows.values())))))
