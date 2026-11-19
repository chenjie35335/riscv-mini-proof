from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
def position(needle):return bisect.bisect_right(q,model.index(needle))-1
mapping={1474:1478,1519:1523,7569:7582}
s=(base/'staged-integration/RequestEnableNormalized.v').read_text().replace('read_valid','write_valid')
for old,new in mapping.items():s=s.replace(str(old),str(new))
for old,new,decl,conn,source in [(1474,1478,1553,7408,8198),(1519,1523,1598,6138,1709)]:
 d=position(f'(@Swire VarOrder.T {new} ')
 needle=f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {new}) '
 c=position(needle)
 a=model.index(needle)+len(needle)
 m=re.match(r'\(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)',model[a:]);assert m
 s=s.replace(f'{decl} {conn} {new} {source} 1',f'{d} {c-d-1} {new} {m[1]} 1')
n=position('(@Snode VarOrder.T 7582 ')
s=s.replace('straight_drop 8039 ',f'straight_drop {n+1} ').replace('straight_drop 8038 ',f'straight_drop {n} ')
(base/'staged-integration/WriteEnableNormalized.v').write_text(s)
