"""Verify store-control column and specialize the shared pipeline proof schema."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
node_expr={int(n):x for n,x in re.findall(r'Definition writer_expr_(\d+) : hfexpr VarOrder.T := (.*)\.',(base/'staged-integration/DataWriterExpressionCertificates.v').read_text())}
values=[]
for n in range(8752,8703,-1):
 bits=re.findall(r'\[::([^]]*)\]',node_expr[n])[0];values.append(sum((b.strip()=='true')<<i for i,b in enumerate(bits.split(';'))))
control=(root/'src/main/scala/mini/Control.scala').read_text();constants={n:int(v) for n,v in re.findall(r'val (\w+) = (\d+)\.U',control)}
scala=[constants[f.split(',')[7].strip()] for _,f in re.findall(r'(\w+)\s*-> List\(([^\n]+)\)',control)];assert values==scala
ids=list(map(int,re.findall(r'\((\d+),writer_expr_', (base/'staged-integration/DataWriterNodePositions.v').read_text())))
s=(base/'staged-integration/LoadTypeCorrespondence.v').read_text().replace('load_type','store_type').replace('is_load','is_store').replace('nonload','nonstore').replace('decode_load','decode_store').replace('not_load','not_store').replace('load_guard','store_guard')
s=re.sub(r'Definition store_type_values .*?\n','Definition store_type_values : seq N := [::'+';'.join(map(str,values))+'].\n',s)
s=re.sub(r'Definition store_type_indices .*?\n','Definition store_type_indices : seq nat := [::'+';'.join(str(ids.index(8752-i))+'%nat' for i in range(49))+'].\n',s)
for a,b in [(8753,8704),(8801,8752),(8258,8257),(7755,7754),(7865,7864),(7872,7871)]:s=s.replace(str(a),str(b))
s=re.sub(r'(?<!\d)92(?!\d)','91',s);s=s.replace('_92','_91')
s=s.replace('Fuint 3)','Fuint 2)').replace('from_N 3','from_N 2').replace('= 3%nat','= 2%nat').replace('7754%nat,3%nat','7754%nat,2%nat').replace('7754 3','7754 2').replace('7754%nat 3%nat','7754%nat 2%nat').replace('joint_register_7754_reg 3','joint_register_7754_reg 2')
s=s.replace('[::20483;16387;8195;4099;3]','[::8227;4131;35]').replace('[::4;5;1;2;3]','[::1;2;3]').replace('[::14%nat;13%nat;12%nat;11%nat;10%nat]','[::17%nat;16%nat;15%nat]')
s=s.replace('(lane < 5)','(lane < 3)').replace('do 5 (destruct lane','do 3 (destruct lane').replace('do 5 (destruct index','do 3 (destruct index').replace('do 10 (destruct index','do 15 (destruct index').replace('(index < 10)','(index < 15)').replace('(14 < index)','(17 < index)').replace('(j < 10)','(j < 15)').replace('(14 < j)','(17 < j)')
s=s.replace('127 <> 3','127 <> 35').replace('127 = 3','127 = 35')
s=s.replace('joint_boundary_registers 60%nat','joint_boundary_registers 59%nat').replace('joint_update_expected_nodes 920%nat','joint_update_expected_nodes 919%nat').replace('joint_update_expected_nodes 927%nat','joint_update_expected_nodes 926%nat')
# Derive physical positions from the immutable flattened model, rather than guessing offsets.
pos=lambda text:bisect.bisect_right(q,model.index(text))-1
for target,source in [(8257,8752),(91,8257)]:
 d=pos(f'(@Swire VarOrder.T {target} ');c=pos(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source})))')
 s=re.sub(r'(Lemma store_type_wire_'+str(target)+r'_checked : declared_wire_check flat_memories flat_statements ).*?( = true\.)',rf'\g<1>{d}%nat {c-d-1}%nat {target} {source} 2%nat\2',s)
 s=re.sub(r'declared_wire_checked_value flat_memories flat_statements \d+%nat \d+%nat '+str(target)+' '+str(source)+r' 3',f'declared_wire_checked_value flat_memories flat_statements {d}%nat {c-d-1}%nat {target} {source} 2',s)
d=pos('(@Sreg VarOrder.T 7754 ');s=s.replace('rf_control_direct_commit_exact 8261','rf_control_direct_commit_exact '+str(d))
p=base/'staged-integration/StoreTypeCorrespondence.v';mark='(* Store instruction alignment. *)'
tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n'
p.write_text(s+mark+tail)
print('Verified49 store-control rows and actual wire/commit positions.')
