"""Certify candidate joint-register declarations; does not certify reachability."""
import json
import re
from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
p=base/'staged-integration'
ids=json.loads((base/'x0-concrete-dependency-audit.json').read_text())['joint_register_candidates']
model=(base/'CoreSocModel.v').read_text()
entries=[]
for node in ids:
 m=re.search(r'\(@Sreg VarOrder.T '+str(node)+r' \(@mk_freg VarOrder.T \(Gtyp \(Fuint (\d+)\)\)',model)
 assert m,node
 entries.append((node,int(m[1])))
def write(name,s):
 dest=p/name
 if not dest.exists() or dest.read_text()!=s: dest.write_text(s)
s=(p/'DataWriterBoundaryRegisters.v').read_text().replace('data_writer_','joint_')
s=re.sub(r' \[:: .*?\]\.', ' [:: '+';'.join(f'({n},{w})' for n,w in entries)+'].',s,count=1)
write('JointBoundaryRegisters.v',s)
s='Require Import JointBoundaryRegisters DataWriterBoundaryRegisters X0BoundaryRegisters.\nFrom Coq Require Import List Arith Bool.\n'
template=(p/'DataWriterBoundaryIncludesAddress.v').read_text()
for short,source in [('writer','data_writer'),('x0','x0')]:
 t=template[template.index('Lemma '):].replace('data_writer_includes_address','joint_includes_'+short).replace('data_writer_boundary_registers','joint_boundary_registers').replace('data_address_boundary_registers',source+'_boundary_registers')
 s+=t
write('JointBoundaryIncludes.v',s)
print(f'Generated declarations and inclusion certificates for {len(entries)} registers.')
