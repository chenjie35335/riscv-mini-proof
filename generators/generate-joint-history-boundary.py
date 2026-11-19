"""Check scalar-update rank-zero coverage and reuse register hold lemmas."""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';p=base/'staged-integration'
ids=[1]+json.loads((base/'x0-concrete-dependency-audit.json').read_text())['joint_register_candidates']
def write(n,s):
 f=p/n
 if not f.exists() or f.read_text()!=s:f.write_text(s)
s=(p/'DataAddressBoundaryCertificate.v').read_text().replace('DataAddressDependencyRanks','JointUpdateDependencyRanks').replace('data_address_','joint_update_')
s=re.sub(r'Definition joint_update_boundary_ids : list nat := \[.*?\]\.', 'Definition joint_update_boundary_ids : list nat := ['+';'.join(map(str,ids))+'].',s,count=1)
write('JointUpdateBoundaryCertificate.v',s)
s=(p/'DataAddressBoundaryHistory.v').read_text().replace('DataAddressDependencyRanks','JointUpdateDependencyRanks').replace('DataAddressBoundaryCertificate','JointUpdateBoundaryCertificate').replace('DataAddressBoundaryRegisters','JointBoundaryRegisters').replace('data_address_','joint_update_').replace('joint_update_boundary_register','joint_boundary_register')
write('JointUpdateBoundaryHistory.v',s)
