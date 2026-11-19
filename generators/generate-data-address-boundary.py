"""Check rank-zero register declarations and their combinational preservation."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[2]
p = root / 'formal/flat-low/staged-integration'
report = json.loads((root / 'formal/flat-low/data-address-dependency-ranks.json').read_text())
ids = report['boundaries']
model = (root / 'formal/flat-low/CoreSocModel.v').read_text()
registers = []
for node in ids:
    if node == 1: continue
    match = re.search(r'\(@Sreg VarOrder.T '+str(node)+r' \(@mk_freg VarOrder.T \(Gtyp \(Fuint (\d+)\)\)', model)
    assert match, node
    registers.append((node, int(match[1])))
def write(name, text):
    path = p / name
    if not path.exists() or path.read_text() != text: path.write_text(text)
s = (p / 'X0BoundaryRegisters.v').read_text().replace('x0_', 'data_address_')
s = re.sub(r' \[:: \(150,2\).*?\]\.', ' [:: '+ ';'.join(f'({n},{w})' for n,w in registers)+'].', s, count=1)
write('DataAddressBoundaryRegisters.v', s)
s = (p / 'X0BoundaryCertificate.v').read_text().replace('X0DependencyRanks', 'DataAddressDependencyRanks').replace('x0_', 'data_address_')
s = re.sub(r'Definition data_address_boundary_ids : list nat := \[.*?\]\.', 'Definition data_address_boundary_ids : list nat := ['+';'.join(map(str,ids))+'].', s, count=1)
write('DataAddressBoundaryCertificate.v', s)
s = (p / 'X0BoundaryHistory.v').read_text().replace('X0DependencyRanks','DataAddressDependencyRanks').replace('X0BoundaryCertificate','DataAddressBoundaryCertificate').replace('X0BoundaryRegisters','DataAddressBoundaryRegisters').replace('x0_', 'data_address_')
write('DataAddressBoundaryHistory.v', s)
print(f'Generated boundary certificates for {len(registers)} registers and reset.')

s = (p / 'X0BoundaryPreparation.v').read_text().replace('X0BoundaryRegisters', 'DataAddressBoundaryRegisters').replace('x0_', 'data_address_')
write('DataAddressBoundaryPreparation.v', s)
