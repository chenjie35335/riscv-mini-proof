"""Refresh the two tables in DUTRedirectDecode.v, preserving its generic proofs.

Cross-check Scala Control/Instructions against the fixed flattened model. These
checks guide generation; Coq's bounded node certificates establish correctness.
"""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / 'formal/flat-low/staged-integration'
model = (ROOT / 'formal/flat-low/CoreSocModel.v').read_text()
nodes = {}
for match in re.finditer(r'\(@Snode VarOrder.T (\d+) ', model):
    start, depth = match.start(), 0
    for end in range(start, len(model)):
        depth += (model[end] == '(') - (model[end] == ')')
        if depth == 0:
            nodes[int(match[1])] = model[start:end + 1]
            break

def constant(node):
    bits = re.search(r'\[::([^]]*)\]', nodes[node])[1]
    return sum((bit.strip() == 'true') << i for i, bit in enumerate(bits.split(';')))

rows = [(constant(8263 + 2*i), constant(8264 + 2*i),
         constant(8409-i), constant(8654-i)) for i in range(49)]
control = (ROOT / 'src/main/scala/mini/Control.scala').read_text()
patterns = dict(re.findall(r'def (\w+) = BitPat\("b([01?]+)"\)',
    (ROOT / 'src/main/scala/mini/Instructions.scala').read_text()))
constants = {name: int(value) for name, value in re.findall(r'val (\w+) = (\d+)\.U', control)}
scala_rows = []
for name, fields in re.findall(r'(\w+)\s*-> List\(([^\n]+)\)', control):
    fields = [field.strip() for field in fields.split(',')]
    pattern = patterns[name]
    mask = int(''.join('0' if bit == '?' else '1' for bit in pattern), 2)
    code = int(pattern.replace('?', '0'), 2)
    scala_rows.append((mask, code, constants[fields[0]], constants[fields[5]]))
assert scala_rows == rows, 'Scala and flattened redirect decode tables differ'
data_ids = list(map(int, re.findall(r'\(N.of_nat (\d+),', (BASE / 'DataAddressPositionCertificate.v').read_text())))
joint_ids = list(map(int, re.findall(r'\((\d+),joint_update_expr_', (BASE / 'JointUpdateNodePositions.v').read_text())))
fields = ['dd_mask', 'dd_code', 'dd_selector', 'dd_kind', 'dd_mask_width', 'dd_code_width',
          'dd_and_index', 'dd_eq_index', 'dd_selector_index', 'dd_kind_index']
certificates = []
for i, row in enumerate(rows):
    widths = [int(re.search(r'Fuint (\d+)', nodes[8263 + 2*i + j])[1]) for j in range(2)]
    values = list(row) + widths + [data_ids.index(8263+2*i), data_ids.index(8264+2*i),
                                    joint_ids.index(8409-i), joint_ids.index(8654-i)]
    certificates.append(' {| ' + '; '.join(f'{field} := {value}' + ('%nat' if j >= 4 else '')
        for j, (field, value) in enumerate(zip(fields, values))) + ' |}')
path = BASE / 'DUTRedirectDecode.v'
source = path.read_text()
source = re.sub(r'(Definition dut_decode_rows[^\n]*\[::\n).*?(\]\.)',
    lambda m: m[1] + ';\n'.join(' (' + ','.join(map(str, row)) + ')' for row in rows) + m[2], source, count=1, flags=re.S)
source = re.sub(r'(Definition dut_decode_certificate_rows[^\n]*\[::\n).*?( \]\.)',
    lambda m: m[1] + ';\n'.join(certificates) + '\n' + m[2], source, count=1, flags=re.S)
if source != path.read_text():
    path.write_text(source)
print('Verified 49 Scala/flattened rows; refreshed two Coq certificate tables.')
