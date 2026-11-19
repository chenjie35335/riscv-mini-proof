"""Locate shared load-data aliases; this map is evidence, not a Coq proof."""
from pathlib import Path
import json
import re
root = Path(__file__).resolve().parents[2]
base = root / 'formal/flat-low'
fir = (base / 'CoreSoc.lo.fir').read_text()
coq = (base / 'CoreSocModel.v').read_text()
names = {}
for fk, ck in [('node', 'Snode'), ('wire', 'Swire'), ('reg', 'Sreg')]:
    fs = re.findall(r'^\s*' + fk + r'\s+([^\s:]+)', fir, re.M)
    cs = re.findall(r'@' + ck + r' VarOrder.T (\d+) ', coq)
    assert len(fs) == len(cs), (fk, len(fs), len(cs))
    names.update(zip(map(int, cs), fs))
chain = [9222, 41, 82, 8079, 8080, 8201, 1477, 1522, 1712, 3347]
edges = []
for source, target in zip(chain, chain[1:]):
    node = f'@Snode VarOrder.T {target} (@Eref VarOrder.T (@Eid VarOrder.T {source}))'
    wire = f'@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {source}))'
    assert node in coq or wire in coq, (source, target)
    edges.append({'source': source, 'target': target, 'kind': 'node' if node in coq else 'wire'})
report = {
    'status': 'actual aliases checked textually; Coq proof and audit recorded separately',
    'configuration_evidence': 'flattened FIRRTL specCore read-data connection cites Checker.scala:107 (non-TLB branch)',
    'source_files': ['src/main/scala/mini/Datapath.scala', 'riscv-spec-core/src/main/scala/rvspeccore/checker/Checker.scala', 'riscv-spec-core/src/main/scala/rvspeccore/core/tool/LoadStore.scala'],
    'chain': [{'id': n, 'name': names[n]} for n in chain],
    'edges': edges,
    'consequence': 'For load result comparison, prove common raw-data aliases and address/type/sign-extension correspondence; no independent reference memory-state bisimulation is needed for this shared input.',
    'proof_artifacts': {'source': 'staged-integration/SharedLoadInput.v', 'theorems': ['shared_load_observed_inputs', 'shared_load_observed_result'], 'audit': 'staged-integration/SharedLoadStable.audit.log'},
    'remaining': [ 'effective address correspondence', 'load type/sign-extension correspondence', 'memory read/write request assertions remain separate obligations'],
}
(base / 'shared-load-input-map.json').write_text(json.dumps(report, indent=2) + '\n')
print('Checked', len(edges), 'actual aliases; shared DUT82/reference3347 raw input.')
