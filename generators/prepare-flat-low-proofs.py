#!/usr/bin/env python3
"""Audit flattened FIRRTL and isolate definitions without importing admitted lemmas."""
import hashlib
import json
from pathlib import Path
import re

root = Path(__file__).resolve().parents[2]
work = root / 'formal/flat-low'
source = (work / 'CoreSoc.v').read_text()
firrtl = (work / 'CoreSoc.lo.fir').read_text()
digest = hashlib.sha256(source.encode()).hexdigest()
baseline = work / 'CoreSoc.before-proof.sha256'
if baseline.exists():
    assert baseline.read_text().split()[0] == digest, 'CoreSoc.v changed!'
else:
    baseline.write_text(digest + '  formal/flat-low/CoreSoc.v\n')
assert len(re.findall(r'^  module ', firrtl, re.M)) == 1
assert not re.search(r'^\s+inst ', firrtl, re.M)
assert len(re.findall(r'^\s+assert\(', firrtl, re.M)) == 45
assert len(re.findall(r'^\s+assume\(', firrtl, re.M)) == 1
boundary = re.search(r'^Lemma generated_assert_0\b', source, re.M)
assert boundary is not None
model, tail = source[:boundary.start()], source[boundary.start():]
obligations = re.findall(r'Lemma (generated_assert_\d+) : (.*?)\nAdmitted\.', tail)
assert [name for name, _ in obligations] == [f'generated_assert_{i}' for i in range(45)]
assert not re.search(r'\b(?:Admitted|admit|Axiom|Parameter)\b', model)
(work / 'CoreSocModel.v').write_text(model)
(work / 'original_statements.json').write_text(json.dumps(obligations, indent=2) + '\n')
print('One module, zero instances, 45 assertions, one assumption; immutable model hash verified.')
print('Definitions isolated. This does not prove any assertion.')
