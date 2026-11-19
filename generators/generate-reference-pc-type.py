"""Reference PC initialization and type preservation, using established register proofs."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
for old,new in [('FormalPrivilegeInitialization','ReferencePCInitialization'),('FormalPrivilegeType','ReferencePCType')]:
 text=(base/(old+'.v')).read_text()
 text=text.replace('FormalPrivilegeInitialization','ReferencePCInitialization').replace('FormalPrivilegeCommitSource','ReferencePCCommitSource')
 text=text.replace('privilege150','reference_pc7331').replace('privilege_150_formal_commit_source','reference_pc_formal_commit_source')
 text=re.sub(r'\b(?:150|2)\b',lambda m:'7331' if m[0]=='150' else '32',text)
 p=base/(new+'.v')
 if not p.exists() or p.read_text()!=text:p.write_text(text)
