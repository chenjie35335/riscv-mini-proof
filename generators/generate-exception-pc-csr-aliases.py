"""Actual reference CSR aliases needed by the exception PC selection cone."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
s=(base/'CoreSocModel.v').read_text()
t=(base/'staged-integration/ExceptionPCPayloadConnections.v').read_text()
header=t[:t.index('Definition exception_pc_121_decl')]
block=t[t.index('Definition exception_pc_121_decl'):t.index('Definition exception_pc_1749_decl')]
out=header
for n,source in [(1758,7340),(1760,7342),(1770,7352),(1783,7365)]:
 d=re.search(r'\(@Swire VarOrder.T '+str(n)+r' ',s);c=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\)',s)
 dp=len(re.findall(r'\(@Qcons VarOrder.T ',s[:d.start()]))-1
 cp=len(re.findall(r'\(@Qcons VarOrder.T ',s[:c.start()]))-1
 part=block
 for old,new in [('exception_pc_121',f'exception_pc_csr_{n}'),(' 7751 ',f' {source} '),(' 121 ',f' {n} '),(' 99 ',f' {dp+1} '),(' 98 ',f' {dp} '),(' 8789 ',f' {cp+1} '),(' 8689 ',f' {cp-dp-1} ')]:part=part.replace(old,new)
 part=re.sub(r"\b121\b",str(n),part)
 part=re.sub(r"\b7751\b",str(source),part)
 if n==1783:part=re.sub(r"\b32\b","8",part)
 out+=part
out+='Print Assumptions exception_pc_csr_1783_value.\n'
(base/'staged-integration/ExceptionPCCSRAliases.v').write_text(out)
