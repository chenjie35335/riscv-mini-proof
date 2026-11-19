from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration';s=(base/'CoreSocModel.v').read_text()
q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
def expr(needle):
 a=s.index(needle)+len(needle);depth=0
 for b in range(a,len(s)):
  depth+=(s[b]=='(')-(s[b]==')')
  if depth==0:return s[a:b+1]
r='(@Sreg VarOrder.T 8040 ';u='(@Sfcnct VarOrder.T (@Eid VarOrder.T 8040) '
pos=bisect.bisect_right(q,s.index(r))-1;upd=bisect.bisect_right(q,s.index(u))-1
old=(proof/'JointRegisterCommits7.v').read_text();head=old[:old.index('Definition joint_register_7751_reg')]
a=old.index('Definition joint_register_7753_reg');b=old.index('Theorem joint_register_7753_commit',a)
body=old[a:b].replace('7753','8040').replace('8260',str(pos+1)).replace('8856',str(upd+1)).replace('595',str(upd-pos-1)).replace('8259',str(pos))
body=re.sub(r'Definition joint_register_8040_reg := .*?\.\n','Definition joint_register_8040_reg := '+expr(r)+'.\n',body)
(proof/'StoreWidthCommitCertificate.v').write_text(head+'Definition joint_register_update_8040 := '+expr(u)+'.\n'+body)
for suffix in ['TypeStep','Initialization','ReachableType','Commit','ResetCommit','CycleUpdate']:
 text=(proof/f'StoreMask{suffix}.v').read_text().replace('StoreMask','StoreWidth').replace('store_mask','store_width').replace('uint4','uint6').replace('7924','8040').replace('8430',str(pos))
 text=re.sub(r'\b80\b','8002',text)
 text=re.sub(r'\b4\b','6',text)
 (proof/f'StoreWidth{suffix}.v').write_text(text)
print('8040 positions',pos,upd,'update',expr(u))
