from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
def expr(needle):
 a=s.index(needle)+len(needle);depth=0
 for b in range(a,len(s)):
  depth+=(s[b]=='(')-(s[b]==')')
  if depth==0:return s[a:b+1]
r='(@Sreg VarOrder.T 8028 ';u='(@Sfcnct VarOrder.T (@Eid VarOrder.T 8028) '
pos=bisect.bisect_right(q,s.index(r))-1;upd=bisect.bisect_right(q,s.index(u))-1
old=(base/'staged-integration/JointRegisterCommits7.v').read_text()
head=old[:old.index('Definition joint_register_7751_reg')]
a=old.index('Definition joint_register_7753_reg');b=old.index('Theorem joint_register_7753_commit',a)
body=old[a:b].replace('7753','8028').replace('8260',str(pos+1)).replace('8856',str(upd+1)).replace('595',str(upd-pos-1)).replace('8259',str(pos))
body=re.sub(r'Definition joint_register_8028_reg := .*?\.\n', 'Definition joint_register_8028_reg := '+expr(r)+'.\n', body)
body='Definition joint_register_update_8028 := '+expr(u)+'.\n'+body
(base/'staged-integration/StoreWriteValidCommitCertificate.v').write_text(head+body)
print('register/connection positions',pos,upd)
