from pathlib import Path
import re
p=Path('formal/flat-low/staged-integration')
s=(p/'ReferenceZeroReadWidth.v').read_text();model=Path('formal/flat-low/CoreSocModel.v').read_text()
mapping={6520:6517,6531:6528,6555:6553,6580:6578,6598:6596,6621:6619,7112:7111,7187:7186,1711:1709,1521:1519}
s=re.sub('|'.join(map(str,mapping)),lambda m:str(mapping[int(m[0])]),s)
s=s.replace('reference_zero_read_width_history','reference_zero_read_valid_history').replace('zero_read_','zero_read_valid_')
for n in list(mapping.values())[:8]:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);d=0
 for j in range(m.start(),len(model)):
  d+=(model[j]=='(')-(model[j]==')')
  if not d:break
 s=re.sub(r'Definition zero_read_valid_expression_'+str(n)+r' :=.*?\.\n','Definition zero_read_valid_expression_'+str(n)+' :='+model[m.end():j]+'.\n',s)
s=s.replace('reference_zero_read_valid_valid_history','reference_zero_read_valid_history')
s=s.replace('(Fuint 6)','(Fuint 1)').replace('(zeros 6)','(zeros 1)').replace('false 6);','false 1);').replace('wire_certificate 1%nat','wire_certificate 0%nat')
(p/'ReferenceZeroReadValid.v').write_text(s)
