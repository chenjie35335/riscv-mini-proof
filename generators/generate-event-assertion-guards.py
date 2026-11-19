from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];b=root/'formal/flat-low/staged-integration'
for n,delta in [(40,12),(42,4)]:
 for suffix in ['GuardNodes','Enable']:
  s=(b/f'Assertion43{suffix}.v').read_text()
  s=s.replace('Assertion43',f'Assertion{n}').replace('assertion43',f'assertion{n}')
  s=re.sub(r'\b(?:7741|7742|8210|8211|8212)\b',lambda m:str(int(m[0])-delta),s)
  s=re.sub(r'^Print Assumptions .*\n','',s,flags=re.M)
  (b/f'Assertion{n}{suffix}.v').write_text(s)
