"""Batch-certify all actual reference instruction mask/compare nodes."""
from pathlib import Path
import json,re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
rows=json.loads((base/'reference-instruction-coverage-map.json').read_text())['rows']
model=(base/'CoreSocModel.v').read_text();positions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
ids=sorted(n for r in rows for n in r[:2]);expr={};pos=[]
for n in ids:
 a=model.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');d=0
 for b in range(a,len(model)):
  d+=(model[b]=='(')-(model[b]==')')
  if d==0:break
 expr[n]=model[a:b+1];pos.append(bisect.bisect_right(positions,a)-1)
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
s=(base/'staged-integration/ReferenceMemoryRequest.v').read_text();s=s[:s.index('Lemma reference_memory_decode_load')].replace('reference_memory','reference_instruction').replace('(row < 8)','(row < 48)').replace('do 8 (','do 48 (')
a=s.index('Definition reference_instruction_nodes');b=s.index('Lemma reference_instruction_positions')
arrays='Definition reference_instruction_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := '+seq(f'({n},{expr[n]})' for n in ids)+'.\n'
arrays+='Definition reference_instruction_offsets := '+seq(str(x)+'%nat' for x in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'.\n'
for name,column,typ in [('guards',0,'VarOrder.T'),('codes',5,'N'),('code_widths',4,'nat'),('masks',3,'N'),('mask_widths',2,'nat')]:
 arrays+=f'Definition reference_instruction_{name} : seq {typ} := '+seq(str(r[column])+('%nat' if typ=='nat' else '') for r in rows)+'.\n'
s=s[:a]+arrays+s[b:]
a=s.index('Definition reference_instruction_mask_expression')
s=s[:a]+'''Definition reference_instruction_mask row := nth 0 reference_instruction_masks row.
Definition reference_instruction_mask_width row := nth 0%nat reference_instruction_mask_widths row.
'''+s[a:]
s=s.replace('Fuint 15','Fuint (reference_instruction_mask_width row)').replace('from_N 15 28799','from_N (reference_instruction_mask_width row) (reference_instruction_mask row)')
s=s.replace('N.land (to_N instruction) 28799','N.land (to_N instruction) (reference_instruction_mask row)')
s=s.replace('= reference_instruction_code row.','= reference_instruction_code row /\\\n to_N (from_N (reference_instruction_mask_width row) (reference_instruction_mask row)) = reference_instruction_mask row.')
s=s.replace('as [MC [GC Code]]','as [MC [GC [Code MaskValue]]]')
s=s.replace('Some (Gval (Fuint 32) (andB instruction','Some (Gval (Fuint (maxn 32 (reference_instruction_mask_width row))) (andB instruction')
s=s.replace(')) 32 15 (reference_instruction_code_width row)) Code', ')) 32 (reference_instruction_mask_width row) (reference_instruction_code_width row)) Code MaskValue')
a=s.index('Definition reference_instruction_nodes');b=s.index('Lemma reference_instruction_positions')
s=s[:a]+arrays+s[b:]
a=s.index(' intro Row. do 48');b=s.index('Qed.',a)
proof=' intro Row.\n'
for r in rows:
 proof+=' destruct row as [|row].\n { split.\n'
 proof+=f' - apply (List.nth_error_In reference_instruction_nodes {ids.index(r[1])}%nat);vm_compute;reflexivity.\n'
 proof+=' - split.\n'
 proof+=f' + apply (List.nth_error_In reference_instruction_nodes {ids.index(r[0])}%nat);vm_compute;reflexivity.\n'
 proof+=' + split;vm_compute;reflexivity. }\n'
proof+=' lia.\n'
s=s[:a]+proof+s[b:]
# Dynamic UInt width is identical on both sides after evaluating Band.
p=base/'staged-integration/ReferenceInstructionDecode.v';p.write_text(s)
