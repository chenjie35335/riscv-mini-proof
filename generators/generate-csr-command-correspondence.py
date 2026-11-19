from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text()
values=[]
for n in range(8948,8899,-1):
 st=model.index(f'(@Snode VarOrder.T {n} ');chunk=model[st:model.index('(@Qcons',st)]
 bits=re.search(r'\[::([^]]*)\]',chunk)[1];values.append(sum((v.strip()=='true')<<i for i,v in enumerate(bits.split(';'))))
csr=(root/'src/main/scala/mini/CSR.scala').read_text();const={n:int(v) for n,v in re.findall(r'val (\w+) = (\d+)\.U',csr)}
control=(root/'src/main/scala/mini/Control.scala').read_text();scala=[const[fields.split(',')[11].strip().split('.')[-1]] for _,fields in re.findall(r'(\w+)\s*-> List\(([^\n]+)\)',control)]
assert values==scala
ids=list(map(int,re.findall(r'\((\d+),', (base/'staged-integration/JointUpdateNodePositions.v').read_text())))
source=(base/'staged-integration/LoadTypeCorrespondence.v').read_text()
header=source[:source.index('Definition load_type_values')]
proof=source[source.index('Definition load_type_row'):source.index('Definition load_type_lane_code')]
proof=proof.replace('load_type','csr_command').replace('8753','8900').replace('data_writer','joint_update')
out=header+'Definition csr_command_values : seq N := [::'+';'.join(map(str,values))+'].\n'
out+='Definition csr_command_indices : seq nat := [::'+';'.join(str(ids.index(8948-i))+'%nat' for i in range(49))+'].\n'
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
pos=lambda token:bisect.bisect_right(q,model.index(token))-1
for target,src,old in [(8261,8948,'9018%nat 749%nat 8258 8801'),(95,8261,'69%nat 9928%nat 92 8258')]:
 d=pos(f'(@Swire VarOrder.T {target} ');c=pos(f'(@Sfcnct VarOrder.T (@Eid VarOrder.T {target}) (@Eref VarOrder.T (@Eid VarOrder.T {src})))')
 proof=proof.replace(old,f'{d}%nat {c-d-1}%nat {target} {src}')
 out+=f"Lemma csr_command_wire_{target}_checked : declared_wire_check flat_memories flat_statements {d}%nat {c-d-1}%nat {target} {src} 3%nat = true.\nProof. vm_compute. reflexivity. Qed.\n"
proof=re.sub(r'\b8258\b','8261',proof)
proof=re.sub(r'\b8801\b','8948',proof)
proof=re.sub(r'\b92\b','95',proof)
proof=proof.replace('wire_92_','wire_95_').replace('wire_8258_','wire_8261_')
out+='Local Opaque flat_statements flat_memories generated_modules generated_top.\n'+proof
out+='''Lemma csr_command_ecall : csr_command_decode 115 49 = from_N 3 4.
Proof. vm_compute. reflexivity. Qed.
Lemma csr_command_ebreak : csr_command_decode 1048691 49 = from_N 3 4.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions csr_command_ecall.
Print Assumptions csr_command_ebreak.
'''
p=base/'staged-integration/CSRCommandCorrespondence.v';mark='(* CSR pipeline extension. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
