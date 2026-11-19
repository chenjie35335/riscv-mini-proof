"""One schema for every actual reference RF rd selector, including nested selectors."""
from pathlib import Path
import re,bisect,json
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();ex={};pos={};qs=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 j=m.end();d=1
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 n=int(m[1]);ex[n]=s[m.end():j-1];pos[n]=bisect.bisect_right(qs,m.start())-1
refs=lambda n:list(map(int,re.findall(r'@Eid VarOrder.T (\d+)',ex[n])))
chain=[];n=3614
while n!=2176:chain.append(n);n=refs(n)[-1]
chain.reverse();rows=[]
for stage,g in enumerate(chain):
 r=refs(g);n=r[1];extra=0;depth=1
 if not ('(@Eprim_binop VarOrder.T (Bcomp Beq)' in ex[n] and refs(n)[0]==3221):
  extra=refs(n)[0];n=refs(n)[1];depth=2
 assert refs(n)[0]==3221,(stage,g,n)
 rows.append((n,refs(n)[1],depth,extra))
items=[]
for index in range(1,32):
 for stage,(base,data,depth,extra)in enumerate(rows):
  prev=2177-index if stage==0 else chain[stage-1]+80*(index-1)
  for slot in range(depth):
   node=3223+index if stage==0 else base+slot+80*(index-1)
   yes=data if slot==0 else node-1
   assert refs(node)==[3221 if slot==0 else extra,yes,prev],(index,stage,slot,refs(node))
   items.append((pos[node],index,stage,slot,node))
items.sort();prev=-1;offsets=[]
for position,*_ in items:offsets.append(position-prev-1);prev=position
out='''\n(* Generated selector schema: actual model nodes, checked by Coq. *)
Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
Definition rf_reference_write_rows : seq(nat*nat*nat*nat) := [::'''+ ';'.join(f'({b}%nat,{d}%nat,{depth}%nat,{extra}%nat)'for b,d,depth,extra in rows)+'''].
Definition rf_reference_write_row stage := nth(0%nat,0%nat,0%nat,0%nat)rf_reference_write_rows stage.
Definition rf_reference_write_depth stage := let '(_,_,depth,_):=rf_reference_write_row stage in depth.
Definition rf_reference_write_data stage : VarOrder.T := let '(_,data,_,_):=rf_reference_write_row stage in N.of_nat data.
Definition rf_reference_write_selector index stage slot : VarOrder.T :=
 if stage==0%nat then N.of_nat(3223+index)%nat else
 let '(base,_,_,_):=rf_reference_write_row stage in N.of_nat(base+slot+80*(index-1))%nat.
Definition rf_reference_write_prior index stage : VarOrder.T :=
 if stage==0%nat then N.of_nat(2177-index)%nat else rf_reference_chain_node index(stage-1).
Definition rf_reference_write_input index stage slot : VarOrder.T :=
 if slot==0%nat then rf_reference_write_data stage else rf_reference_write_selector index stage(slot-1).
Definition rf_reference_write_condition index stage slot := if slot==0%nat then rf_reference_entry_condition index else
 let '(_,_,_,guard):=rf_reference_write_row stage in @Eref VarOrder.T(@Eid VarOrder.T(N.of_nat guard)).
Definition rf_reference_write_expr index stage slot := @Emux VarOrder.T(rf_reference_write_condition index stage slot)
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_input index stage slot)))
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_prior index stage))).
Definition rf_reference_write_nodes : seq(VarOrder.T*hfexpr VarOrder.T) :=
 List.map(fun index=>(rf_reference_write_selector index 0 0,rf_reference_write_expr index 0 0))(List.seq 1 31) ++
 List.flat_map(fun index=>List.flat_map(fun stage=>List.map(fun slot=>(rf_reference_write_selector index stage slot,rf_reference_write_expr index stage slot))(List.seq 0(rf_reference_write_depth stage)))(List.seq 1 35))(List.seq 1 31).
Definition rf_reference_write_offsets : seq nat := [::'''+ ';'.join(f'{n}%nat'for n in offsets)+'''].
Lemma rf_reference_write_positions : select_node_offsets rf_reference_write_offsets flat_statements=Some rf_reference_write_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_write_safety : selected_node_safety flat_memories flat_statements rf_reference_write_offsets flat_statements=true.
Proof. vm_compute. reflexivity. Qed.
'''
file=p/'RFReferenceWriteEffect.v';old=file.read_text();marker='(* Generated selector schema: actual model nodes, checked by Coq. *)';endmarker='(* Reference effect semantic composition. *)';prefix=old.split(marker,1)[0];suffix=old.split(endmarker,1)[1]if endmarker in old else'\n';file.write_text(prefix+out+endmarker+suffix)
(root/'formal/flat-low/rf-reference-write-effect-schema.json').write_text(json.dumps({'selectors':len(items),'nonzero_registers':31,'opcode_stages':36,'rows':[{'selector_base':b,'data_source':d,'depth':depth,'permission_guard':extra,'guard':refs(chain[i])[0]}for i,(b,d,depth,extra)in enumerate(rows)]},indent=2)+'\n')
print(len(items),'actual rd selectors,',sum(d for _,_,d,_ in rows),'per nonzero register')
