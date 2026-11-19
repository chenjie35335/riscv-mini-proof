"""Actual control decode implication, sharing the 49 instruction-choice guards."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();ex={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 j=m.end();d=1
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 ex[int(m[1])]=s[m.end():j-1]
src=(root/'formal/generators/generate-nop-kill-values.py').read_text();exec(src[src.index('def parse(s):'):src.index('values={7748:')])
expr={n:parse(e) for n,e in ex.items()}
bits=lambda bs:'[::'+';'.join(bs)+']'
rows=[]
for k in range(49):
 kill,sel,en=[expr[n+k] for n in [8655,8802,8851]]
 guard=int(kill[2][2][2]);assert guard==8360-2*k
 assert int(sel[2][2][2])==guard==int(en[2][2][2])
 code=expr[guard][3];mask=expr[guard-1][4]
 assert expr[guard][2]==['Bcomp','Beq'] and expr[guard-1][2]=='Band'
 rows.append((guard,mask,code,kill[3][3][0],sel[3][3],en[3][3][0]))
ids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (p/'JointUpdateNodePositions.v').read_text())))
required=[n for n in range(8263,8361)]+[n for base in [8655,8802,8851] for n in range(base,base+49)]+[8998,8999]
dataids=list(map(int,re.findall(r'\(N.of_nat (\d+), address_expr_', (p/'DataAddressPositionCertificate.v').read_text())))
assert set(required)<=set(ids+dataids)
head='''Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates JointUpdateNodePositions JointUpdateExpressionCertificates JointBoundaryRegisters JointUpdateBoundaryHistory X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalGroundNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Record wbkill_value := WbkillValue { wbkill_kill : bool; wbkill_low : bool; wbkill_high : bool; wbkill_enable : bool }.
Record wbkill_row := WbkillRow { wbkill_mask : bits; wbkill_code : bits; wbkill_row_value : wbkill_value }.
Definition wbkill_default_value := WbkillValue false false false false.
Definition wbkill_default_row := WbkillRow [::] [::] wbkill_default_value.
Definition wbkill_rows : seq wbkill_row := [::
'''
out=head+';\n'.join(f'WbkillRow {bits(mask[3])} {bits(code[3])} (WbkillValue {kill} {sel[0]} {sel[1]} {en})' for _,mask,code,kill,sel,en in rows)+'].\n'
out+='''Definition wbkill_choice instruction row := to_N (wbkill_code row) == to_N (andB instruction (wbkill_mask row)).
Fixpoint wbkill_decode (stage : nat) instruction : wbkill_value :=
 match stage with
 | O => wbkill_default_value
 | S previous => let row := nth wbkill_default_row wbkill_rows previous in
   if wbkill_choice instruction row then wbkill_row_value row else wbkill_decode previous instruction
 end.
Definition wbkill_safe value := (wbkill_enable value && (wbkill_low value || wbkill_high value)) ==> wbkill_kill value.
Lemma wbkill_rows_safe index : (index < 49)%coq_nat -> wbkill_safe (wbkill_row_value (nth wbkill_default_row wbkill_rows index)) = true.
Proof. intro Bound.
'''
for _ in rows:out+=' destruct index as [|index]. { vm_compute; reflexivity. }\n'
out+=' lia. Qed.\n'
out+='''Lemma wbkill_decode_safe stage instruction : (stage <= 49)%coq_nat -> wbkill_safe (wbkill_decode stage instruction) = true.
Proof.
 induction stage as [|stage IH]; intro Bound; [reflexivity|].
 cbn [wbkill_decode]. destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows stage)).
 - apply wbkill_rows_safe. lia.
 - apply IH. lia.
Qed.
Lemma wbkill_and_value width left right :
 eval_binop Band (Gval (Fuint 32) left) (Gval (Fuint width) right) = Some (Gval (Fuint (maxn 32 width)) (andB left right)).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit Band (Gval (Fuint 32) left) (Gval (Fuint width) right)); reflexivity.
Qed.
Lemma wbkill_eq_value width code masked :
 eval_binop (Bcomp Beq) (Gval (Fuint width) code) (Gval (Fuint 32) masked) = Some (Gval (Fuint 1) [::to_N code == to_N masked]).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit (Bcomp Beq) (Gval (Fuint width) code) (Gval (Fuint 32) masked)); reflexivity.
Qed.
'''
wires={83:(7748,32),8249:(83,32),8251:(8998,1),85:(8251,1),8259:(8850,2),93:(8259,2),8260:(8999,1),94:(8260,1)}
pos=lambda at:s[:at].count('(@Qcons VarOrder.T ')-1
wireparams={}
for n,(source,width) in wires.items():
 m=re.search(r'\(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint '+str(width)+r'\)\)',s);assert m;count=pos(m.start())
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(source)+r'\)\)\)',s);assert m;distance=pos(m.start())-count-1;wireparams[n]=(count,distance)
 out+=f'Lemma wbkill_wire_{n}_checked : declared_wire_check flat_memories flat_statements {count}%nat {distance}%nat {n} {source} {width}%nat = true.\nProof. vm_compute. reflexivity. Qed.\n'
out+='''Lemma wbkill_instruction_member : List.In (7748%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 53%nat). vm_compute. reflexivity. Qed.
Theorem control_writeback_decode_history invalid history limit instruction :
 size instruction = 32%nat ->
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 85 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49 instruction)]) /\\
 VM.find 93 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49 instruction);wbkill_high (wbkill_decode 49 instruction)]) /\\
 VM.find 94 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49 instruction)]).
Proof.
 intros Size Initial Steps.
 assert (H7748 : forall time, (time <= limit)%coq_nat -> VM.find 7748 (history time) = Some (Gval (Fuint 32) instruction)).
 { intros time Upper. rewrite (joint_update_register_history_same invalid history limit 7748 32 wbkill_instruction_member Steps time Upper). exact Initial. }
'''
vals={7748:'(Gval (Fuint 32) instruction)',83:'(Gval (Fuint 32) instruction)',8249:'(Gval (Fuint 32) instruction)'};ranks={7748:0,83:1,8249:2};deps={83:[7748],8249:[83]};order=[83,8249];kind={}
for k,(guard,mask,code,*_) in enumerate(rows):
 vals[guard-1]=f'(Gval (Fuint 32) (andB instruction {bits(mask[3])}))';ranks[guard-1]=3;deps[guard-1]=[8249];kind[guard-1]='and'
 vals[guard]=f'(Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows {k}%nat)])';ranks[guard]=4;deps[guard]=[guard-1];kind[guard]='eq'
 order +=[guard-1,guard]
for stage in range(1,50):
 for base,field in [(8655,'kill'),(8802,'sel'),(8851,'enable')]:
  n=base+stage-1;value=f'[::wbkill_{field} (wbkill_decode {stage}%nat instruction)]' if field!='sel' else f'[::wbkill_low (wbkill_decode {stage}%nat instruction);wbkill_high (wbkill_decode {stage}%nat instruction)]'
  vals[n]=f'(Gval (Fuint {2 if field=="sel" else 1}) {value})';ranks[n]=4+stage;deps[n]=[8360-2*(stage-1)]+([n-1] if stage>1 else []);kind[n]=('mux',stage);order.append(n)
for n,source in [(8998,8703),(8999,8899)]:vals[n]=vals[source];ranks[n]=54;deps[n]=[source];kind[n]='extract';order.append(n)
for n in [8251,85,8259,93,8260,94]:
 source,width=wires[n];vals[n]=vals[source];ranks[n]=ranks[source]+1;deps[n]=[source];order.append(n)
for n in order:
 out+=f' assert (H{n} : forall time, ({ranks[n]} <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find {n} (history time) = Some {vals[n]}).\n {{ intros time Lower Upper. destruct time as [|time]; [lia|].\n'
 if n in wires:
  source,width=wires[n];count,distance=wireparams[n]
  out+=f'''  eapply (declared_wire_checked_value flat_memories flat_statements {count}%nat {distance}%nat {n} {source} {width}%nat {vals[source]} {vals[n]} invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_{n}_checked|apply H{source};lia| |apply Steps;lia].
'''
  if width==32:out+='  cbn [adapt_hvalue_as_type]. assert (Take : take 32 instruction = instruction). { apply take_oversize. rewrite Size. reflexivity. }\n  rewrite Take. unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.\n'
  else:out+='  reflexivity.\n'
 else:
  if n in ids:
   expression=f'joint_update_expr_{n}';entries='joint_update_expected_nodes';offsets='joint_update_node_offsets';positions='joint_update_node_positions';safety='joint_update_node_safety';entry_index=ids.index(n)
  else:
   expression=f'address_expr_{n}';entries='data_address_expected_nodes';offsets='data_address_node_offsets';positions='data_address_actual_node_expressions';safety='data_address_actual_nodes_safe';entry_index=dataids.index(n)
  out+=f'''  assert (Member : List.In ({n},{expression}) {entries}).
  {{ apply (List.nth_error_In {entries} {entry_index}%nat). vm_compute. reflexivity. }}
  destruct (selected_node_safe_position flat_memories flat_statements {offsets} flat_statements {entries} {n} {expression} {positions} {safety} Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [{expression} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
  for d in deps[n]:out+=f'  rewrite (H{d} time ltac:(lia) ltac:(lia)).\n'
  if kind[n]=='and':out+='  apply wbkill_and_value.\n'
  elif kind[n]=='eq':out+='  apply wbkill_eq_value.\n'
  elif kind[n]=='extract':out+='  reflexivity.\n'
  else:
   stage=kind[n][1]
   out+=f'''  change (wbkill_decode {stage}%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows {stage-1}%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows {stage-1}%nat) else wbkill_decode {stage-1}%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows {stage-1}%nat)); reflexivity.
'''
 out+=' }\n'
out+=' intros time Lower Upper. repeat split; [apply H85|apply H93|apply H94];lia.\nQed.\n'
out+='''Theorem control_writeback_kill_history invalid history limit instruction :
 size instruction = 32%nat ->
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 94 (history time) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 93 (history time) <> Some (Gval (Fuint 2) [::false;false]) ->
 VM.find 85 (history time) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Size Initial Steps time Lower Upper Enable NonAlu.
 destruct (control_writeback_decode_history invalid history limit instruction Size Initial Steps time Lower Upper) as [Kill [Sel En]].
 pose proof (wbkill_decode_safe 49 instruction ltac:(lia)) as Safe.
 destruct (wbkill_decode 49 instruction) as [kill low high enabled].
 destruct kill, low, high, enabled; cbn [wbkill_safe wbkill_kill wbkill_low wbkill_high wbkill_enable] in *; try congruence.
 all: try discriminate.
 Show.
Qed.
'''
(p/'ControlWritebackKill.v').write_text(out)
print('Generated',len(order),'local history statements and zero new node certificates')
