"""One batch of actual ImmGen nodes; reuse DataAddress location/safety certificates."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
src=(root/'formal/generators/generate-nop-kill-values.py').read_text();exec(src[src.index('def parse(s):'):src.index('values={7748:')])
text=(p/'DataAddressExpressionCertificates.v').read_text();expr={int(n):e for n,e in re.findall(r'Definition address_expr_(\d+) : hfexpr VarOrder.T := (.*)\.',text)}
ids=list(range(1309,1355));value={1306:('Fuint',32,'instruction'),1307:('Fuint',3,'[::true;false;false]')};rank={1306:0,1307:0};deps={}
def val(n):return f'load_imm_value {n} instruction'
def word(n):return f'(load_imm_word_{n} instruction)'
def calc(a):
 k=a[0]
 if k=='@Eref':
  n=int(a[2][2]);t,w,_=value[n];return t,w,word(n)
 if k=='@Econst':return a[2][0],int(a[2][1]),'[::'+';'.join(a[3])+']'
 if k=='@Ecast':
  t,w,b=calc(a[3]);return ('Fsint' if a[2]=='AsSInt' else 'Fuint'),w,b
 if k=='@Eprim_unop':
  t,w,b=calc(a[3]);op=a[2]
  if op=='Ucvt':return 'Fsint',w+1,f'(zext 1 {b})'
  hi,lo=map(int,op[1:]);return 'Fuint',hi-lo+1,f'(drop {lo} (take {hi+1} {b}))'
 if k=='@Eprim_binop':
  t,w,b=calc(a[3]);u,v,c=calc(a[4]);op=a[2]
  if op=='Bcat':return 'Fuint',w+v,f'({c} ++ {b})'
  if op=='Band':return 'Fuint',max(w,v),f'(andB {b} {c})'
  if op==['Bcomp','Beq']:
   code=a[3][3];return 'Fuint',1,'[::'+str(code==['true','false','false']).lower()+']'
 if k=='@Emux':
  t,w,b=calc(a[3]);u,v,c=calc(a[4]);cond=int(a[2][2][2]);chosen=b if cond==1342 else c
  return t,max(w,v),f'(sext_to {max(w,v)} (take {max(w,v)} {chosen}))'
 raise ValueError(a)
for n in ids:
 deps[n]=list(dict.fromkeys(map(int,re.findall(r'@Eid VarOrder.T (\d+)',expr[n]))));value[n]=calc(parse(expr[n]));rank[n]=1+max(rank[d]for d in deps[n])
head='''Require Import CoreSocModel ComparisonNodes FormalGroundNodeEquation SelectedNodeSafety DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates ConcreteDecodeOperations.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out=head
for n,(t,w,b) in value.items():out+=f'Definition load_imm_word_{n} (instruction:bits) := {b}.\n'
out+='Definition load_imm_value (node:nat) instruction : hvalue := match node with\n'+''.join(f'| {n}%nat =>Gval({t} {w}){word(n)}\n'for n,(t,w,b)in value.items())+'| _=>Gval(Fuint 1)[::false] end.\n'
out+='Definition load_imm_rank (node:nat) : nat := match node with\n'+''.join(f'| {n}%nat =>{r}%nat\n'for n,r in rank.items())+'| _=>0%nat end.\n'
out+='Definition load_imm_dependencies (node:nat) : list nat := match node with\n'+''.join(f'| {n}%nat =>[::'+ ';'.join(f'{d}%nat'for d in ds)+']\n'for n,ds in deps.items())+'| _=>nil end.\n'
out+='Definition load_imm_expr (index:nat) := nth (@Econst VarOrder.T(Fuint 1)[::false]) [::'+ ';'.join(f'address_expr_{n}'for n in ids)+'] index.\n'
out+='''Lemma load_imm_member index : (index<46)%coq_nat -> List.In(N.of_nat(1309+index)%nat,load_imm_expr index)data_address_expected_nodes.
Proof. intro Bound. apply(List.nth_error_In data_address_expected_nodes(76+index)%nat).
 do 46(destruct index as[|index];[vm_compute;reflexivity|]);lia. Qed.
Lemma load_imm_step index invalid old result instruction : (index<46)%coq_nat ->
 (forall dep,List.In dep(load_imm_dependencies(1309+index)%nat) -> VM.find(N.of_nat dep)old=Some(load_imm_value dep instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(1309+index)%nat)result=Some(load_imm_value(1309+index)%nat instruction).
Proof.
 intros Bound Values Step.
 destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe(load_imm_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
'''
for n in ids:
 out+=' destruct index as[|index].\n {\n'
 for d in deps[n]:out+=f' pose proof(Values {d}%nat ltac:(vm_compute;tauto))as H{d}.\n'
 out+=' eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].\n'
 out+=f' change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_{n} old old=Some(load_imm_value {n} instruction)).\n'
 out+=f' cbn [address_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].\n'
 out+=' unfold eval_type_of_expr;cbn [type_of_expr\' eval_type_of_ref].\n' if parse(expr[n])[0]=='@Emux' else ''
 out+=' rewrite '+' '.join(f'H{d}'for d in deps[n])+'.\n'
 out+=' cbn [load_imm_value].\n'
 if n==1340:out+=' unfold eval_binop. cbn [eval_binop_basic].\n'
 out+=' reflexivity. }\n'
out+=' lia. Qed.\n'
# Preserve manual composition below generator-owned block.
file=p/'LoadImmediateSemantics.v';marker='(* Semantic composition. *)';manual=file.read_text().split(marker,1)[1]if file.exists()and marker in file.read_text()else'\n'
file.write_text(out+marker+manual)
print('nodes',len(ids),'rank1354',rank[1354])
