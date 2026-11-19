"""Reuse the existing ImmGen prefix; certify only its 13-node mode suffix."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
src=(root/'formal/generators/generate-nop-kill-values.py').read_text();exec(src[src.index('def parse(s):'):src.index('values={7748:')])
expr={int(n):e for n,e in re.findall(r'Definition address_expr_(\d+) : hfexpr VarOrder.T := (.*)\.',(p/'DataAddressExpressionCertificates.v').read_text())}
old=(p/'LoadImmediateSemantics.v').read_text();types={int(n):(t,int(w))for n,t,w in re.findall(r'\| (\d+)%nat =>Gval\((Fuint|Fsint) (\d+)\)',old)}
ids=list(range(1342,1355));modes=[1,2,5,4]
control=(root/'src/main/scala/mini/Control.scala').read_text()
assert modes == [int(re.search(r'val IMM_'+name+r' = (\d+)\.U',control).group(1)) for name in ['I','S','B','J']]
def word(n): return f'(dut_imm_mode_word_{n} mode instruction)' if n>=1342 else f'(load_imm_word_{n} instruction)'
def calc(a):
 k=a[0]
 if k=='@Eref':
  n=int(a[2][2]);t,w=types[n];return t,w,word(n)
 if k=='@Econst':return a[2][0],int(a[2][1]),'[::'+';'.join(a[3])+']'
 if k=='@Ecast':
  t,w,b=calc(a[3]);return ('Fsint' if a[2]=='AsSInt' else 'Fuint'),w,b
 if k=='@Eprim_binop' and a[2]==['Bcomp','Beq']:
  code=sum((v=='true')<<i for i,v in enumerate(a[3][3]))
  return 'Fuint',1,'[::nth false [::'+';'.join(str(code==m).lower()for m in modes)+'] mode]'
 if k=='@Emux':
  t,w,b=calc(a[3]);u,v,c=calc(a[4]);cond=int(a[2][2][2]);return t,max(w,v),f'(sext_to {max(w,v)} (take {max(w,v)} (if hd false {word(cond)} then {b} else {c})))'
 raise ValueError(a)
values={n:calc(parse(expr[n]))for n in ids}
out='''Require Import CoreSocModel ComparisonNodes LoadImmediateSemantics FormalGroundNodeEquation SelectedNodeSafety DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates ConcreteDecodeOperations.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Modes 0,1,2,3 denote I,S,B,J respectively. *)
Definition dut_imm_selector mode : bits := from_N 3 (nth 1 [::1;2;5;4] mode).
'''
for n,(t,w,b)in values.items():out+=f'Definition dut_imm_mode_word_{n} (mode:nat) (instruction:bits) := {b}.\n'
out+='Definition dut_imm_value mode (node:nat) instruction : hvalue := match node with\n| 1307%nat => Gval(Fuint 3)(dut_imm_selector mode)\n'+''.join(f'| {n}%nat =>Gval({t} {w}){word(n)}\n'for n,(t,w,b)in values.items())+'| _ =>load_imm_value node instruction end.\n'
out+='''Lemma dut_imm_prefix_value mode index instruction : (index<33)%coq_nat ->
 dut_imm_value mode (1309+index)%nat instruction = load_imm_value (1309+index)%nat instruction.
Proof. intro Bound;do 33(destruct index as[|index];[reflexivity|]);lia. Qed.
Lemma dut_imm_prefix_no_selector index : (index<33)%coq_nat ->
 ~ List.In 1307%nat (load_imm_dependencies(1309+index)%nat).
Proof. intro Bound;do 33(destruct index as[|index];[vm_compute;intuition discriminate|]);lia. Qed.
Lemma dut_imm_prefix_dependencies_below index : (index<33)%coq_nat ->
 List.forallb (fun dep => Nat.ltb dep 1342) (load_imm_dependencies(1309+index)%nat) = true.
Proof. intro Bound;do 33(destruct index as[|index];[vm_compute;reflexivity|]);lia. Qed.
Lemma dut_imm_prefix_dependency mode index instruction dep : (index<33)%coq_nat ->
 List.In dep(load_imm_dependencies(1309+index)%nat) -> dut_imm_value mode dep instruction = load_imm_value dep instruction.
Proof.
 intros Bound Member.
 destruct(load_imm_dependency_rank index dep ltac:(lia) Member)as[Root|[Root|[prior[Prior[Same Rank]]]]].
 - subst dep;reflexivity.
 - subst dep;exfalso;exact(dut_imm_prefix_no_selector index Bound Member).
 - pose proof(dut_imm_prefix_dependencies_below index Bound)as Below.
   rewrite List.forallb_forall in Below;specialize(Below dep Member);apply Nat.ltb_lt in Below.
   subst dep;apply dut_imm_prefix_value;change (Nat.add 1309 prior < 1342)%coq_nat in Below;lia.
Qed.
Lemma dut_imm_step mode index invalid old result instruction : (mode<4)%coq_nat -> (index<46)%coq_nat ->
 (forall dep,List.In dep(load_imm_dependencies(1309+index)%nat) -> VM.find(N.of_nat dep)old=Some(dut_imm_value mode dep instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(1309+index)%nat)result=Some(dut_imm_value mode (1309+index)%nat instruction).
Proof.
 intros Mode Bound Values Step.
 destruct (lt_dec index 33) as [Prefix|Suffix].
 - rewrite (dut_imm_prefix_value mode index instruction Prefix).
   apply (load_imm_step index invalid old result instruction Bound);[|exact Step].
   intros dep Member;specialize(Values dep Member);rewrite (dut_imm_prefix_dependency mode index instruction dep Prefix Member) in Values;exact Values.
 - destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe(load_imm_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
   do 33 (destruct index as [|index];[lia|]).
'''
for n in ids:
 ds=list(dict.fromkeys(map(int,re.findall(r'@Eid VarOrder.T (\d+)',expr[n]))))
 out+='   destruct index as[|index].\n   {\n'
 for d in ds:out+=f'    pose proof(Values {d}%nat ltac:(vm_compute;tauto))as H{d}.\n'
 out+='    eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].\n'
 out+=f'    change (eval_hfexpr_validif_policy (isolated_validif_policy invalid) (validif_raw_address [::] count 0 [::]) flat_memories address_expr_{n} old old=Some(dut_imm_value mode {n} instruction)).\n'
 out+=f'    cbn [address_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].\n'
 if parse(expr[n])[0]=='@Emux':out+='    unfold eval_type_of_expr;cbn [type_of_expr\' eval_type_of_ref].\n'
 out+='    rewrite '+' '.join(f'H{d}'for d in ds)+'.\n'
 out+='    destruct mode as [|[|[|[|mode]]]];try lia;reflexivity. }\n'
out+='   lia.\nQed.\n'
file=p/'DUTImmediateModes.v';marker='(* Shared mode composition. *)';manual=file.read_text().split(marker,1)[1]if file.exists()and marker in file.read_text()else'\n'
file.write_text(out+marker+manual)
print('reused prefix nodes: 33; new mode suffix nodes:',len(ids))
