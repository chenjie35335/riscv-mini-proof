from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];outdir=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
lanes=[(3480,3481,3482,3483,'Band',False),(3476,3477,3478,3479,'Bor',False),(3472,3473,3474,3475,'Bxor',False),(3525,2552,3526,3527,'Band',True),(3522,2552,3523,3524,'Bor',True),(3519,2552,3520,3521,'Bxor',True)]
ids=sorted(set([1290,1292,1294]+[n for row in lanes for n in row[:4] if n!=2552]));expr={};pos={};q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
from bisect import bisect_right
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 n=int(m[1])
 if n not in ids:continue
 d=1;j=m.end()
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 expr[n]=s[m.end():j-1];pos[n]=bisect_right(q,m.start())-1
out='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ids:out+=f'Definition rf_alu_expr_{n} := {expr[n]}.\n'
out+='Definition rf_alu_nodes := [::'+';'.join(f'({n},rf_alu_expr_{n})'for n in ids)+'].\n';prev=-1;offs=[]
for n in ids:offs.append(pos[n]-prev-1);prev=pos[n]
out+='Definition rf_alu_offsets := [::'+';'.join(str(i)+'%nat'for i in offs)+'].\nLemma rf_alu_positions :select_node_offsets rf_alu_offsets flat_statements=Some rf_alu_nodes.\nProof. vm_compute;reflexivity. Qed.\nLemma rf_alu_safety :selected_node_safety flat_memories flat_statements rf_alu_offsets flat_statements=true.\nProof. vm_compute;reflexivity. Qed.\nLocal Opaque flat_statements flat_memories generated_modules generated_top.\n'
out+='Definition rf_bitwise_op lane :=match Nat.modulo lane 3 with 0%nat=>Band|1%nat=>Bor|_=>Bxor end.\nDefinition rf_bitwise_word lane left right :=match Nat.modulo lane 3 with 0%nat=>andB left right|1%nat=>orB left right|_=>xorB left right end.\nDefinition rf_bitwise_source lane :=if Nat.ltb lane 3 then 2804 else 2552.\nDefinition rf_bitwise_output lane := nth 0 [::3483;3479;3475;3527;3524;3521] lane.\nDefinition rf_bitwise_dut lane :=nth 0 [::1290;1292;1294] (Nat.modulo lane 3).\n'
def ground(n,step,rew):
 return f'eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes {n} rf_alu_expr_{n});[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes {ids.index(n)}%nat);reflexivity| |exact {step}].\nintros site. cbn[rf_alu_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {rew}. reflexivity.\n'
out+='''Theorem rf_reference_bitwise_three lane invalid s0 s1 s2 s3 left right : (lane<6)%coq_nat ->
 VM.find 2209 s0=Some(Gval(Fuint 32)left) ->
 (forall old,old=s0 \/ old=s1 ->VM.find(rf_bitwise_source lane)old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_bitwise_output lane)s3=Some(Gval(Fuint 32)(rf_bitwise_word lane left right)).
Proof. intros Bound Left Right S1 S2 S3.
'''
for a,b,c,d,op,imm in lanes:
 out+='destruct lane as[|lane].\n{\n'
 out+=f'assert(A:VM.find {a} s1=Some(Gval(Fuint 32)left)).\n{{'+ground(a,'S1','Left')+'}\n'
 if imm:out+='pose proof(Right s1 (or_intror(Logic.eq_refl _)))as B. cbn[rf_bitwise_source]in B.\n'
 else:out+=f'assert(B:VM.find {b} s1=Some(Gval(Fuint 32)right)).\n{{pose proof(Right s0 (or_introl(Logic.eq_refl _)))as R. cbn[rf_bitwise_source]in R.\n'+ground(b,'S1','R')+'}\n'
 word={'Band':'andB','Bor':'orB','Bxor':'xorB'}[op]
 out+=f'assert(C:VM.find {c} s2=Some(Gval(Fuint 32)({word} left right))).\n{{'+ground(c,'S2','A B')+'}\n'+ground(d,'S3','C')+'}\n'
out+='lia. Qed.\n'
f=outdir/'RFALUData.v';marker='Theorem rf_dut_bitwise_step';manual=f.read_text().split(marker,1)[1] if f.exists() and marker in f.read_text() else None;f.write_text(out+(marker+manual if manual is not None else ''))
