from pathlib import Path
import re
from bisect import bisect_right
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/CoreSocModel.v').read_text()
ids=[3067,3068,3069,3222,3496,3497,3498,3499,3500,3501,3502,3503,3504]
q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
expr={};pos={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 n=int(m[1])
 if n not in ids:continue
 d=1;j=m.end()
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 expr[n]=s[m.end():j-1];pos[n]=bisect_right(q,m.start())-1
out='''Require Import FormalLocalHistory ObservedJointRegisterConcrete CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ids:out+=f'Definition rf_arithmetic_expr_{n} := {expr[n]}.\n'
out+='Definition rf_arithmetic_nodes := [::'+';'.join(f'({n},rf_arithmetic_expr_{n})'for n in ids)+'].\n'
prev=-1;offs=[]
for n in ids:offs.append(pos[n]-prev-1);prev=pos[n]
out+='Definition rf_arithmetic_offsets := [::'+';'.join(str(i)+'%nat'for i in offs)+'].\nLemma rf_arithmetic_positions :select_node_offsets rf_arithmetic_offsets flat_statements=Some rf_arithmetic_nodes.\nProof. vm_compute;reflexivity. Qed.\nLemma rf_arithmetic_safety :selected_node_safety flat_memories flat_statements rf_arithmetic_offsets flat_statements=true.\nProof. vm_compute;reflexivity. Qed.\nLocal Opaque flat_statements flat_memories generated_modules generated_top.\n'
out+='Definition rf_add_left lane :=if Nat.eqb lane 2 then 2812 else 2209.\nDefinition rf_add_right lane :=if Nat.eqb lane 0 then 2804 else 2552.\nDefinition rf_add_output lane :=nth 0 [::3500;3222;3503]lane.\n'
def ground(n,step,rew):
 return f'eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes {n} rf_arithmetic_expr_{n});[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes {ids.index(n)}%nat);reflexivity| |exact {step}].\nintros site. cbn[rf_arithmetic_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {rew}. reflexivity.\n'
out+='''Theorem rf_reference_add_four lane invalid s0 s1 s2 s3 s4 left right :
 (lane<3)%coq_nat ->
 (forall old, old=s0 \\/ old=s1 ->VM.find(rf_add_left lane)old=Some(Gval(Fuint 32)left)) ->
 (forall old, old=s0 \\/ old=s1 ->VM.find(rf_add_right lane)old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find(rf_add_output lane)s4=Some(Gval(Fuint 32)(reference_load_address left right)).
Proof.
 intros Bound Left Right S1 S2 S3 S4.
 destruct lane as[|lane].
 {
 pose proof(Left s0(or_introl(Logic.eq_refl _)))as L.
 pose proof(Right s0(or_introl(Logic.eq_refl _)))as R.
 cbn[rf_add_left rf_add_right]in L,R.
'''
for n,w,r in [(3496,'left','L'),(3497,'right','R')]:
 out+=f'assert(V{n}:VM.find {n} s1=Some(Gval(Fuint 32){w})).\n{{'+ground(n,'S1',r)+'}\n'
out+='assert(Sum:VM.find 3498 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).\n{'+ground(3498,'S2','V3496 V3497')+'}\n'
out+='assert(Tail:VM.find 3499 s3=Some(Gval(Fuint 32)(reference_load_address left right))).\n{'+ground(3499,'S3','Sum')+'}\n'+ground(3500,'S4','Tail')+'}\n'
out+='destruct lane as[|lane].\n{\npose proof(Left s0(or_introl(Logic.eq_refl _)))as L.\npose proof(Right s1(or_intror(Logic.eq_refl _)))as R.\ncbn[rf_add_left rf_add_right]in L,R.\n'
out+='assert(A:VM.find 3067 s1=Some(Gval(Fuint 32)left)).\n{'+ground(3067,'S1','L')+'}\n'
out+='assert(Sum:VM.find 3068 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).\n{'+ground(3068,'S2','A R')+'}\n'
out+='assert(Tail:VM.find 3069 s3=Some(Gval(Fuint 32)(reference_load_address left right))).\n{'+ground(3069,'S3','Sum')+'}\n'+ground(3222,'S4','Tail')+'}\n'
out+='destruct lane as[|lane];[|lia].\npose proof(Left s1(or_intror(Logic.eq_refl _)))as L.\npose proof(Right s1(or_intror(Logic.eq_refl _)))as R.\ncbn[rf_add_left rf_add_right]in L,R.\n'
out+='assert(Sum:VM.find 3501 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).\n{'+ground(3501,'S2','L R')+'}\n'
out+='assert(Tail:VM.find 3502 s3=Some(Gval(Fuint 32)(reference_load_address left right))).\n{'+ground(3502,'S3','Sum')+'}\n'+ground(3503,'S4','Tail')+'Qed.\n'
f=root/'formal/flat-low/staged-integration/RFALUArithmeticData.v'
marker='Require Import FormalObservedHistory ReferenceControlStabilityHistory.'
manual=f.read_text().split(marker,1)[1] if f.exists() and marker in f.read_text() else None
f.write_text(out+(marker+manual if manual is not None else ''))
