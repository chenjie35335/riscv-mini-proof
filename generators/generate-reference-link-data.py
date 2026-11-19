"""Extract six actual JAL/JALR return-address nodes from the flat model."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration';src=(base/'CoreSocModel.v').read_text();qs=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',src)]
ids=list(range(3444,3450));expr={};pos=[]
for n in ids:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+' ',src);a=m.end();depth=0
 for b in range(a,len(src)):
  depth+=(src[b]=='(')-(src[b]==')')
  if not depth:break
 expr[n]=src[a:b+1];pos.append(bisect.bisect_right(qs,a)-1)
s='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferencePCSequentialValues ExceptionPCPayloadNodes ExceptionPCPayloadConnections ExceptionPCSourceRegisters FormalRFResetPropagation FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ids:s+=f'Definition rf_link_expr_{n} := {expr[n]}.\n'
s+='Definition rf_link_nodes := [::'+';'.join(f'({n},rf_link_expr_{n})'for n in ids)+'].\n'
s+='Definition rf_link_offsets := [::'+';'.join(str(x)+'%nat'for x in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])])+'].\n'
s+='''Lemma rf_link_positions :select_node_offsets rf_link_offsets flat_statements=Some rf_link_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_link_safety :selected_node_safety flat_memories flat_statements rf_link_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_link_output lane :=if Nat.eqb lane 0 then 3449 else 3446.
Theorem rf_link_data_three lane invalid s0 s1 s2 s3 pc :
 (lane<2)%coq_nat -> VM.find 2812 s0=Some(Gval(Fuint 32)pc) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_link_output lane)s3=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Bound PC S1 S2 S3. destruct lane as[|[|lane]];[| |lia].
'''
for a in [3447,3444]:
 s+=' {\n'
 for off,width,word,state,dep in [(0,33,'(from_N 33(to_N pc+4))',1,'PC'),(1,32,'(reference_pc_plus_four pc)',2,'V0'),(2,32,'(reference_pc_plus_four pc)',3,'V1')]:
  n=a+off
  s+=f''' assert(V{off}:VM.find {n} s{state}=Some(Gval(Fuint {width}){word})).
 {{eapply(reference_redirect_ground_step rf_link_offsets rf_link_nodes {n} rf_link_expr_{n});[exact rf_link_positions|exact rf_link_safety|apply(List.nth_error_In rf_link_nodes {ids.index(n)}%nat);reflexivity| |exact S{state}].
 intros site. cbn[rf_link_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {dep}. reflexivity. }}
'''
 s+=' exact V2. }\n'
s+='Qed.\n'
s+='''Theorem rf_link_data_observed memory inputs k observed lane pc :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<2)%coq_nat ->size pc=32%nat ->
 VM.find 7331(top_environment observed)=Some(Gval(Fuint 32)pc) ->
 VM.find(rf_link_output lane)(top_environment observed)=Some(Gval(Fuint 32)(reference_pc_plus_four pc)).
Proof.
 intros Observe Legal Lane Size PC.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(PC0:VM.find 7331(history 9254%nat)=Some(Gval(Fuint 32)pc)).
 { rewrite(proj2(exception_pc_sources_history_stable _ history 9259 9254 Steps ltac:(vm_compute;lia)))Last. exact PC. }
 pose proof(exception_pc_1749_value _ (history 9254%nat)(history 9254%nat)(history 9255%nat) _ _ PC0 (sized_uint_adapt_identity 32 pc Size)(Steps 9254%nat ltac:(vm_compute;lia)))as P1.
 pose proof(exception_pc_2812_value _ (history 9255%nat)(history 9255%nat)(history 9256%nat) pc P1 (Steps 9255%nat ltac:(vm_compute;lia)))as P2.
 rewrite <-Last. exact(rf_link_data_three lane _ (history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat) pc Lane P2
 (Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
'''
(proof/'RFLinkReferenceData.v').write_text(s)
