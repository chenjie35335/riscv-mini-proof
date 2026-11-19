"""Batch the actual byte/halfword/word store data slices and observed bank source."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text();q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
nodes=[6634,6635,6654,6655,6678,6679];pairs=[];poses=[]
for n in nodes:
 key=f'(@Snode VarOrder.T {n} ';a=model.index(key)+len(key);d=0
 for b in range(a,len(model)):
  d+=(model[b]=='(')-(model[b]==')')
  if d==0:break
 pairs.append(f'({n},{model[a:b+1]})');poses.append(bisect.bisect_right(q,a)-1)
s='''Require Import CoreSocModel ComparisonNodes ReferenceStoreRs2 StoreTypeCorrespondence RFReadPorts RFReferenceNopHistory ReferenceRedirectSpine ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
s+='Definition reference_store_data_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(pairs)+'].\n'
s+='Definition reference_store_data_offsets := [::'+';'.join(str(n)+'%nat' for n in [poses[0]]+[b-a-1 for a,b in zip(poses,poses[1:])])+'].\n'
s+='''Lemma reference_store_data_positions : select_node_offsets reference_store_data_offsets flat_statements = Some reference_store_data_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_data_safety : selected_node_safety flat_memories flat_statements reference_store_data_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_store_data_base lane : VarOrder.T := nth 0 [::6678;6654;6634] lane.
Definition reference_store_data_width lane := nth 0%nat [::32%nat;16%nat;8%nat] lane.
Theorem reference_store_data_steps lane invalid s0 s1 s2 word : (lane<3)%coq_nat ->
 VM.find 2804 s0=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find (reference_store_data_base lane+1) s2=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)word)).
Proof.
 intros Lane Source Step1 Step2.
'''
for lane,(n,w) in enumerate([(6678,32),(6654,16),(6634,8)]):
 s+=' destruct lane as [|lane]. {\n'
 for j in range(2):
  expr=pairs[nodes.index(n+j)].split(',',1)[1][:-1];width=32 if j==0 else w;value='word' if j==0 else f'take {w} word'
  if j==0:s+=f' assert (Alias:VM.find {n} s1=Some(Gval(Fuint 32)word)). {{\n'
  else:s+=f' change (VM.find {n+1} s2=Some(Gval(Fuint {w})(take {w} word))).\n'
  s+=f''' eapply (reference_redirect_ground_step reference_store_data_offsets reference_store_data_nodes {n+j} {expr} (Fuint {width}) ({value}) invalid {"s0" if j==0 else "s1"} {"s0" if j==0 else "s1"} {"s1" if j==0 else "s2"});
 [exact reference_store_data_positions|exact reference_store_data_safety|
 apply (List.nth_error_In reference_store_data_nodes {nodes.index(n+j)}%nat);vm_compute;reflexivity|
 intro site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];'''
  s+= 'exact Source|exact Step1]. }\n' if j==0 else 'rewrite Alias;cbn;rewrite drop0;reflexivity|exact Step2]. }\n'
s+=' lia. Qed.\n'
s+='''Theorem reference_store_data_observed memory inputs k observed instruction lane bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->store_type_is_store instruction lane ->
 rf_reference_bank_at(top_environment observed)bank ->
 VM.find(reference_store_data_base lane+1)(top_environment observed)=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)(bank(to_nat(rf_instruction_address true instruction))))).
Proof.
 intros Observe Legal Reset Lane Instruction Store Bank.
 pose proof(reference_store_rs2_bank_observed memory inputs k observed instruction lane bank Observe Legal Reset Lane Instruction Store Bank)as Data.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Source:VM.find 2804(history 9257%nat)=Some(Gval(Fuint 32)(bank(to_nat(rf_instruction_address true instruction))))).
 { rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9257 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last;exact Data. }
 rewrite <-Last. eapply(reference_store_data_steps lane _ (history 9257%nat)(history 9258%nat)(history 9259%nat));[exact Lane|exact Source|apply Steps;vm_compute;lia|apply Steps;vm_compute;lia].
Qed.
'''
(base/'staged-integration/ReferenceStoreData.v').write_text(s)
