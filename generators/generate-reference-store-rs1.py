"""Reuse the shared actual rs1 mux and register-bank reader for stores."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
load=(base/'ReferenceLoadRs1.v').read_text();obs=(base/'ReferenceStoreObserved.v').read_text()
s=load[:load.index('Definition')].replace('Require Import ReferenceRegisterRead','Require Import ReferenceLoadRs1 ReferenceStoreObserved StoreTypeCorrespondence RFScalarControl ReferenceIllegalObserved RFReferenceNopHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory FormalLocalHistory MemoryRequestObservedSemantics ReferenceRegisterRead')
s+='''Lemma reference_store_rs1_raw inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 VM.find(reference_load_rs1_yes(Nat.sub 7 lane))(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source.
'''
for lane in range(3):
 s+=' destruct lane as [|lane].\n {\n'
 for j in range(3):
  n=1942+5*lane+j;src=1884 if j==0 else n-1;w=[25,20,5][j];v=['take 25 instruction','take 20 instruction','rf_instruction_address false instruction'][j]
  s+=f''' assert (V{j}:VM.find {n}(history time)=Some(Gval(Fuint {w})({v}))).
 {{ rewrite (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes {n} reference_control_expr_{n});
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_{n}| |apply Steps;lia].
 intro site. cbn [reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {'Source' if j==0 else 'V'+str(j-1)}. cbn.
'''
  if j==2:s+=' unfold rf_instruction_address.\n'
  s+=' repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }\n'
 s+=' exact V2. }\n'
s+=' lia.\nQed.\n'
a=load.index('Theorem reference_load_rs1_history');b=load.index('Lemma reference_load_rs1_other',a)
t=load[a:b].replace('reference_load_rs1_history','reference_store_rs1_history').replace('reference_load_rs1_raw','reference_store_rs1_raw').replace('(lane<5)','(lane<3)').replace('Nat.sub 4 lane','Nat.sub 7 lane');s+=t
s+='''Lemma reference_store_rs1_decode instruction lane n : (lane<3)%coq_nat ->(n<19)%coq_nat ->store_type_is_store instruction lane ->
 N.eqb(reference_instruction_code(Nat.add 29 n))(N.land(to_N instruction)(reference_instruction_mask(Nat.add 29 n)))=Nat.eqb n(Nat.sub 7 lane).
Proof.
 intros Lane Bound Store.
 assert (Match : N.land (to_N instruction) (reference_instruction_mask (Nat.sub 36 lane)) = reference_instruction_code (Nat.sub 36 lane)).
 { unfold store_type_is_store in Store. do 3 (destruct lane as [|lane];[exact Store|]);lia. }
 rewrite (rf_reference_decode_onehot instruction (Nat.sub 36 lane) (Nat.add 29 n) ltac:(lia) ltac:(lia) Match).
 do 3 (destruct lane as [|lane];[do 19 (destruct n as [|n];[reflexivity|]);lia|]);lia.
Qed.
'''
a=load.index('Theorem reference_load_rs1_observed');b=load.index('Qed.',a)+len('Qed.')
t=load[a:b].replace('reference_load_rs1_observed','reference_store_rs1_observed').replace('reference_load_rs1_decode','reference_store_rs1_decode').replace('reference_load_rs1_history','reference_store_rs1_history').replace('(lane < 5)','(lane < 3)').replace('load_type_is_load','store_type_is_store').replace('Nat.sub 4 lane','Nat.sub 7 lane')
t=t.replace('pose proof (proj2 (load_pipeline_load_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load)) as Enabled.','pose proof (store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as Enabled.')
s+=t+'\n'
t=load[load.index('Theorem reference_load_rs1_bank_observed'):].replace('reference_load_rs1_bank_observed','reference_store_rs1_bank_observed').replace('reference_load_rs1_observed','reference_store_rs1_observed').replace('(lane<5)','(lane<3)').replace('load_type_is_load','store_type_is_store');s+=t
(base/'ReferenceStoreRs1.v').write_text(s)
