"""Close actual store immediate history using legal observed instruction decoding."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
load=(base/'ReferenceLoadImmediate.v').read_text()
imports=load.split('Definition',1)[0].split('Lemma',1)[0]
imports=imports.replace('Require Import CoreSocModel','Require Import JointUpdateBoundaryHistory ReferenceLoadImmediate ReferenceStoreParts StoreTypeCorrespondence RFScalarControl ReferenceInstructionDecode ReferenceIllegalObserved CoreSocModel')
s=imports+'''Lemma store_reference_enabled_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 (lane < 3)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 store_type_is_store instruction lane ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal Reset Lane Instruction Store.
 destruct (load_pipeline_late_observed memory inputs k observed Observe Legal) as [bit [Late Nop]].
 destruct bit.
 - specialize (Nop (Logic.eq_refl _)). rewrite Nop in Instruction. inversion Instruction;subst instruction.
   exfalso. exact (store_type_nop_not_store lane Lane Store).
 - exact (reference_enable_observed_bubble memory inputs k observed false Observe Legal Reset Late).
Qed.
Definition store_upper_decoder n := nth 0%nat [::29%nat;30%nat;31%nat;32%nat;33%nat;34%nat;35%nat;36%nat;37%nat;38%nat;39%nat] n.
Lemma store_upper_guard n : (n < 11)%coq_nat -> load_imm_mux_guard true n = reference_instruction_guard (store_upper_decoder n).
Proof. intro Bound. do 11 (destruct n as [|n];[reflexivity|]);lia. Qed.
Lemma store_upper_decode instruction lane n :
 (lane < 3)%coq_nat -> (n < 11)%coq_nat -> store_type_is_store instruction lane ->
 N.eqb (reference_instruction_code (store_upper_decoder n)) (N.land (to_N instruction) (reference_instruction_mask (store_upper_decoder n))) = Nat.eqb n (Nat.sub 7 lane).
Proof.
 intros Lane Bound Store.
 assert (Row : (Nat.sub 36 lane < 37)%coq_nat) by lia.
 assert (Match : N.land (to_N instruction) (reference_instruction_mask (Nat.sub 36 lane)) = reference_instruction_code (Nat.sub 36 lane)).
 { unfold store_type_is_store in Store. do 3 (destruct lane as [|lane];[exact Store|]);lia. }
 rewrite (rf_reference_decode_onehot instruction (Nat.sub 36 lane) (store_upper_decoder n) Row ltac:(do 11 (destruct n as [|n];[cbn [store_upper_decoder nth];lia|]);lia) Match).
 do 3 (destruct lane as [|lane];[do 11 (destruct n as [|n];[reflexivity|]);lia|]);lia.
Qed.
'''
# Reuse established observed-history extraction proof, but replace load-only guard derivation.
t=load[load.index('Theorem reference_load_immediate_observed'):]
t=t.replace('reference_load_immediate_observed','reference_store_immediate_observed').replace('(lane < 5)','(lane < 3)').replace('load_type_is_load','store_type_is_store').replace('load_i_immediate','store_s_immediate')
t=t.replace('pose proof (proj2 (load_pipeline_load_reference_enabled memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load)) as Enabled.','pose proof (store_reference_enabled_observed memory inputs k observed instruction lane Observe Legal Reset Lane Instruction Load) as Enabled.')
a=t.index(' assert (Guards :');b=t.index(' pose proof (reference_load_immediate_history',a)
t=t[:a]+''' assert (Guards : forall n, (n < load_imm_mux_count true)%coq_nat -> VM.find (load_imm_mux_guard true n) (history 9250%nat) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 7 lane)])).
 { intros n Bound. cbn [load_imm_mux_count] in Bound. rewrite (store_upper_guard n Bound).
   pose proof (reference_instruction_decode_history (formal_invalid_policy (generated_observation_input inputs k) nil) (fun t => history (Nat.add 9248 t)) 2 instruction (store_upper_decoder n)
      ltac:(do 11 (destruct n as [|n];[cbn [store_upper_decoder nth];lia|]);lia)
      ltac:(intros i I;destruct i as [|[|i]];[apply Steps;vm_compute;lia|apply Steps;vm_compute;lia|lia])
      ltac:(intros i I;destruct i as [|[|[|i]]];[apply Source;vm_compute;lia|apply Source;vm_compute;lia|apply Source;vm_compute;lia|lia])
      2 ltac:(lia) ltac:(lia)) as Decode.
   change (VM.find (reference_instruction_guard (store_upper_decoder n)) (history 9250%nat) = Some (Gval (Fuint 1) [::N.eqb (reference_instruction_code (store_upper_decoder n)) (N.land (to_N instruction) (reference_instruction_mask (store_upper_decoder n)))])) in Decode.
   rewrite (store_upper_decode instruction lane n Lane Bound Load) in Decode. exact Decode. }
'''+t[b:]
t=t.replace('reference_load_immediate_history','reference_store_immediate_history').replace('(load_imm_guards_selected (history 9250%nat) lane Lane Guards Fence Ecall Ebreak)','Guards')
s+=t
(base/'ReferenceStoreObserved.v').write_text(s)
