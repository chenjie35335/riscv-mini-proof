"""Connect actual non-load decode to the zero-width history and original assertion."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
out='''Require Import CoreSocModel ComparisonNodes CycleView ReferenceNonloadDecode ReferenceZeroReadWidth ReferenceMemoryRequest MemoryRequestObservedSemantics LoadTypeCorrespondence LoadPipelineClassification ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory FormalAssertionDischarge MemoryRequestWidth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nonload_width_assertion memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 load_type_decode(to_N instruction)49=from_N 3 0 ->generated_assert_m0_2_local(top_environment observed).
Proof.
 intros Observe Legal Reset Instruction Zero.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 pose proof(reference_nonload_guards_observed memory inputs k observed instruction enabled Observe Legal Instruction Zero Enabled)as Decode.
 destruct(observed_history memory inputs k observed Observe Legal)as[bit[history[Last[Steps Resets]]]].
 assert(Enable:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])).
 { intros t Lower Upper. rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 bit Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Enabled. }
 assert(Guards:forall node,List.In node [::1970;1966;1962;1958;1886] ->forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])).
 { intros node Member t Lower Upper. cbn in Member. repeat destruct Member as[<-|Member];try contradiction.
'''
for n,row in [(1970,4),(1966,3),(1962,2),(1958,1),(1886,0)]:
 out+=f' - rewrite(reference_control_stable_{n}_history (generated_observation_input inputs k)nil history 9259 bit Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact(Decode {row}%nat ltac:(lia)).\n'
out+=''' }
 assert(Ref:forall t,(210<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1521(history t)=Some(Gval(Fuint 6)(zeros 6))).
 { intros t Lower Upper. exact(reference_zero_read_width_history _ history 9259 200 enabled Steps Enable Guards t Lower Upper). }
 pose proof(load_pipeline_observed memory inputs k observed Observe Legal instruction Instruction)as Mode. rewrite Zero in Mode.
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7755(history t)=Some(Gval(Fuint 3)(from_N 3 0))).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7755 3 load_type_register_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(Dut:forall t,(16<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1476(history t)=Some(Gval(Fuint 6)(from_N 6 0))).
 { intros t Lower Upper. eapply(memory_width_alias_history false _ _ history 9259);[apply size_from_N|exact Steps| |exact Lower|exact Upper].
 intros u Lo Hi. exact(memory_width_decoder_history false 0%nat _ history 9259 ltac:(vm_compute;lia) Steps Modes u Lo Hi). }
 rewrite <-Last. eapply(assertion_2_from_enabled_agreement _ (history 9258%nat)(history 9258%nat)(history 9259%nat));[apply Steps;vm_compute;lia|].
 intro EnabledAssertion. exists 6%nat,6%nat,(from_N 6 0),(zeros 6).
 split;[apply Dut;vm_compute;lia|]. split;[apply Ref;vm_compute;lia|reflexivity].
Qed.
'''
(root/'formal/flat-low/staged-integration/NonloadWidthAssertion.v').write_text(out)
