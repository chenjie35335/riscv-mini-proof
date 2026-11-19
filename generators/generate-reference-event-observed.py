"""Connect the shared exception mux theorem to actual observed guards."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
rows=json.loads((base/'event-proof-frontier.json').read_text())['reference_event_flag_spine'];ids={r['node'] for r in rows};guards=sorted({n for r in rows for n in r['dependencies'] if n not in ids})
s='''Require Import CoreSocModel ComparisonNodes ReferenceEventSpine ReferenceEventConditions ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_event_guard_stable inputs path history limit reset node :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 List.In node reference_event_guards ->
 forall left right, (200 <= left)%coq_nat -> (200 <= right)%coq_nat -> (left <= limit)%coq_nat -> (right <= limit)%coq_nat ->
 VM.find node (history left) = VM.find node (history right).
Proof.
 intros Resets Steps Member left right LL RL LU RU.
 cbn [reference_event_guards List.In] in Member.
'''
for n in guards:
 s+=f' destruct Member as [<-|Member];[exact (reference_control_stable_{n}_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].\n'
s+=' contradiction.\nQed.\n'
s+='''Theorem reference_event_value_observed memory inputs k observed guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_event_guards -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::reference_event_value guards]).
Proof.
 intros Observe Legal Values.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Guards : forall node i, List.In node reference_event_guards -> (200 <= i)%coq_nat -> (i <= 9259)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])).
 { intros node i Member Lower Upper.
 rewrite (reference_event_guard_stable (generated_observation_input inputs k) nil history 9259 reset node Resets Steps Member i 9259%nat Lower ltac:(vm_compute;lia) Upper ltac:(lia)) Last.
 exact (Values node Member). }
 rewrite <- Last. exact (reference_event_spine_history guards _ history 9259 200 Steps Guards 9259 ltac:(vm_compute;lia) ltac:(lia)).
Qed.
Theorem reference_event_safe_observed memory inputs k observed guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_event_guards -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 reference_event_safe guards -> VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Values Safe.
 rewrite (reference_event_value_observed memory inputs k observed guards Observe Legal Values) (reference_event_safe_false guards Safe). reflexivity.
Qed.
'''
p=base/'staged-integration/ReferenceEventObserved.v';mark='(* Event output transport. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
