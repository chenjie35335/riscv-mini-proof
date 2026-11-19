"""Compose checked Boolean node transfers across actual local histories."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low'
entries=json.loads((base/'legal-boolean-cone.json').read_text())['nodes']
out='''Require Import CoreSocModel ComparisonNodes LegalBooleanCone FormalLocalHistory NormalizedBit.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for e in entries:
 n,r=e['id'],e['rank']
 out+=fr'''Theorem legal_bool_{n}_history invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 forall time, ({r} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find {n} (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper. destruct time as [|time]; [lia|].
 apply (legal_bool_{n}_normalized invalid (history time) (history time) (history (S time))).
'''
 if not e['leaf']:
  for src in e['dependencies']:out+=f' - apply (legal_bool_{src}_history invalid history limit Steps time); lia.\n'
 out+=(' - ' if not e['leaf'] else ' ')+ 'apply Steps. lia.\nQed.\n'
out+='Print Assumptions legal_bool_9139_history.\n'
p=base/'staged-integration/LegalBooleanHistory.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
