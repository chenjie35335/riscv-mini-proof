from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
rows=json.loads((base/'reference-control-stability-plan.json').read_text())['nodes'];shape={int(n):ds for n,ds in json.loads((base/'reference-control-shape-dependencies.json').read_text()).items()};roots=[r['id'] for r in rows if r['kind']=='register']
s='''Require Import CoreSocModel ComparisonNodes RegisterInvariants StagedRegisterHold ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCongruence3 ReferenceControlWires0 ReferenceControlWires1 ReferenceControlWires2 ReferenceControlWires3.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
s+='Definition reference_control_registers : list VarOrder.T := [::'+';'.join(map(str,roots))+'].\n'
s+='''Lemma reference_control_registers_check : List.forallb (fun node => has_register node flat_statements) reference_control_registers = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_control_register_present node :
 List.In node reference_control_registers -> has_register node flat_statements = true.
Proof.
 intro Member. pose proof reference_control_registers_check as Check. rewrite List.forallb_forall in Check.
 exact (Check node Member).
Qed.
Lemma reference_control_register_history_same invalid history limit node :
 has_register node flat_statements = true ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (time <= limit)%coq_nat -> VM.find node (history time) = VM.find node (history 0%nat).
Proof.
 intros Present Steps time. induction time as [|time IH]; intro Bound; [reflexivity|].
 rewrite (staged_combinational_holds_registers invalid flat_memories (history time) (history time) (history (S time)) flat_statements node Present (Steps time ltac:(lia))).
 apply IH. lia.
Qed.
'''
common=''' (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
'''
for r in rows:
 n,rank,kind=r['id'],r['rank'],r['kind']
 if kind!='register':
  s+=f'Theorem reference_control_ground_{n}_history inputs path history limit bit :\n'+common+f''' forall time, ({rank} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value ground, VM.find {n} (history time) = Some value /\\ type_of_val value = Gtyp ground.
Proof.
 intros Resets Steps time Lower Upper.
'''
  if kind=='reset':s+=' exists (Gval (Fuint 1) [::bit]), (Fuint 1). split; [apply Resets; exact Upper|reflexivity].\n'
  else:
   s+=' destruct time as [|time]; [lia|].\n'
   if kind=='Sfcnct':s+=f' apply (reference_control_wire_{n}_ground (formal_invalid_policy inputs path) (history time) (history time) (history (S time))). apply Steps. lia.\n'
   else:
    s+=f' apply (reference_control_node_{n}_ground inputs path (history time) (history time) (history (S time))).\n'
    for d in shape[n]:s+=f' - apply (reference_control_ground_{d}_history inputs path history limit bit Resets Steps time); lia.\n'
    s+=' - apply Steps. lia.\n'
  s+='Qed.\n'
 if kind=='register':
  s+=f'''Lemma reference_control_register_{n}_present : has_register {n} flat_statements = true.
Proof. apply reference_control_register_present. apply (List.nth_error_In reference_control_registers {roots.index(n)}%nat). vm_compute. reflexivity. Qed.
'''
 s+=f'Theorem reference_control_stable_{n}_history inputs path history limit bit :\n'+common+f''' forall left right, ({rank} <= left)%coq_nat -> ({rank} <= right)%coq_nat -> (left <= limit)%coq_nat -> (right <= limit)%coq_nat ->
 VM.find {n} (history left) = VM.find {n} (history right).
Proof.
 intros Resets Steps left right LeftLower RightLower LeftUpper RightUpper.
'''
 if kind=='register':
  s+=f''' rewrite (reference_control_register_history_same _ history limit {n} reference_control_register_{n}_present Steps left LeftUpper)
 (reference_control_register_history_same _ history limit {n} reference_control_register_{n}_present Steps right RightUpper). reflexivity.
'''
 elif kind=='reset':s+=' rewrite (Resets left LeftUpper) (Resets right RightUpper). reflexivity.\n'
 else:
  s+=' destruct left as [|left]; [lia|]. destruct right as [|right]; [lia|].\n'
  if kind=='Sfcnct':s+=f' apply (reference_control_wire_{n}_congruent (formal_invalid_policy inputs path) (history left) (history right) (history (S left)) (history (S right))).\n'
  else:
   s+=f' apply (reference_control_node_{n}_congruent inputs path (history left) (history right) (history (S left)) (history (S right))).\n'
   for d in shape[n]:s+=f' - apply (reference_control_ground_{d}_history inputs path history limit bit Resets Steps left); lia.\n'
  for d in r['dependencies']:s+=f' - apply (reference_control_stable_{d}_history inputs path history limit bit Resets Steps left right); lia.\n'
  s+=' - apply Steps. lia.\n - apply Steps. lia.\n'
 s+='Qed.\n'
marker=s.index('Theorem reference_control_ground_1_history')
registers=s[:marker]
registers=registers.replace(registers.splitlines()[0], 'Require Import CoreSocModel ComparisonNodes RegisterInvariants StagedRegisterHold.')
rp=proof/'ReferenceControlRegisters.v'
if not rp.exists() or rp.read_text()!=registers:rp.write_text(registers)
header_end=s.index('Definition reference_control_registers')
s=s[:header_end]+'Require Import ReferenceControlRegisters.\nLocal Opaque flat_statements flat_memories generated_modules generated_top.\n'+s[marker:]
p=proof/'ReferenceControlStabilityHistory.v'
if not p.exists() or p.read_text()!=s:p.write_text(s)
print('generated',len(rows),'ranked stability and',len(rows)-len(roots),'ground history lemmas')
