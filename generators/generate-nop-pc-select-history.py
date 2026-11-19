"""Compose exact NOP decode steps over the actual combinational history."""
from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
values=json.loads((base/'nop-pc-select-values.json').read_text());order=values['nodes'];rows={r['id']:r for r in values['rows']}
out='''Require Import NopKillHistory NopPCSelectValues.
Require Import CoreSocModel ComparisonNodes NopKillValues FormalInstructionResetConstants JointUpdateBoundaryHistory JointBoundaryRegisters.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for n in order:
 row=rows[n];rank=row['rank']
 out+=f'''Theorem nop_kill_history_{n} invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, ({rank} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find {n} (history time) = Some nop_kill_value_{n}.
Proof.
 intros Initial Steps time Lower Upper.
'''
 if n==7748:
  out+=''' rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps time Upper).
 exact Initial.
'''
 else:
  out+=' destruct time as [|time]; [lia|].\n'
  out+=f' apply (nop_kill_step_{n} invalid (history time) (history time) (history (S time))).\n'
  for dep in row['dependencies']:out+=f' - apply (nop_kill_history_{dep} invalid history limit Initial Steps time); lia.\n'
  out+=' - apply Steps. lia.\n'
 out+='Qed.\n'
for target,name,width,bs in [(84,'nop_pc_select_zero_history',2,'[::false;false]'),(7771,'nop_pc_select_7771_false_history',1,'[::false]'),(7772,'nop_pc_select_7772_false_history',1,'[::false]'),(7776,'nop_pc_select_7776_false_history',1,'[::false]')]:
 rank=rows[target]['rank']
 out+=f'''Theorem {name} invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, ({rank} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find {target} (history time) = Some (Gval (Fuint {width}) {bs}).
Proof.
 intros Initial Steps time Lower Upper.
 exact (nop_kill_history_{target} invalid history limit Initial Steps time Lower Upper).
Qed.
Theorem {name}_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, ({rank} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find {target} (history time) = Some (Gval (Fuint {width}) {bs}).
Proof.
 intros Final Steps.
 rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl _)) in Final.
 exact ({name} invalid history limit Final Steps).
Qed.
Print Assumptions {name}.
'''
import re
for n in order:
 out=re.sub(r'\bnop_kill_(value|step|history)_'+str(n)+r'\b',lambda m:'nop_pc_select_'+m[1]+'_'+str(n),out)
p=proof/'NopPCSelectHistory.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
print('Generated history for',len(order),'new nodes; target84 rank55, selectors rank56')
