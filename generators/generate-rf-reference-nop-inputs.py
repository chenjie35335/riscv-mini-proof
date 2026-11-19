"""Five actual connections supplying reference instruction and commit enable."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
rows=[(1396,7750,32),(1516,1396,32),(1706,1516,32),(1517,1395,1),(1707,1517,1)]
pos=lambda at:s[:at].count('(@Qcons VarOrder.T ')-1
out='''Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck FormalInstructionResetConstants JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node,source,width in rows:
 m=re.search(r'\(@Swire VarOrder.T '+str(node)+r' \(Gtyp \(Fuint '+str(width)+r'\)\)',s);assert m,node;decl=pos(m.start())
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(node)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(source)+r'\)\)\)',s);assert m,node;distance=pos(m.start())-decl-1
 val='(Gval (Fuint 32) instruction_nop)' if width==32 else '(Gval (Fuint 1) [::true])'
 out+=f'''Lemma rf_reference_input_{node}_certificate : declared_wire_check flat_memories flat_statements {decl}%nat {distance}%nat {node} {source} {width}%nat = true.
Proof. vm_compute. reflexivity. Qed.
Local Lemma rf_reference_input_{node}_step invalid old result :
 VM.find {source} old = Some {val} ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find {node} result = Some {val}.
Proof.
 intros Source Step.
 eapply (declared_wire_checked_value flat_memories flat_statements {decl}%nat {distance}%nat {node} {source} {width}%nat);
 [exact rf_reference_input_{node}_certificate|exact Source|vm_compute;reflexivity|exact Step].
Qed.
'''
ids=list(map(int,re.findall(r'\((\d+),\d+\)',(p/'JointBoundaryRegisters.v').read_text())))
out+=f'''Lemma rf_reference_input_register_member : List.In (7750%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers {ids.index(7750)}%nat). vm_compute. reflexivity. Qed.
Theorem rf_reference_nop_inputs_history invalid history limit :
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|[|[|time]]]; try lia.
 apply (rf_reference_input_1706_step invalid (history (S (S time))) (history (S (S (S time))))); [|apply Steps;lia].
 apply (rf_reference_input_1516_step invalid (history (S time)) (history (S (S time)))); [|apply Steps;lia].
 apply (rf_reference_input_1396_step invalid (history time) (history (S time))); [|apply Steps;lia].
 rewrite (joint_update_register_history_same invalid history limit 7750 32 rf_reference_input_register_member Steps time ltac:(lia)). exact Initial.
Qed.
Theorem rf_reference_enable_inputs_history invalid history (limit start : nat) :
 (forall time, (start <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 1395 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|[|time]]; try lia.
 apply (rf_reference_input_1707_step invalid (history (S time)) (history (S (S time)))); [|apply Steps;lia].
 apply (rf_reference_input_1517_step invalid (history time) (history (S time))); [|apply Steps;lia].
 apply Initial;lia.
Qed.
'''
(p/'RFReferenceNopInputs.v').write_text(out)
