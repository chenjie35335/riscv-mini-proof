"""Reference RF comparison ports: one checked indexed wire family."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)];pos=lambda at:bisect.bisect_right(q,at)-1
d=[];c=[]
for i in range(32):
 m=re.search(r'\(@Swire VarOrder.T '+str(1597+i)+r' ',s);d.append(pos(m.start()))
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(1597+i)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(1787+i)+r'\)\)\)',s);assert m;c.append(pos(m.start()))
out='''Require Import CoreSocModel ComparisonNodes RFReferenceNopCycle RFReferenceNopHistory RFWriteEffect FormalDeclaredWireCheck FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for n,ls in [('position',d),('distance',[b-a-1 for a,b in zip(d,c)])]:out+='Definition rf_reference_output_'+n+' (index:nat) : nat := nth 0%nat [::'+';'.join(str(x)+'%nat' for x in ls)+'] index.\n'
out+='''Lemma rf_reference_output_certificate (index:nat) : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_reference_output_position index) (rf_reference_output_distance index)
 (N.of_nat (Nat.add 1597 index)) (N.of_nat (Nat.add 1787 index)) 32 = true.
Proof. intros Bound. do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia. Qed.
Theorem rf_reference_output_step (index:nat) invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (Nat.add 1787 index)) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (N.of_nat (Nat.add 1597 index)) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Source Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_reference_output_position index) (rf_reference_output_distance index)
 (N.of_nat (Nat.add 1597 index)) (N.of_nat (Nat.add 1787 index)) 32);
 [apply rf_reference_output_certificate;exact Bound|exact Source| |exact Step].
 change (Some (Gval (Fuint 32%nat) (zext_to 32%nat (take 32%nat word))) = Some (Gval (Fuint 32%nat) word)).
 rewrite -Size take_size. unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_reference_nop_fullhistory_outputs invalid history bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1597 index)) (history 9259%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps Resets Bubble index Index.
 destruct (Bank index Index) as [Size _].
 eapply (rf_reference_output_step index invalid (history 9258%nat) (history 9258%nat) (history 9259%nat) (bank index));
 [exact Index|exact Size| |apply Steps;vm_compute;lia].
 eapply (rf_reference_nop_from_writeback_sources invalid history 9259 12 bank Bank Zero Instruction
 (rf_reference_nop_checker_enabled invalid history Steps Resets Bubble) Steps 9258 ltac:(vm_compute;lia));exact Index.
Qed.
'''
target=p/'RFReferenceNopObservedOutputs.v'
marker='(* Additional semantic composition. *)'
if target.exists() and marker in target.read_text():out += target.read_text()[target.read_text().index(marker):]
target.write_text(out)
