"""Indexed reference RF NOP output suffix and UInt32 port adaptation."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
pos=lambda at:s[:at].count('(@Qcons VarOrder.T ')-1
nodes=[];decl=[];conn=[]
for i in range(1,32):
 for n in [3615+80*(i-1),3616+80*(i-1)]:
  m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',s);nodes.append((n,pos(m.start())))
 m=re.search(r'\(@Swire VarOrder.T '+str(1787+i)+r' ',s);decl.append(pos(m.start()))
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(1787+i)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(3616+80*(i-1))+r'\)\)\)',s);assert m,i;conn.append(pos(m.start()))
out='''Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation FormalDeclaredWireCheck X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_exit_node (base index : nat) := N.of_nat (Nat.add base (Nat.mul 80 (Nat.pred index))).
Definition rf_exit_port index := N.of_nat (Nat.add 1787 index).
Definition rf_exit_outer index := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707))
 (@Eref VarOrder.T (@Eid VarOrder.T (rf_exit_node 3614 index)))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 index)))).
Definition rf_exit_alias index := @Eref VarOrder.T (@Eid VarOrder.T (rf_exit_node 3615 index)).
'''
out+='Definition rf_exit_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'(rf_exit_node {n} {i}%nat,rf_exit_{k} {i}%nat)' for i in range(1,32) for n,k in [(3615,'outer'),(3616,'alias')])+'].\n'
prev=-1;offsets=[]
for n,at in nodes:offsets.append(at-prev-1);prev=at
out+='Definition rf_exit_offsets : seq nat := [::'+';'.join(f'{x}%nat' for x in offsets)+'].\n'
out+='''Lemma rf_exit_positions : select_node_offsets rf_exit_offsets flat_statements = Some rf_exit_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_exit_safety : selected_node_safety flat_memories flat_statements rf_exit_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_exit_members index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 List.In (rf_exit_node 3615 index, rf_exit_outer index) rf_exit_nodes /\\
 List.In (rf_exit_node 3616 index, rf_exit_alias index) rf_exit_nodes.
Proof. intros Lower Upper.
'''
out+=' split.\n'
for branch in range(2):
 out+=' - apply (List.nth_error_In rf_exit_nodes '+('' if branch==0 else '(S ')+'(Nat.mul 2 (Nat.pred index))'+('' if branch==0 else ')')+').\n'
 for i in range(32):out+='   destruct index as [|index]. '+('{ lia. }\n' if i==0 else '{ vm_compute; reflexivity. }\n')
 out+='   lia.\n'
out+='Qed.\n'
for name,data in [('decl_position',decl),('connect_position',conn)]:
 out+=f'Definition rf_exit_{name} (index : nat) : nat := match index with\n'+''.join(f'| {i}%nat => {v}%nat\n' for i,v in enumerate(data,1))+'| _ => 0%nat end.\n'
out+='''Lemma rf_exit_wire_certificates index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_exit_decl_position index)
 (Nat.sub (rf_exit_connect_position index) (S (rf_exit_decl_position index)))
 (rf_exit_port index) (rf_exit_node 3616 index) 32 = true.
Proof. intros Lower Upper.
'''
for i in range(32):out+='destruct index as [|index]. '+('{ lia. }\n' if i==0 else '{ vm_compute; reflexivity. }\n')
out+='lia. Qed.\n'
out+='''Lemma rf_exit_alias_step index invalid old current result value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 VM.find (rf_exit_node 3615 index) old = Some value ->
 (exists width word, value = Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_exit_node 3616 index) result = Some value.
Proof.
 intros Lower Upper Input [width [word Value]] Step. subst value.
 destruct (rf_exit_members index Lower Upper) as [_ Member].
 destruct (selected_node_safe_position flat_memories flat_statements rf_exit_offsets flat_statements rf_exit_nodes _ _ rf_exit_positions rf_exit_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rf_exit_alias eval_hfexpr_validif_policy eval_href_validif_policy]. exact Input.
Qed.
Lemma rf_exit_wire_step index invalid old current result word value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat -> size word = 32%nat ->
 rf_reference_word_extension word value ->
 VM.find (rf_exit_node 3616 index) old = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_exit_port index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Lower Upper Size [width [Width Value]] Input Step. subst value.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_exit_decl_position index)
 (Nat.sub (rf_exit_connect_position index) (S (rf_exit_decl_position index))) (rf_exit_port index) (rf_exit_node 3616 index) 32);
 [apply rf_exit_wire_certificates;assumption|exact Input| |exact Step].
 cbn [adapt_hvalue_as_type].
 rewrite (rf_reference_word_resize word width 32 Size Width (leqnn 32)).
 unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Theorem rf_reference_nop_exit index invalid state0 state1 state2 state3 word value :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat -> size word = 32%nat ->
 rf_reference_word_extension word value ->
 VM.find (rf_exit_node 3614 index) state0 = Some value ->
 VM.find 1707 state0 = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories state0 false state0 flat_statements = Some state1 ->
 formal_value_iter invalid flat_memories state1 false state1 flat_statements = Some state2 ->
 formal_value_iter invalid flat_memories state2 false state2 flat_statements = Some state3 ->
 VM.find (rf_exit_port index) state3 = Some (Gval (Fuint 32) word).
Proof.
 intros Lower Upper Size Extension Input Enable Step0 Step1 Step2.
 destruct (rf_exit_members index Lower Upper) as [Member _].
 destruct (rf_reference_word_true_node rf_exit_offsets rf_exit_nodes (rf_exit_node 3615 index) 1707 (rf_exit_node 3614 index) (N.of_nat (Nat.sub 2177 index)) invalid state0 state0 state1 word value rf_exit_positions rf_exit_safety Member Size Extension Enable Input Step0) as [outer [Outer Extended]].
 assert (Alias : VM.find (rf_exit_node 3616 index) state2 = Some outer).
 { eapply rf_exit_alias_step; [exact Lower|exact Upper|exact Outer| |exact Step1].
   destruct Extended as [width [_ Value]]. exists width, (zext_to width word). exact Value. }
 exact (rf_exit_wire_step index invalid state2 state2 state3 word outer Lower Upper Size Extended Alias Step2).
Qed.
'''
(p/'RFReferenceNopExit.v').write_text(out)
