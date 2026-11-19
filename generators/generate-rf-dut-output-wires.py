"""Checked five-step DUT architectural-output wiring, including x0."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
pos=lambda at:s[:at].count('(@Qcons VarOrder.T ')-1
nodes=[]
for dst,src in [(1117,1053),(8041,819),(8166,8041)]:
 for i in range(32):
  pat=r'\(@Snode VarOrder.T '+str(dst+i)+r' \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(src+i)+r'\)\)\)';m=re.search(pat,s);assert m,(dst,i);nodes.append((dst+i,src+i,pos(m.start())))
assert nodes==sorted(nodes,key=lambda row:row[2])
wire={}
for outer,dst,src in [(False,819,1117),(True,1399,8166)]:
 for i in range(32):
  m=re.search(r'\(@Swire VarOrder.T '+str(dst+i)+r' \(Gtyp \(Fuint 32\)\)\)',s);assert m;decl=pos(m.start())
  m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(dst+i)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T '+str(src+i)+r'\)\)\)',s);assert m;wire[outer,i]=(decl,pos(m.start())-decl-1)
out='''Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_dut_output_node base index := N.of_nat (Nat.add base index).
Definition rf_dut_alias_target stage index := rf_dut_output_node (match stage with 0%nat => 1117%nat | 1%nat => 8041%nat | _ => 8166%nat end) index.
Definition rf_dut_alias_source stage index := rf_dut_output_node (match stage with 0%nat => 1053%nat | 1%nat => 819%nat | _ => 8041%nat end) index.
Definition rf_dut_alias_expression stage index := @Eref VarOrder.T (@Eid VarOrder.T (rf_dut_alias_source stage index)).
'''
out+='Definition rf_dut_output_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+';'.join(f'(rf_dut_alias_target {stage}%nat {i}%nat,rf_dut_alias_expression {stage}%nat {i}%nat)' for stage in range(3) for i in range(32))+'].\n'
prev=-1;offs=[]
for _,_,at in nodes:offs.append(at-prev-1);prev=at
out+='Definition rf_dut_output_offsets : seq nat := [::'+';'.join(f'{x}%nat' for x in offs)+'].\n'
out+='''Lemma rf_dut_output_positions : select_node_offsets rf_dut_output_offsets flat_statements = Some rf_dut_output_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_dut_output_safety : selected_node_safety flat_memories flat_statements rf_dut_output_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_dut_alias_member (stage index : nat) : (stage < 3)%coq_nat -> (index < 32)%coq_nat ->
 List.In (rf_dut_alias_target stage index, rf_dut_alias_expression stage index) rf_dut_output_nodes.
Proof. intros Stage Index.
 apply (List.nth_error_In rf_dut_output_nodes (Nat.add (Nat.mul 32 stage) index)).
 destruct stage as [|[|[|stage]]]; try lia.
'''
for stage in range(3):
 out+=' - '
 for i in range(32):out+='destruct index as [|index]. { vm_compute;reflexivity. }\n'
 out+='   lia.\n'
out+='Qed.\n'
out+='''Definition rf_dut_wire_target outer index := rf_dut_output_node (if outer then 1399%nat else 819%nat) index.
Definition rf_dut_wire_source outer index := rf_dut_output_node (if outer then 8166%nat else 1117%nat) index.
'''
for name,part in [('position',0),('distance',1)]:
 out+=f'Definition rf_dut_wire_{name} (outer : bool) (index : nat) : nat :=\n match outer,index with\n'+''.join(f'| {str(outer).lower()},{i}%nat => {wire[outer,i][part]}%nat\n' for outer in [False,True] for i in range(32))+'| _,_ => 0%nat end.\n'
out+='''Lemma rf_dut_wire_certificate outer index : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_dut_wire_position outer index) (rf_dut_wire_distance outer index)
 (rf_dut_wire_target outer index) (rf_dut_wire_source outer index) 32 = true.
Proof. intro Index. destruct outer.
'''
for outer in [True,False]:
 out+=' - '
 for i in range(32):out+='destruct index as [|index]. { vm_compute;reflexivity. }\n'
 out+='   lia.\n'
out+='Qed.\n'
out+='''Lemma rf_dut_output_alias_step stage index invalid old current result word :
 (stage < 3)%coq_nat -> (index < 32)%coq_nat ->
 VM.find (rf_dut_alias_source stage index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_dut_alias_target stage index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Stage Index Input Step.
 pose proof (rf_dut_alias_member stage index Stage Index) as Member.
 destruct (selected_node_safe_position flat_memories flat_statements rf_dut_output_offsets flat_statements rf_dut_output_nodes _ _ rf_dut_output_positions rf_dut_output_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [rf_dut_alias_expression eval_hfexpr_validif_policy eval_href_validif_policy]. exact Input.
Qed.
Lemma rf_dut_output_wire_step outer index invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_dut_wire_source outer index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_dut_wire_target outer index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Index Size Input Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_dut_wire_position outer index) (rf_dut_wire_distance outer index) (rf_dut_wire_target outer index) (rf_dut_wire_source outer index) 32);
 [apply rf_dut_wire_certificate;exact Index|exact Input| |exact Step].
 cbn [adapt_hvalue_as_type].
 assert (Take : take 32 word = word). { apply take_oversize. rewrite Size. reflexivity. }
 rewrite Take. unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Theorem rf_dut_output_wires index invalid state0 state1 state2 state3 state4 state5 word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_dut_output_node 1053 index) state0 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories state0 false state0 flat_statements = Some state1 ->
 formal_value_iter invalid flat_memories state1 false state1 flat_statements = Some state2 ->
 formal_value_iter invalid flat_memories state2 false state2 flat_statements = Some state3 ->
 formal_value_iter invalid flat_memories state3 false state3 flat_statements = Some state4 ->
 formal_value_iter invalid flat_memories state4 false state4 flat_statements = Some state5 ->
 VM.find (rf_dut_output_node 1399 index) state5 = Some (Gval (Fuint 32) word).
Proof.
 intros Index Size Input Step0 Step1 Step2 Step3 Step4.
 pose proof (rf_dut_output_alias_step 0 index invalid state0 state0 state1 word ltac:(lia) Index Input Step0) as Alias0.
 pose proof (rf_dut_output_wire_step false index invalid state1 state1 state2 word Index Size Alias0 Step1) as Wire0.
 pose proof (rf_dut_output_alias_step 1 index invalid state2 state2 state3 word ltac:(lia) Index Wire0 Step2) as Alias1.
 pose proof (rf_dut_output_alias_step 2 index invalid state3 state3 state4 word ltac:(lia) Index Alias1 Step3) as Alias2.
 exact (rf_dut_output_wire_step true index invalid state4 state4 state5 word Index Size Alias2 Step4).
Qed.
'''
(p/'RFDutOutputWires.v').write_text(out)
