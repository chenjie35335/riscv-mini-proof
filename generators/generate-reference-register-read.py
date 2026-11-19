"""Instantiate the shared RF read proof schema at the actual reference 32-way mux."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
s=(base/'RFReadPorts.v').read_text();s=s[:s.index('Definition rf_read_tail_nodes')]
s=s.replace('Require Import ConcreteDecodeOperations','Require Import ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1 RFReferenceNopIngress RFReferenceNopHistory RFReadPorts ReferenceRedirectSpine ConcreteDecodeOperations')
a=s.index('Definition rf_read_address_port');b=s.index('Definition rf_read_condition')
s=s[:a]+'''Definition rf_read_address_port : VarOrder.T := 2145.
Definition rf_read_stage (index:nat) : VarOrder.T := N.of_nat (Nat.add 2178 index).
'''+s[b:]
s=s.replace('second ','').replace(' second','')
s=s.replace('(N.of_nat (851+index)%nat)','(N.of_nat (Nat.sub 2177 index))').replace('(N.of_nat (851+S index)%nat)','(N.of_nat (Nat.sub 2177 (S index)))').replace('851','2177')
a=s.index('Proof.',s.index('Lemma rf_read_stage_member'));b=s.index('Qed.',a)+4
s=s[:a]+'''Proof.
 intro Bound. do 32 (destruct index as [|index];[apply (List.nth_error_In reference_control_0_nodes 0%nat)|]).
Qed.
'''+s[b:]
# actual member indices in the frozen node certificate list
nodes=(base/'ReferenceControlNodeCertificates0.v').read_text()
# use named congruence membership lemmas rather than reducing whole lists
start=s.index('Proof.',s.index('Lemma rf_read_stage_member'));end=s.index('Qed.',start)+4
proof='Proof. intro Bound.\n'+''.join(f' destruct index as [|index];[exact reference_control_member_{2178+i}|].\n' for i in range(32))+' lia. Qed.'
s=s[:start]+proof+s[end:]
s=s.replace('data_address_expected_nodes','reference_control_0_nodes').replace('data_address_node_offsets','reference_control_0_offsets').replace('data_address_actual_node_expressions','reference_control_0_positions').replace('data_address_actual_nodes_safe','reference_control_0_safety')
s=s.replace('List.In (rf_read_stage index,rf_read_stage_expr index) reference_control_0_nodes.', 'List.In (rf_read_stage index,rf_read_stage_expr index) (if Nat.ltb index 5 then reference_control_0_nodes else reference_control_1_nodes).')
helper=r"""Lemma rf_read_safe_position index : (index<32)%coq_nat -> exists count tail,
 straight_drop count flat_statements = Some (Qcons (Snode (rf_read_stage index) (rf_read_stage_expr index)) tail) /\
 formal_typed_suffix_safe flat_memories (rf_read_stage index) tail /\ has_register (rf_read_stage index) flat_statements = false.
Proof.
 intro Bound. pose proof (rf_read_stage_member index Bound) as Member.
 destruct (Nat.ltb index 5).
 - exact (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements reference_control_0_nodes _ _ reference_control_0_positions reference_control_0_safety Member).
 - exact (selected_node_safe_position flat_memories flat_statements reference_control_1_offsets flat_statements reference_control_1_nodes _ _ reference_control_1_positions reference_control_1_safety Member).
Qed.
"""
pos=s.index('Lemma rf_read_condition_value');s=s[:pos]+helper+s[pos:]
old='destruct (selected_node_safe_position flat_memories flat_statements reference_control_0_offsets flat_statements reference_control_0_nodes _ _ reference_control_0_positions reference_control_0_safety (rf_read_stage_member '
s=s.replace(old,'destruct (rf_read_safe_position ')
s=s.replace('0 ltac:(lia))) as','0 ltac:(lia)) as').replace('(S index) Bound)) as','(S index) Bound) as')
# shared primitive, not a duplicate
start=s.index('Lemma rf_read_mux_exact');end=s.index('Lemma rf_read_base_type',start);s=s[:start]+s[end:]
# history source is stable reference alias bank, already propagated two steps
s=s.replace('rf_dut_bank_at (history 0%nat) bank ->','(forall t index, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> (index < 32)%coq_nat -> size (bank index)=32%nat /\\ VM.find (N.of_nat (Nat.sub 2177 index)) (history t)=Some(Gval(Fuint 32)(bank index))) ->')
s=s.replace('rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) 0%nat ltac:(lia)','Bank time 0%nat ltac:(lia) ltac:(lia) ltac:(lia)')
s=s.replace('rf_dut_bank_history_hold _ history limit bank Bank Steps time ltac:(lia) (S index) Bound','Bank time (S index) ltac:(lia) ltac:(lia) Bound')
s=s.replace('(Bank (to_nat address) ltac:(lia))','(Bank time (to_nat address) ltac:(lia) ltac:(lia) ltac:(lia))')
s=s.replace('rf_read_mux_exact','SHARED_MUX_EXACT').replace('rf_read_', 'reference_bank_read_').replace('SHARED_MUX_EXACT','rf_read_mux_exact')
p=base/'ReferenceRegisterRead.v';mark='(* Reference bank and instruction bridge. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
