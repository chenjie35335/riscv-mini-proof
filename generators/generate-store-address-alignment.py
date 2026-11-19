"""Actual DUT word/halfword store alignment from existing NoTrap assumption."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
load=(base/'LoadAddressAlignment.v').read_text();dut=(base/'DUTRedirectReachability.v').read_text()
s=load[:load.index('Theorem load_word_invalid_history')]
s+='Require Import FormalExceptionInput JointUpdateConnectionCertificates FormalDeclaredConnection DUTRedirectDecode.\n'
a=dut.index('Theorem dut_no_trap_invalid_flags_history');b=dut.index('  as [Zero427 Zero425].',a)+len('  as [Zero427 Zero425].')
t=dut[a:b].replace('dut_no_trap_invalid_flags_history','dut_no_trap_store_invalid_history').replace('dut_node_low_zero 408 (history time) /\\ dut_node_low_zero 418 (history time).','dut_node_low_zero 425 (history time).')
s+=t+'\n exact Zero425.\nQed.\n'
a=load.index('Theorem load_word_invalid_history');b=load.index(' assert (V409',a)
t=load[a:b].replace('load_word_invalid_history','store_invalid_history').replace('time b0 b1 rest :','time half b0 b1 rest :').replace('VM.find 126','VM.find 125').replace('Fuint 3)','Fuint 2)').replace('[::true;false;false]','[::negb half;half]').replace('VM.find 418','VM.find 425').replace('[::b0 || b1]','[::b0 || (b1 && negb half)]')
s+=t
rows=[(419,2,'[::b0;b1]',['Address']),(420,1,'[::b0 || b1]',['V419']),(421,1,'[::b0]',['Address']),(422,1,'[::negb half]',['Mode']),(423,1,'[::(b0 || b1) && negb half]',['V422','V420']),(424,1,'[::half]',['Mode']),(425,1,'[::b0 || (b1 && negb half)]',['V424','V421','V423'])]
for node,width,value,lookups in rows:
 s+=f''' assert (V{node} : VM.find {node} (history time) = Some (Gval (Fuint {width}) {value})).
 {{ rewrite (exception_stable_{node}_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {node} joint_update_expr_{node});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes {node-161}%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite {' '.join(lookups)}. unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite {' '.join('?'+v for v in lookups)}. destruct half,b0,b1,rest;reflexivity. }}
'''
s+=' exact V425.\nQed.\n'
s+='''Theorem store_aligned_history inputs path history limit time half b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 125 (history time) = Some (Gval (Fuint 2) [::negb half;half]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\\ (half = false -> b1 = false).
Proof.
 intros Boundary Steps Lower Upper NoTrap Mode Address.
 pose proof (dut_no_trap_store_invalid_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as Zero.
 pose proof (store_invalid_history inputs path history limit time half b0 b1 rest Boundary Steps Lower Upper Mode Address) as Invalid.
 specialize (Zero _ _ Invalid). cbn in Zero. destruct half,b0,b1;cbn in Zero;try discriminate;auto.
Qed.
'''
p=base/'StoreAddressAlignment.v';mark='(* Observed store alignment. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
