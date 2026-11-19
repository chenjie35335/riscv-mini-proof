from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'formal/flat-low/staged-integration/LoadAddressAlignment.v'
s='''Require Import CoreSocModel ComparisonNodes DUTRedirectReachability ReferenceRedirectSpine
 JointUpdateNodePositions JointUpdateExpressionCertificates ExceptionStabilityHistory
 JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem load_word_invalid_history inputs path history limit time b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 126 (history time) = Some (Gval (Fuint 3) [::true;false;false]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 418 (history time) = Some (Gval (Fuint 1) [::b0 || b1]).
Proof.
 intros Boundary Steps Lower Upper Mode Address.
 pose proof (Steps time Upper) as Step.
'''
rows=[(409,2,'[::b0;b1]',['Address']),(410,1,'[::b0 || b1]',['V409']),(411,1,'[::b0]',['Address']),(412,1,'[::b0]',['Address']),(413,1,'[::true]',['Mode']),(414,1,'[::b0 || b1]',['V413','V410']),(415,1,'[::false]',['Mode']),(416,1,'[::b0 || b1]',['V415','V411','V414']),(417,1,'[::false]',['Mode']),(418,1,'[::b0 || b1]',['V417','V412','V416'])]
for node,width,value,lookups in rows:
 s+=f''' assert (V{node} : VM.find {node} (history time) = Some (Gval (Fuint {width}) {value})).
 {{ rewrite (exception_stable_{node}_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {node} joint_update_expr_{node});
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes {node-161}%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite {' '.join(lookups)}. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite {' '.join('?' + x for x in lookups)}. destruct b0,b1,rest; reflexivity. }}
'''
s+=' exact V418.\nQed.\n'
s+='''Theorem load_word_aligned_history inputs path history limit time b0 b1 rest :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 126 (history time) = Some (Gval (Fuint 3) [::true;false;false]) ->
 VM.find 122 (history time) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 b0 = false /\\ b1 = false.
Proof.
 intros Boundary Steps Lower Upper NoTrap Mode Address.
 destruct (dut_no_trap_invalid_flags_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as [_ Zero].
 pose proof (load_word_invalid_history inputs path history limit time b0 b1 rest Boundary Steps Lower Upper Mode Address) as Invalid.
 specialize (Zero _ _ Invalid). cbn in Zero.
 apply Bool.orb_false_iff in Zero. exact Zero.
Qed.
'''

# Reuse the existing theorem signature and the same actual-node schema.
head=s[s.index('Theorem load_word_invalid_history'):s.index(' assert (V409')]
head=head.replace('load_word_invalid_history','load_half_invalid_history').replace('time b0 b1 rest :','time unsigned b0 b1 rest :').replace('[::true;false;false]','[::false;negb unsigned;unsigned]').replace('[::b0 || b1]','[::b0]')
s+=head
halfrows=[(409,2,'[::b0;b1]',['Address']),(410,1,'[::b0 || b1]',['V409']),(411,1,'[::b0]',['Address']),(412,1,'[::b0]',['Address']),(413,1,'[::false]',['Mode']),(414,1,'[::false]',['V413','V410']),(415,1,'[::negb unsigned]',['Mode']),(416,1,'[::b0 && negb unsigned]',['V415','V411','V414']),(417,1,'[::unsigned]',['Mode']),(418,1,'[::b0]',['V417','V412','V416'])]
for node,width,value,lookups in halfrows:
 s+=f''' assert (V{node} : VM.find {node} (history time) = Some (Gval (Fuint {width}) {value})).
 {{ rewrite (exception_stable_{node}_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {node} joint_update_expr_{node});
   [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes {node-161}%nat); vm_compute;reflexivity| |exact Step].
   intros site. cbn [joint_update_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
   rewrite {' '.join(lookups)}. unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite {' '.join('?' + x for x in lookups)}. destruct unsigned,b0,b1,rest; reflexivity. }}
'''
s+=' exact V418.\nQed.\n'

marker='(* Observed load alignment. *)'
if p.exists() and marker in p.read_text():
 s += '\n' + marker + p.read_text().split(marker,1)[1]
p.write_text(s)
