from pathlib import Path
import re
ROOT = Path(__file__).resolve().parents[2]
static = r'''Require Import ReferenceRedirectSpine ReferenceRedirectSemantics ReferenceControlGroundExpressions JointUpdateExpressionCertificates JointUpdateNodePositions JointUpdateConnectionCertificates EarlyControlStabilityHistory FetchPCSelectorStability JointBoundaryRegisters ConcreteRegisterInitialization FormalDeclaredConnection CoreSocModel ComparisonNodes.
From Coq Require Import NArith ZArith Lia List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBitsDef NBitsOp.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma dut_from_Zneg_inv n z : from_Zneg n z = invB (from_Zpos n z).
Proof.
 revert z. induction n as [|n IH]; intro z; [reflexivity|].
 cbn [from_Zneg from_Zpos invB]. rewrite IH.
 rewrite <- Z.negb_odd. reflexivity.
Qed.
Lemma dut_from_Z33_value z :
 (-4294967296 < z < 4294967296)%Z ->
 to_Zpos (from_Z 33 z) = (if Z.ltb z 0 then 8589934592 + z else z)%Z.
Proof.
 intro Bounds. destruct z as [|p|p].
 - reflexivity.
 - change (to_Zpos (from_Zpos 33 (Z.pos p)) = Z.pos p).
   rewrite to_Zpos_from_Zpos_bounded; [reflexivity|lia|change (Z.pos p < 8589934592)%Z; lia].
 - change (-4294967296 < - Z.pos p < 4294967296)%Z in Bounds.
   change (to_Zpos (from_Zneg 33 (Z.pred (Z.pos p))) = (8589934592 - Z.pos p)%Z).
   rewrite dut_from_Zneg_inv to_Zpos_invB_full size_from_Zpos.
   rewrite to_Zpos_from_Zpos_bounded; change (2 ^ Z.of_nat 33)%Z with 8589934592%Z; unfold Z.one; lia.
Qed.
Definition dut_branch_difference left right :=
 take 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z).
Lemma dut_branch_difference_subB left right :
 size left = 32%nat -> size right = 32%nat ->
 dut_branch_difference left right = subB left right.
Proof.
 intros LeftSize RightSize.
 assert (SameSize : size left = size right) by lia.
 assert (Bound : (-4294967296 < to_Zpos left - to_Zpos right < 4294967296)%Z).
 { pose proof (to_Zpos_bounded left) as L. pose proof (to_Zpos_bounded right) as R.
   pose proof (@to_Zpos_ge0 left). pose proof (@to_Zpos_ge0 right).
   rewrite LeftSize in L. rewrite RightSize in R.
   change (to_Zpos left < 4294967296)%Z in L.
   change (to_Zpos right < 4294967296)%Z in R. lia. }
 apply to_Zpos_inj_ss.
 - unfold dut_branch_difference. rewrite size_take size_from_Z size_subB LeftSize RightSize. reflexivity.
 - unfold dut_branch_difference.
   replace (take 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z)) with
    (low 32 (from_Z 33 (to_Zpos left - to_Zpos right)%Z)).
   2: { unfold low. rewrite size_from_Z. change (32 - 33)%nat with 0%nat. rewrite zeros0 cats0. reflexivity. }
   rewrite <- to_Zpos_mod_pow2.
   rewrite (dut_from_Z33_value _ Bound) (to_Zpos_subB' SameSize) LeftSize.
   change ((if Z.ltb (to_Zpos left - to_Zpos right) 0 then 8589934592 + (to_Zpos left - to_Zpos right) else to_Zpos left - to_Zpos right) mod 4294967296 = (to_Zpos left - to_Zpos right) mod 4294967296)%Z.
   destruct (Z.ltb (to_Zpos left - to_Zpos right) 0); [|reflexivity].
   replace (8589934592 + (to_Zpos left - to_Zpos right))%Z with
    ((to_Zpos left - to_Zpos right) + 2 * 4294967296)%Z by ring.
   rewrite Z.mod_add; [reflexivity|discriminate].
Qed.
Lemma dut_unsigned_compare left right :
 size left = size right ->
 (if msb left == msb right then msb (subB left right) else msb right) =
 N.ltb (to_N left) (to_N right).
Proof.
 intro SameSize. rewrite <- to_N_ltB_eqn.
 rewrite (ltB_equiv_borrow_subB SameSize) (borrow_subB_eq_msbs SameSize).
 destruct (msb left), (msb right), (msb (subB left right)); reflexivity.
Qed.
Lemma dut_signed_compare left right :
 size left = size right ->
 (if msb left == msb right then msb (subB left right) else msb left) =
 Z.ltb (to_Z left) (to_Z right).
Proof.
 intro SameSize. rewrite <- (to_Z_sltB_eqn SameSize).
 destruct (msb left == msb right) eqn:Same.
 - rewrite <- (ltB_sltB_same SameSize Same), to_N_ltB_eqn.
   pose proof (dut_unsigned_compare left right SameSize) as U. rewrite Same in U. exact U.
 - unfold sltB, msb.
   destruct (splitmsb left) as [lt ls] eqn:L.
   destruct (splitmsb right) as [rt rs] eqn:R.
   unfold msb in Same. rewrite L R in Same. cbn in Same.
   destruct ls, rs; try discriminate Same; reflexivity.
Qed.
Lemma dut_sub_zero left right :
 size left = size right -> is_zero (subB left right) = (left == right).
Proof.
 intro SameSize. destruct (eqP : reflect (left = right) (left == right)) as [Equal|Different].
 - subst right. rewrite subB_same. exact (zeros_is_zero (size left)).
 - destruct (is_zero (subB left right)) eqn:Zero; [|reflexivity].
   exfalso. apply Different. apply (to_Zpos_inj_ss SameSize).
   pose proof (is_zero_to_Zpos Zero) as V.
   rewrite (to_Zpos_subB SameSize) in V.
   pose proof (to_Zpos_bounded left) as L. pose proof (to_Zpos_bounded right) as R.
   pose proof (@to_Zpos_ge0 left). pose proof (@to_Zpos_ge0 right).
   rewrite <- SameSize in R.
   destruct (borrow_subB left right); cbn [Z.b2z] in V; lia.
Qed.
Lemma dut_eq_numeric left right :
 size left = size right ->
 is_zero (subB left right) = N.eqb (to_N left) (to_N right).
Proof.
 intro SameSize. rewrite (dut_sub_zero left right SameSize).
 destruct (eqP : reflect (left = right) (left == right)) as [Equal|Different].
 - subst right. rewrite N.eqb_refl. reflexivity.
 - symmetry. apply N.eqb_neq. intro Equal. apply Different.
   apply (to_Zpos_inj_ss SameSize). rewrite !to_Zpos_N Equal. reflexivity.
Qed.
Lemma dut_reduction_or bits : foldr orb false bits = negb (is_zero bits).
Proof.
 induction bits as [|bit bits IH]; [reflexivity|].
 cbn [foldr]. rewrite is_zero_cons IH. destruct bit; reflexivity.
Qed.
Lemma dut_sign_extract bits : size bits = 32%nat ->
 drop 31 (take 32 bits) = [::msb bits].
Proof.
 intro Size. rewrite <- Size at 1. rewrite take_size.
 rewrite (drop_nth false); [|rewrite Size; reflexivity].
 change (nth false bits 31 :: drop 32 bits = [::msb bits]).
 rewrite <- Size at 1. rewrite drop_size. f_equal.
 replace 31%nat with (size bits).-1 by (rewrite Size; reflexivity).
 rewrite nth_last. unfold msb, splitmsb, split_last, lastd. destruct bits; reflexivity.
Qed.
Definition dut_branch_bit_function kind left right :=
 let unequal := foldr orb false (subB left right) in
 let same_sign := msb left == msb right in
 let signed_lt := if same_sign then msb (subB left right) else msb left in
 let unsigned_lt := if same_sign then msb (subB left right) else msb right in
 (N.eqb kind 3 && negb unequal) || (N.eqb kind 6 && unequal) ||
 (N.eqb kind 2 && signed_lt) || (N.eqb kind 5 && negb signed_lt) ||
 (N.eqb kind 1 && unsigned_lt) || (N.eqb kind 4 && negb unsigned_lt).
Definition dut_branch_function kind left right :=
 (N.eqb kind 3 && N.eqb left right) || (N.eqb kind 6 && negb (N.eqb left right)) ||
 (N.eqb kind 2 && Z.ltb (reference_redirect_signed left) (reference_redirect_signed right)) ||
 (N.eqb kind 5 && Z.leb (reference_redirect_signed right) (reference_redirect_signed left)) ||
 (N.eqb kind 1 && N.ltb left right) || (N.eqb kind 4 && N.leb right left).
Definition dut_redirect_function selector kind left right :=
 N.eqb selector 1 || dut_branch_function kind left right.
Lemma dut_branch_numeric kind left right :
 size left = 32%nat -> size right = 32%nat ->
 dut_branch_bit_function kind left right = dut_branch_function kind (to_N left) (to_N right).
Proof.
 intros LeftSize RightSize. assert (SameSize : size left = size right) by lia.
 unfold dut_branch_bit_function, dut_branch_function.
 rewrite dut_reduction_or negbK (dut_eq_numeric left right SameSize).
 rewrite (dut_signed_compare left right SameSize) (dut_unsigned_compare left right SameSize).
 rewrite (reference_redirect_signed32 left LeftSize) (reference_redirect_signed32 right RightSize).
 rewrite N.leb_antisym Z.leb_antisym. reflexivity.
Qed.
Lemma dut_boolean_binop op a b :
 eval_binop op (Gval (Fuint 1) [::a]) (Gval (Fuint 1) [::b]) =
 match op with
 | Band => Some (Gval (Fuint 1) [::a && b])
 | Bor => Some (Gval (Fuint 1) [::a || b])
 | Bcomp Beq => Some (Gval (Fuint 1) [::a == b])
 | _ => eval_binop op (Gval (Fuint 1) [::a]) (Gval (Fuint 1) [::b])
 end.
Proof. destruct op; try match goal with c : bcmp |- _ => destruct c end; destruct a,b; reflexivity. Qed.
'''
source=(ROOT/'formal/flat-low/staged-integration/JointUpdateExpressionCertificates.v').read_text()
expressions={int(n):expr for n,expr in re.findall(r'Definition joint_update_expr_(\d+) : hfexpr VarOrder.T := (.*)\.',source)}
node_ids=[int(x) for x in re.findall(r'\((\d+),joint_update_expr_\d+\)',(ROOT/'formal/flat-low/staged-integration/JointUpdateNodePositions.v').read_text())]
# The expected-node table is declared with the expression certificates.
if not node_ids: node_ids=[int(x) for x in re.findall(r'\((\d+),joint_update_expr_\d+\)',source)]
values={1357:('32','left'),1358:('32','right'),1359:('3','kind')}
booleans={}
for n in range(1361,1393):
 if n==1361: values[n]=('33','(from_Z 33 (to_Zpos left - to_Zpos right)%Z)')
 elif n==1362: values[n]=('32','(subB left right)')
 else:
  expr=expressions[n];deps=[int(d) for d in re.findall(r'@Eid VarOrder.T (\d+)',expr)]
  if n==1363: bit='foldr orb false (subB left right)'
  elif n in [1365,1369]: bit='msb left'
  elif n in [1366,1372]: bit='msb right'
  elif n in [1368,1371]: bit='msb (subB left right)'
  elif n in [1364,1374,1375]: bit=f'negb v{deps[0]}'
  elif n==1367: bit='v1365 == v1366'
  elif 'Emux' in expr: bit=f'if v{deps[0]} then v{deps[1]} else v{deps[2]}'
  elif len(deps)==1:
   const=re.search(r'\[::([^]]*)\]',expr)[1]
   number=sum((x=='true')<<i for i,x in enumerate(re.findall('true|false',const)))
   bit=f'N.eqb (to_N kind) {number}'
  else: bit=f'v{deps[0]} '+('&&' if ' Band ' in expr else '||')+f' v{deps[1]}'
  booleans[n]=bit;values[n]=('1',f'[::v{n}]')
lines=['''Theorem dut_branch_history inputs path history limit time left right kind :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1357 (history time) = Some (Gval (Fuint 32) left) ->
 VM.find 1358 (history time) = Some (Gval (Fuint 32) right) ->
 VM.find 1359 (history time) = Some (Gval (Fuint 3) kind) ->
 size left = 32%nat -> size right = 32%nat ->
 VM.find 1392 (history time) = Some (Gval (Fuint 1) [::dut_branch_function (to_N kind) (to_N left) (to_N right)]).
Proof.
 intros Boundary Steps Lower Upper H1357 H1358 H1359 LeftSize RightSize.
 pose proof (Steps time Upper) as Step.
 assert (DiffSize : size (subB left right) = 32%nat) by (rewrite size_subB LeftSize RightSize; reflexivity).''']
for n in range(1361,1393):
 expr=expressions[n];deps=[int(d) for d in re.findall(r'@Eid VarOrder.T (\d+)',expr)]
 if n in booleans: lines += [f' set v{n} := ({booleans[n]}).']
 width,bits=values[n]
 lines += [f' assert (H{n} : VM.find {n} (history (S time)) = Some (Gval (Fuint {width}) {bits})).',
 f' {{ eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {n} joint_update_expr_{n});',
 f' [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes {node_ids.index(n)}%nat); vm_compute; reflexivity| |exact Step].',
 f' intros site. unfold joint_update_expr_{n}. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].',
 ' rewrite '+' '.join('H'+str(d) for d in deps)+'.']
 if n==1361 or n==1363: lines+=[' reflexivity. }']
 elif n==1362: lines += [' change (Some (Gval (Fuint 32) (dut_branch_difference left right)) = Some (Gval (Fuint 32) (subB left right))). rewrite (dut_branch_difference_subB left right LeftSize RightSize). reflexivity. }']
 elif n in [1365,1366,1368,1369,1371,1372]:
  word='left' if n in [1365,1369] else 'right' if n in [1366,1372] else '(subB left right)'
  size='LeftSize' if word=='left' else 'RightSize' if word=='right' else 'DiffSize'
  lines += [f' change (Some (Gval (Fuint 1) (drop 31 (take 32 {word}))) = Some (Gval (Fuint 1) [::v{n}])). rewrite (dut_sign_extract {word} {size}). reflexivity. }}']
 elif n in [1370,1373]:
  lines += [' unfold eval_type_of_expr. cbn [type_of_expr\' eval_type_of_ref]. rewrite '+' '.join('H'+str(d) for d in deps[1:])+'.',f' unfold v{n}. destruct '+', '.join('v'+str(d) for d in deps)+'; reflexivity. }']
 elif len(deps)==1 and n not in [1364,1374,1375]:
  number=re.search(r'N.eqb \(to_N kind\) (\d+)',booleans[n])[1]
  lines += [f' unfold v{n}. change (Some (Gval (Fuint 1) [::to_N kind == {number}]) = Some (Gval (Fuint 1) [::N.eqb (to_N kind) {number}])). rewrite redirect_N_eqb. reflexivity. }}']
 else:
  if n in [1364,1374,1375]:lines += [f' change (eval_binop (Bcomp Beq) (Gval (Fuint 1) [::v{deps[0]}]) (Gval (Fuint 1) [::false]) = Some (Gval (Fuint 1) [::v{n}])).']
  lines += [' rewrite dut_boolean_binop.',f' unfold v{n}. destruct '+', '.join('v'+str(d) for d in deps)+'; reflexivity. }']
 lines += [f' rewrite <- (early_control_stable_{n}_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H{n}.']
lines += [' rewrite H1392. rewrite <- (dut_branch_numeric (to_N kind) left right LeftSize RightSize).',
 ' unfold dut_branch_bit_function. subst '+' '.join('v'+str(n) for n in reversed(booleans))+'. reflexivity.','Qed.']
(ROOT/'formal/flat-low/staged-integration/DUTRedirectSemantics.v').write_text(static+'\n'+'\n'.join(lines)+'\n')
redirect = r'''
Theorem dut_redirect_history inputs path history limit time left right kind selector :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1357 (history time) = Some (Gval (Fuint 32) left) ->
 VM.find 1358 (history time) = Some (Gval (Fuint 32) right) ->
 VM.find 1359 (history time) = Some (Gval (Fuint 3) kind) ->
 VM.find 84 (history time) = Some (Gval (Fuint 2) selector) ->
 size left = 32%nat -> size right = 32%nat ->
 VM.find 7773 (history time) = Some (Gval (Fuint 1)
 [::dut_redirect_function (to_N selector) (to_N kind) (to_N left) (to_N right)]).
Proof.
 intros Boundary Steps Lower Upper Left Right Kind Selector LeftSize RightSize.
 pose proof (Steps time Upper) as Step.
 pose proof (dut_branch_history inputs path history limit time left right kind Boundary Steps Lower Upper Left Right Kind LeftSize RightSize) as Branch.
 set taken := dut_branch_function (to_N kind) (to_N left) (to_N right) in Branch.
 assert (H1360 : VM.find 1360 (history (S time)) = Some (Gval (Fuint 1) [::taken])).
 { eapply (declared_connection_value 1438 flat_statements joint_update_connection_1360_decl joint_update_connection_1360_mid joint_update_connection_1360_tail 1360 1392 1 (Gval (Fuint 1) [::taken]));
 [exact joint_update_connection_1360_position|exact joint_update_connection_1360_split|exact joint_update_connection_1360_straight|exact joint_update_connection_1360_mid_safe|exact joint_update_connection_1360_tail_safe|exact joint_update_connection_1360_nonregister|reflexivity|exact Branch|destruct taken; reflexivity|exact Step]. }
 rewrite <- (early_control_stable_1360_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1360.
 assert (H7772 : VM.find 7772 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (to_N selector) 1])).
 { eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7772 joint_update_expr_7772);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes INDEX7772%nat); vm_compute; reflexivity| |exact Step].
 intros site. unfold joint_update_expr_7772. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Selector.
 change (Some (Gval (Fuint 1) [::to_N selector == 1]) = Some (Gval (Fuint 1) [::N.eqb (to_N selector) 1])). rewrite redirect_N_eqb. reflexivity. }
 rewrite <- (fetch_pc_selector_7772_same inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H7772.
 rewrite (fetch_pc_selector_7773_same inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 7773 joint_update_expr_7773);
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes INDEX7773%nat); vm_compute; reflexivity| |exact Step].
 intros site. unfold joint_update_expr_7773. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H7772 H1360.
 rewrite dut_boolean_binop. reflexivity.
Qed.
'''
redirect=redirect.replace('INDEX7772',str(node_ids.index(7772))).replace('INDEX7773',str(node_ids.index(7773)))
with (ROOT/'formal/flat-low/staged-integration/DUTRedirectSemantics.v').open('a') as output:
 output.write(redirect)

correspondence = r'''
From Coq Require Import btauto.Btauto.
Definition dut_operand_tests_match kind dut_left dut_right ref_left ref_right : Prop :=
 ((N.eqb kind 3 || N.eqb kind 6) = true -> N.eqb dut_left dut_right = N.eqb ref_left ref_right) /\
 ((N.eqb kind 2 || N.eqb kind 5) = true ->
  Z.ltb (reference_redirect_signed dut_left) (reference_redirect_signed dut_right) =
  Z.ltb (reference_redirect_signed ref_left) (reference_redirect_signed ref_right)) /\
 ((N.eqb kind 1 || N.eqb kind 4) = true -> N.ltb dut_left dut_right = N.ltb ref_left ref_right).
Lemma dut_operand_tests_branch kind dut_left dut_right ref_left ref_right :
 dut_operand_tests_match kind dut_left dut_right ref_left ref_right ->
 dut_branch_function kind dut_left dut_right = dut_branch_function kind ref_left ref_right.
Proof.
 unfold dut_operand_tests_match, dut_branch_function.
 intros [Eq [Signed Unsigned]]. rewrite !N.leb_antisym !Z.leb_antisym.
 destruct (N.eqb kind 3), (N.eqb kind 6), (N.eqb kind 2), (N.eqb kind 5), (N.eqb kind 1), (N.eqb kind 4);
 cbn [orb] in Eq, Signed, Unsigned;
 try specialize (Eq (Logic.eq_refl true)); try specialize (Signed (Logic.eq_refl true)); try specialize (Unsigned (Logic.eq_refl true));
 cbn [andb orb]; congruence.
Qed.
Definition dut_redirect_controls_match instruction selector kind : Prop :=
 let code := N.land instruction 28799 in
 (N.eqb kind 3 = N.eqb code 99) /\
 (N.eqb kind 6 = N.eqb code 4195) /\
 (N.eqb kind 2 = N.eqb code 16483) /\
 (N.eqb kind 5 = N.eqb code 20579) /\
 (N.eqb kind 1 = N.eqb code 24675) /\
 (N.eqb kind 4 = N.eqb code 28771) /\
 (N.eqb selector 1 = (N.eqb (N.land instruction 127) 111 || N.eqb code 103)).
Definition dut_reference_taken instruction left right :=
 let code := N.land instruction 28799 in
 (N.eqb code 99 && N.eqb left right) || (N.eqb code 4195 && negb (N.eqb left right)) ||
 (N.eqb code 16483 && Z.ltb (reference_redirect_signed left) (reference_redirect_signed right)) ||
 (N.eqb code 20579 && Z.leb (reference_redirect_signed right) (reference_redirect_signed left)) ||
 (N.eqb code 24675 && N.ltb left right) || (N.eqb code 28771 && N.leb right left) ||
 N.eqb (N.land instruction 127) 111.
Lemma dut_redirect_decode instruction selector kind left right :
 dut_redirect_controls_match instruction selector kind ->
 dut_redirect_function selector kind left right =
 (dut_reference_taken instruction left right || N.eqb (N.land instruction 28799) 103).
Proof.
 unfold dut_redirect_controls_match, dut_redirect_function, dut_branch_function, dut_reference_taken.
 intros [Eq [Ne [Lt [Ge [Ltu [Geu Jump]]]]]].
 rewrite Eq Ne Lt Ge Ltu Geu Jump. btauto.
Qed.
Lemma dut_reference_alignment instruction left right immediate pc csr :
 reference_redirect_function instruction left right immediate pc csr =
 (dut_reference_taken instruction left right && reference_redirect_aligned (N.testbit csr 2) (pc + immediate)) ||
 (N.eqb (N.land instruction 28799) 103 && reference_redirect_aligned (N.testbit csr 2) (N.clearbit (left + immediate) 0)).
Proof. unfold reference_redirect_function, dut_reference_taken. btauto. Qed.
Lemma dut_redirect_gate a b aligned_a aligned_b :
 (a = true -> aligned_a = true) -> (b = true -> aligned_b = true) ->
 (a || b) = ((a && aligned_a) || (b && aligned_b)).
Proof. destruct a,b,aligned_a,aligned_b; intros A B; try reflexivity; try (specialize (A (Logic.eq_refl true)); discriminate A); try (specialize (B (Logic.eq_refl true)); discriminate B). Qed.
Theorem dut_redirect_reference instruction selector kind dut_left dut_right ref_left ref_right immediate pc csr :
 dut_redirect_controls_match instruction selector kind ->
 dut_operand_tests_match kind dut_left dut_right ref_left ref_right ->
 (dut_reference_taken instruction ref_left ref_right = true ->
  reference_redirect_aligned (N.testbit csr 2) (pc + immediate) = true) ->
 (N.eqb (N.land instruction 28799) 103 = true ->
  reference_redirect_aligned (N.testbit csr 2) (N.clearbit (ref_left + immediate) 0) = true) ->
 dut_redirect_function selector kind dut_left dut_right =
 reference_redirect_function instruction ref_left ref_right immediate pc csr.
Proof.
 intros Controls Operands BranchAligned JalrAligned.
 unfold dut_redirect_function at 1.
 rewrite (dut_operand_tests_branch kind dut_left dut_right ref_left ref_right Operands).
 change (dut_redirect_function selector kind ref_left ref_right = reference_redirect_function instruction ref_left ref_right immediate pc csr).
 rewrite (dut_redirect_decode instruction selector kind ref_left ref_right Controls) dut_reference_alignment.
 apply dut_redirect_gate; assumption.
Qed.
'''
with (ROOT/'formal/flat-low/staged-integration/DUTRedirectSemantics.v').open('a') as output:
 output.write(correspondence)
observed=r'''
Require Import FormalLocalHistory StagedIterationCount JointBoundaryReachable JointBoundaryPreparation FormalFetchType.
Theorem dut_redirect_observed memory inputs k observed left right kind selector :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) left) ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) right) ->
 VM.find 1359 (top_environment observed) = Some (Gval (Fuint 3) kind) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) selector) ->
 size left = 32%nat -> size right = 32%nat ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1)
 [::dut_redirect_function (to_N selector) (to_N kind) (to_N left) (to_N right)]).
Proof.
 intros Observe Legal Left Right Kind Selector LeftSize RightSize.
 unfold generated_observe, generated_observe_cycle in Observe.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
  (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial observed Observe)
 as [history [First [Last Steps]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 rewrite <- Last.
 rewrite <- (fetch_pc_selector_7773_same (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 eapply (dut_redirect_history (generated_observation_input inputs k) nil history 9259 9258 left right kind selector Boundary Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)); try assumption.
 - rewrite (early_control_stable_1357_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Left.
 - rewrite (early_control_stable_1358_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Right.
 - rewrite (early_control_stable_1359_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Kind.
 - destruct (fetch_pc_decode_same_history (generated_observation_input inputs k) nil history 9259 Boundary Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [word [Before After]].
   rewrite Last Selector in After. rewrite Before. symmetry. exact After.
Qed.
'''
with (ROOT/'formal/flat-low/staged-integration/DUTRedirectSemantics.v').open('a') as output:
 output.write(observed)
comparison=r'''
(* Only the selected branch comparison must agree.  The immediate is used only
   by the two conditional target-alignment obligations below.  The raw DUT
   selector has no alignment gate, so these obligations cannot be omitted. *)
Theorem dut_reference_redirect_observed memory inputs k observed
 instruction dut_left dut_right kind selector ref_left ref_right immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1357 (top_environment observed) = Some (Gval (Fuint 32) dut_left) ->
 VM.find 1358 (top_environment observed) = Some (Gval (Fuint 32) dut_right) ->
 VM.find 1359 (top_environment observed) = Some (Gval (Fuint 3) kind) ->
 VM.find 84 (top_environment observed) = Some (Gval (Fuint 2) selector) ->
 VM.find 1884 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) ref_left) ->
 VM.find 2804 (top_environment observed) = Some (Gval (Fuint 32) ref_right) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment observed) = Some (Gval (Fuint 32) csr) ->
 size dut_left = 32%nat -> size dut_right = 32%nat ->
 size ref_left = 32%nat -> size ref_right = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 dut_redirect_controls_match (to_N instruction) (to_N selector) (to_N kind) ->
 dut_operand_tests_match (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) ->
 (dut_reference_taken (to_N instruction) (to_N ref_left) (to_N ref_right) = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate) = true) ->
 (N.eqb (N.land (to_N instruction) 28799) 103 = true ->
  reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N ref_left + to_N immediate) 0) = true) ->
 VM.find 7773 (top_environment observed) = VM.find 6507 (top_environment observed).
Proof.
 intros Observe Legal DutLeft DutRight Kind Selector Instruction RefLeft RefRight Immediate Pc Csr
 DutLeftSize DutRightSize RefLeftSize RefRightSize PcSize CsrSize Controls Operands BranchAligned JalrAligned.
 rewrite (dut_redirect_observed memory inputs k observed dut_left dut_right kind selector Observe Legal DutLeft DutRight Kind Selector DutLeftSize DutRightSize).
 rewrite (reference_redirect_function_observed memory inputs k observed instruction ref_left ref_right immediate pc csr Observe Legal Instruction RefLeft RefRight Immediate Pc Csr RefLeftSize RefRightSize PcSize CsrSize).
 rewrite (dut_redirect_reference (to_N instruction) (to_N selector) (to_N kind) (to_N dut_left) (to_N dut_right) (to_N ref_left) (to_N ref_right) (to_N immediate) (to_N pc) (to_N csr) Controls Operands BranchAligned JalrAligned).
 reflexivity.
Qed.
'''
with (ROOT/'formal/flat-low/staged-integration/DUTRedirectSemantics.v').open('a') as output:
 output.write(comparison)
