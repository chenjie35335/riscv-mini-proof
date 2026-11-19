import json,re
from pathlib import Path
REPO_ROOT = Path(__file__).resolve().parents[2]
rows={x['id']:x for x in json.load((REPO_ROOT / 'formal/flat-low/reference-control-stability-plan.json').open())['nodes']}
nodes=[6314,6325,6346,6359,6373,6377,6387,6397,6401,6411,6421,6425,6435,6445,6449,6459,6469,6473,6483,6493,6497,6507]
out=['''Require Import CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3 FormalGroundNodeEquation SelectedNodeSafety.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
''']
out += [r"""
Lemma reference_redirect_mux_step node expression condition yes no invalid old current result c y n :
 List.In (node, expression) reference_control_3_nodes ->
 expression = @Emux VarOrder.T condition yes no ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories condition old old = Some (Gval (Fuint 1) [::c])) ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories yes old old = Some (Gval (Fuint 1) [::y])) ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories no old old = Some (Gval (Fuint 1) [::n])) ->
 eval_type_of_expr yes old = Some (Gtyp (Fuint 1)) ->
 eval_type_of_expr no old = Some (Gtyp (Fuint 1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 1) [::if c then y else n]).
Proof.
 intros Member Expression Condition Yes No YesType NoType Step.
 destruct (selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements
 reference_control_3_nodes node expression reference_control_3_positions reference_control_3_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply (formal_combinational_known_ground_node count flat_statements tail node expression (Fuint 1)); [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 rewrite Expression. cbn [eval_hfexpr_validif_policy]. rewrite Condition.
 destruct c; cbn; [rewrite Yes NoType|rewrite No YesType]; destruct y, n; reflexivity.
Qed.
"""]
(REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').write_text('\n'.join(out))
guards=sorted({d for n in nodes for d in rows[n]['dependencies']} - set(nodes))
val={g:'b'+str(g) for g in guards}
lines=['''Require Import ReferenceRedirectSpine ReferenceControlStabilityHistory ReferenceControlExpressions ReferenceControlNodeCongruence3.
From Coq Require Import ZArith Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Require Import CoreSocModel ComparisonNodes.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Six-input branch/jump specification.  Immediate decoding is a separate interface.
   Inputs are unsigned numerical representations of 32-bit words. *)
Definition reference_redirect_aligned compressed target :=
 N.eqb (N.land target (if compressed then 1 else 3)) 0.
Definition reference_redirect_signed word :=
 if N.testbit word 31 then (Z.of_N word - 4294967296)%Z else Z.of_N word.
Definition reference_redirect_function instruction rs1 rs2 immediate pc csr : bool :=
 let code := N.land instruction 28799 in
 let compressed := N.testbit csr 2 in
 let aligned := reference_redirect_aligned compressed (pc + immediate) in
 let taken :=
 (N.eqb code 28771 && N.leb rs2 rs1) ||
 (N.eqb code 20579 && Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1)) ||
 (N.eqb code 24675 && N.ltb rs1 rs2) ||
 (N.eqb code 16483 && Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2)) ||
 (N.eqb code 4195 && negb (N.eqb rs1 rs2)) ||
 (N.eqb code 99 && N.eqb rs1 rs2) || N.eqb (N.land instruction 127) 111 in
 (taken && aligned) ||
 (N.eqb code 103 && reference_redirect_aligned compressed (N.clearbit (rs1 + immediate) 0)).
''']
# Boolean guard function preserves separate per-instruction alignment guards until normalized.
clauses=[[1974,2806,2825],[1980,2830,2847],[1986,2850,2867],[1992,2872,2889],[1998,2892,2909],[2004,2912,2929],[2010,2949],[2357,2966]]
canonical=' || '.join('('+' && '.join('b'+str(x) for x in c)+')' for c in clauses)
lines += ['Definition reference_redirect_guards '+' '.join('(b'+str(g)+' : bool)' for g in guards)+' := '+canonical+'.',
'Theorem reference_redirect_spine_history inputs path history limit reset time '+' '.join('b'+str(g) for g in guards)+' :',
' (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->',
' (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->',
' (127 <= time)%coq_nat -> (time < limit)%coq_nat ->']
lines += [f' VM.find {g} (history time) = Some (Gval (Fuint 1) [::b{g}]) ->' for g in guards]
lines += [' VM.find 6507 (history time) = Some (Gval (Fuint 1) [::reference_redirect_guards '+' '.join('b'+str(g) for g in guards)+']).',
'Proof.', ' intros Resets Steps Lower Upper '+' '.join('H'+str(g) for g in guards)+'.',' pose proof (Steps time Upper) as Step.']
for n in nodes:
 atoms=re.findall(r'\(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)|\(@Econst VarOrder.T \(Fuint 1\) \[::(true|false)\]\)',rows[n]['expression'])
 ts=[val[int(a)] if a else b for a,b in atoms];val[n]='b'+str(n); lines += [f' set b{n} := (if {ts[0]} then {ts[1]} else {ts[2]}).']
 ds=rows[n]['dependencies']
 atomexpr=[f'(@Eref VarOrder.T (@Eid VarOrder.T {a}))' if a else f'(@Econst VarOrder.T (Fuint 1) [::{b}])' for a,b in atoms]
 lines += [f' assert (H{n} : VM.find {n} (history (S time)) = Some (Gval (Fuint 1) [::b{n}])).',
 ' { eapply (reference_redirect_mux_step '+str(n)+' reference_control_expr_'+str(n)+' '+' '.join(atomexpr)+' (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) '+' '.join(ts)+');',
 f' [exact reference_control_member_{n}|reflexivity| | | | | |exact Step];',
 " try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }",
 f' rewrite <- (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H{n}.']
lines+=[' rewrite H6507. f_equal. f_equal. f_equal. unfold reference_redirect_guards in *. subst b6507 b6497 b6493 b6483 b6473 b6469 b6459 b6449 b6445 b6435 b6425 b6421 b6411 b6401 b6397 b6387 b6377 b6373 b6359 b6346 b6325 b6314. btauto.','Qed.']
(REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').write_text('\n'.join(lines)+'\n')

# Normalize all eight instruction clusters to the six-input arithmetic interface.
# Keep this separate from the circuit-value obligations: this lemma alone does
# not assert that any intermediate wire has its intended arithmetic value.
normal = r'''
Lemma reference_redirect_guards_normalize instruction rs1 rs2 immediate pc csr :
 reference_redirect_guards
  (N.eqb (N.land instruction 28799) 28771)
  (N.eqb (N.land instruction 28799) 20579)
  (N.eqb (N.land instruction 28799) 24675)
  (N.eqb (N.land instruction 28799) 16483)
  (N.eqb (N.land instruction 28799) 4195)
  (N.eqb (N.land instruction 28799) 99)
  (N.eqb (N.land instruction 28799) 103)
  (N.eqb (N.land instruction 127) 111)
  (N.leb rs2 rs1)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.ltb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (negb (N.eqb rs1 rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.eqb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (reference_redirect_aligned (N.testbit csr 2) (N.clearbit (rs1 + immediate) 0))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate)) =
 reference_redirect_function instruction rs1 rs2 immediate pc csr.
Proof. unfold reference_redirect_guards, reference_redirect_function. btauto. Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(normal)

bits_bridge = r'''
Lemma redirect_to_N_cons bit rest :
 to_N (bit :: rest) = 2 * to_N rest + (if bit then 1 else 0).
Proof. unfold to_N. destruct bit; cbn [foldr N.b2n]; lia. Qed.
Lemma redirect_to_N_and_nil right : to_N (andB [::] right) = 0.
Proof.
 induction right as [|b right IH]; [reflexivity|].
 unfold andB, lift0 in *. rewrite lift_nil_cons.
 rewrite redirect_to_N_cons. change (2 * to_N (lift b0 andb [::] right) + 0 = 0). rewrite IH. reflexivity.
Qed.
Lemma redirect_to_N_and left right :
 to_N (andB left right) = N.land (to_N left) (to_N right).
Proof.
 revert right. induction left as [|a left IH]; intros [|b right].
 - reflexivity.
 - rewrite redirect_to_N_and_nil. reflexivity.
 - unfold andB, lift0. rewrite lift_cons_nil.
   rewrite redirect_to_N_cons. change (2 * to_N (andB left [::]) + (if a && false then 1 else 0) = N.land (to_N (a :: left)) 0).
   rewrite IH !N.land_0_r. destruct a; reflexivity.
 - rewrite andB_cons !redirect_to_N_cons IH.
   destruct a, b; cbn [andb]; rewrite ?N.add_0_r;
   rewrite ?N.land_even_even ?N.land_odd_even ?N.land_even_odd ?N.land_odd_odd; reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write('\nFrom Coq Require Import Lia.\nFrom nbits Require Import NBitsDef NBitsOp.\n' + bits_bridge)

generic = r'''
Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
Lemma reference_redirect_ground_step offsets nodes node expression ground bits invalid old current result :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node, expression) nodes ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression old old = Some (Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find node result = Some (Gval ground bits).
Proof.
 intros Positions Safety Member Eval Step.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node expression Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply (formal_combinational_known_ground_node count flat_statements tail node expression ground);
 [exact Position|exact Safe|exact Nonreg|apply Eval|reflexivity|exact Step].
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write(generic)

decode_bridge = r'''
From firrtl Require Import Firrtl_with_implicit_widths.
Lemma redirect_N_eqb x y : (x == y) = N.eqb x y.
Proof.
 destruct (eqP : reflect (x = y) (x == y)) as [H|H].
 - subst y. rewrite N.eqb_refl. reflexivity.
 - symmetry. apply N.eqb_neq. exact H.
Qed.
Lemma redirect_mask_decode instruction mask code iw mw cw :
 eval_binop (Bcomp Beq) (Gval (Fuint cw) code)
  (Gval (Fuint (maxn iw mw)) (andB instruction mask)) =
 Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) (to_N mask)) (to_N code)]).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit (Bcomp Beq) (Gval (Fuint cw) code)
 (Gval (Fuint (maxn iw mw)) (andB instruction mask))); cbn [refine_boolean_result];
 rewrite redirect_to_N_and redirect_N_eqb N.eqb_sym; reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write(decode_bridge)

# All eight decoders share the same two-stage masked-equality proof.
decode_nodes = [1974,1980,1986,1992,1998,2004,2010,2357]
def constant(expr):
 match = re.search(r'\(@Econst VarOrder.T \(Fuint (\d+)\) (\[::[^]]*\])\)', expr)
 width, bits = int(match[1]), match[2]
 value = sum((bit == 'true') << i for i,bit in enumerate(re.findall('true|false',bits)))
 return width,bits,value
batch = ['\nRequire Import ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1.\nFrom nbits Require Import NBitsDef NBitsOp.\nFrom firrtl Require Import Firrtl_with_implicit_widths.',
'Theorem reference_redirect_decoders_history inputs path history limit reset time instruction :',
' (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->',
' (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->',
' (127 <= time)%coq_nat -> (time < limit)%coq_nat ->',
' VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->']
claims=[]
for node in decode_nodes:
 mw,mask,mv=constant(rows[node-1]['expression']);cw,code,cv=constant(rows[node]['expression'])
 claims.append(f'VM.find {node} (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) {mv}) {cv}])')
batch += [' /\\\n '.join(claims)+'.','Proof.',' intros Resets Steps Lower Upper Instruction.',' pose proof (Steps time Upper) as Step.']
for node in decode_nodes:
 group=0 if node<2183 else 1
 mw,mask,mv=constant(rows[node-1]['expression']);cw,code,cv=constant(rows[node]['expression'])
 for n,bits,ground in [(node-1,f'(andB instruction {mask})','(Fuint 32)'),(node,f'[::N.eqb (N.land (to_N instruction) {mv}) {cv}]','(Fuint 1)')]:
  batch += [f' assert (H{n} : VM.find {n} (history (S time)) = Some (Gval {ground} {bits})).',
  f' {{ eapply (reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes {n} reference_control_expr_{n});',
  f' [exact reference_control_{group}_positions|exact reference_control_{group}_safety|exact reference_control_member_{n}| |exact Step].',
  f' intros site. unfold reference_control_expr_{n}. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].']
  if n==node-1:
   batch += [' rewrite Instruction. reflexivity. }']
  else:
   batch += [f' rewrite H{node-1}. change (eval_binop (Bcomp Beq) (Gval (Fuint {cw}) {code}) (Gval (Fuint (maxn 32 {mw})) (andB instruction {mask})) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) {mv}) {cv}])).',f' exact (redirect_mask_decode instruction {mask} {code} 32 {mw} {cw}). }}']
  batch += [f' rewrite <- (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H{n}.']
batch += [' repeat split; assumption.','Qed.']
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write('\n'.join(batch)+'\n')

# Six register comparisons share references and signed casts.  Keep the signed
# result in the bit-vector library's to_Z form until its word-size bridge.
compare_nodes=[2806,2830,2850,2872,2892,2912]
cone=set()
def visit_compare(n):
 if n in (2209,2804) or n in cone: return
 for dep in rows[n]['dependencies']: visit_compare(dep)
 cone.add(n)
for n in compare_nodes: visit_compare(n)
values={2209:('(Fuint 32)','rs1'),2804:('(Fuint 32)','rs2')}
for n in sorted(cone):
 expr=rows[n]['expression'];deps=rows[n]['dependencies']
 if 'Ecast' in expr: values[n]=('(Fsint 32)',values[deps[0]][1])
 elif 'Eprim_binop' in expr:
  op=re.search(r'Bcomp (\w+)',expr)[1];a,b=[values[d] for d in deps]
  if a[0]=='(Fsint 32)': bit=f'Z.{"geb" if op=="Bgeq" else "ltb"} (to_Z {a[1]}) (to_Z {b[1]})'
  elif op=='Bgeq': bit=f'N.leb (to_N {b[1]}) (to_N {a[1]})'
  elif op=='Blt': bit=f'N.ltb (to_N {a[1]}) (to_N {b[1]})'
  elif op=='Beq': bit=f'(to_N {a[1]} == to_N {b[1]})'
  else: bit=f'(to_N {a[1]} != to_N {b[1]})'
  values[n]=('(Fuint 1)',f'[::{bit}]')
 else: values[n]=values[deps[0]]
compare=['\nRequire Import ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence2.',
'Theorem reference_redirect_comparisons_history inputs path history limit reset time rs1 rs2 :',
' (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->',
' (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->',
' (127 <= time)%coq_nat -> (time < limit)%coq_nat ->',
' VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->',
' VM.find 2804 (history time) = Some (Gval (Fuint 32) rs2) ->']
compare += [' /\\\n '.join(f'VM.find {n} (history time) = Some (Gval {values[n][0]} {values[n][1]})' for n in compare_nodes)+'.',
'Proof.',' intros Resets Steps Lower Upper H2209 H2804.',' pose proof (Steps time Upper) as Step.']
for n in sorted(cone):
 ground,bits=values[n];group=2 if n<2828 else 3
 compare += [f' assert (H{n} : VM.find {n} (history (S time)) = Some (Gval {ground} {bits})).',
 f' {{ eapply (reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes {n} reference_control_expr_{n});',
 f' [exact reference_control_{group}_positions|exact reference_control_{group}_safety|exact reference_control_member_{n}| |exact Step].',
 f' intros site. unfold reference_control_expr_{n}. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].',
 ' rewrite '+' '.join('H'+str(d) for d in rows[n]['dependencies'])+'. reflexivity. }',
 f' rewrite <- (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H{n}.']
compare += [' repeat split; assumption.','Qed.']
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write('\n'.join(compare)+'\n')

bit_index_bridge = r'''
From Coq Require Import NArith.
Lemma redirect_to_N_testbit bits index :
 N.testbit (to_N bits) (N.of_nat index) = nth false bits index.
Proof.
 revert bits. induction index as [|index IH]; intros [|b bits].
 - reflexivity.
 - rewrite redirect_to_N_cons. change (N.testbit (2 * to_N bits + N.b2n b) 0 = b). apply N.testbit_0_r.
 - rewrite N.bits_0. reflexivity.
 - rewrite redirect_to_N_cons Nat2N.inj_succ.
   change (N.testbit (2 * to_N bits + N.b2n b) (N.succ (N.of_nat index)) = nth false bits index).
   rewrite N.testbit_succ_r. apply IH.
Qed.
Lemma redirect_msb_nth bits : msb bits = nth false bits (size bits).-1.
Proof.
 rewrite nth_last. unfold msb, splitmsb, split_last, lastd.
 destruct bits; reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write(bit_index_bridge)

signed_bridge = r'''
Lemma reference_redirect_signed32 bits :
 size bits = 32%nat -> to_Z bits = reference_redirect_signed (to_N bits).
Proof.
 intro Size. unfold reference_redirect_signed.
 change (to_Z bits = if N.testbit (to_N bits) (N.of_nat 31) then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 rewrite redirect_to_N_testbit to_Z_to_Zpos to_Zpos_N redirect_msb_nth Size.
 change ((Z.of_N (to_N bits) - Z.b2z (nth false bits 31) * 4294967296)%Z = if nth false bits 31 then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 destruct (nth false bits 31); cbn [Z.b2z]; rewrite ?Z.mul_1_l ?Z.mul_0_l ?Z.sub_0_r; reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(signed_bridge)

alignment_bridge = r'''
Lemma reference_redirect_aligned_bits compressed target :
 reference_redirect_aligned compressed target =
 negb (N.testbit target 0) && (compressed || negb (N.testbit target 1)).
Proof.
 unfold reference_redirect_aligned.
 destruct compressed; destruct target as [|[p|p|]]; try reflexivity; destruct p; reflexivity.
Qed.
Lemma reference_redirect_alignment_select compressed bits :
 (if compressed then (to_N (take 1 bits) == 0) else (to_N (take 2 bits) == 0)) =
 reference_redirect_aligned compressed (to_N bits).
Proof.
 rewrite reference_redirect_aligned_bits
  (redirect_to_N_testbit bits 0) (redirect_to_N_testbit bits 1).
 destruct compressed; destruct bits as [|a [|b bits]]; try reflexivity;
 destruct a; try reflexivity; destruct b; cbn [take]; rewrite ?take0; vm_compute; reflexivity.
Qed.
Lemma reference_redirect_aligned_take32_from33 compressed value :
 reference_redirect_aligned compressed (to_N (take 32 (from_N 33 value))) =
 reference_redirect_aligned compressed value.
Proof.
 rewrite !reference_redirect_aligned_bits
  (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 rewrite !nth_take //.
 rewrite -(redirect_to_N_testbit (from_N 33 value) 0)
  -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite !N.mod_pow2_bits_low; reflexivity.
Qed.
Lemma reference_redirect_aligned_jalr compressed value :
 reference_redirect_aligned compressed
  (to_N (false :: take 31 (drop 1 (take 32 (from_N 33 value))))) =
 reference_redirect_aligned compressed (N.clearbit value 0).
Proof.
 rewrite !reference_redirect_aligned_bits N.clearbit_eq
  N.clearbit_neq; [|discriminate].
 rewrite (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 cbn [nth]. rewrite !nth_take // nth_drop.
 change ((true && (compressed || ~~ nth false (take 32 (from_N 33 value)) 1)) =
  (true && (compressed || ~~ N.testbit value 1))).
 rewrite nth_take // -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite N.mod_pow2_bits_low; reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(alignment_bridge)

csr_bridge = r'''
Lemma reference_redirect_csr_compressed bits :
 size bits = 32%nat ->
 eval_unop (Uextr 2 2) (Gval (Fuint 32) bits) =
 Some (Gval (Fuint 1) [::N.testbit (to_N bits) 2]).
Proof.
 intro Size. rewrite (redirect_to_N_testbit bits 2).
 change (Some (Gval (Fuint 1) (drop 2 (take 3 bits))) = Some (Gval (Fuint 1) [::nth false bits 2])).
 destruct bits as [|a [|b [|c rest]]]; try discriminate Size.
 cbn [drop take nth]. rewrite take0. reflexivity.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write(csr_bridge)

equation_bridge = r'''
Require Import ReferenceControlGroundExpressions FormalSuccessfulNodeEvaluation.
Lemma reference_redirect_node_equation offsets nodes node expression inputs path old result :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node, expression) nodes ->
 reference_control_ready old expression ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 VM.find node old = VM.find node result ->
 exists site, VM.find node old =
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression old old.
Proof.
 intros Positions Safety Member Ready Step Stable.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node expression Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression
 (formal_invalid_policy inputs path) flat_memories old false old result Position Step) as [value Eval].
 rewrite add0n in Eval.
 destruct (reference_control_expression_ground inputs path flat_memories old expression Ready _ value Eval) as [ground Typed].
 exists (validif_raw_address nil count 0 nil).
 rewrite Stable Eval.
 exact (formal_combinational_known_ground_node count flat_statements tail node expression ground value (formal_invalid_policy inputs path)
 flat_memories old old result Position Safe Nonreg Eval Typed Step).
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSpine.v').open('a') as output:
 output.write(equation_bridge)

# A single batch theorem closes all alignment clusters.  Local evaluation
# equations reuse existing certificates instead of adding per-node wrappers.
alignment_roots=[2825,2847,2867,2889,2909,2929,2949,2966]
alignment_cones={}
for root in alignment_roots:
 cone=set()
 def visit_alignment(n):
  if n in (1750,1749,2552,2209) or n in cone: return
  for dep in rows[n]['dependencies']: visit_alignment(dep)
  cone.add(n)
 visit_alignment(root)
 alignment_cones[root]=cone
alignment_nodes=set.union(*alignment_cones.values())
alignment=['''Theorem reference_redirect_alignments_history inputs path history limit reset time csr pc immediate rs1 :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1750 (history time) = Some (Gval (Fuint 32) csr) ->
 VM.find 1749 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) immediate) ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 size csr = 32%nat ->''']
for i,root in enumerate(alignment_roots):
 target='(N.clearbit (to_N rs1 + to_N immediate) 0)' if root==2949 else '(to_N pc + to_N immediate)'
 alignment += [f' VM.find {root} (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) {target}])'+(' /\\' if i<7 else '.')]
alignment += ['Proof.',' intros Resets Steps Lower Upper Csr Pc Immediate Rs1 Size.',' pose proof (Steps time Upper) as Step.']
for n in sorted(alignment_nodes):
 group=2 if n<2828 else 3
 deps=rows[n]['dependencies'];ready=f'apply reference_control_ready_{n}'
 if deps: ready+='; first ['+'|'.join(f'exact (reference_control_ground_{d}_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))' for d in deps)+']'
 alignment += [f' destruct (reference_redirect_node_equation reference_control_{group}_offsets reference_control_{group}_nodes {n} reference_control_expr_{n} inputs path (history time) (history (S time)) reference_control_{group}_positions reference_control_{group}_safety reference_control_member_{n} ltac:({ready}) Step (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site{n} E{n}].',f' unfold reference_control_expr_{n} in E{n}.']
alignment += [' repeat split.']
for root in alignment_roots:
 cone=alignment_cones[root]
 alignment += [f' - rewrite E{root}.',
 '   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr\' eval_type_of_ref]; rewrite '+' '.join('?E'+str(n) for n in sorted(cone,reverse=True))+' ?Csr ?Pc ?Immediate ?Rs1)).',
 '   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].',
 '   rewrite (reference_redirect_csr_compressed csr Size).',
 '   destruct (N.testbit (to_N csr) 2);',
 '   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];',
 '   cbv -[from_N reference_redirect_aligned].']
 for compressed,width in [('true',1),('false',2)]:
  total='(to_N rs1 + to_N immediate)' if root==2949 else '(to_N pc + to_N immediate)'
  targetbits=f'(false :: take 31 (drop 1 (take 32 (from_N 33 {total}))))' if root==2949 else f'(take 32 (from_N 33 {total}))'
  numerical=f'(N.clearbit {total} 0)' if root==2949 else total
  alignment += [f'   + change (Some (Gval (Fuint 1) [::to_N (take {width} {targetbits}) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned {compressed} {numerical}])).',
  f'     rewrite (reference_redirect_alignment_select {compressed} {targetbits}).',
  '     rewrite '+('reference_redirect_aligned_jalr' if root==2949 else 'reference_redirect_aligned_take32_from33')+'. reflexivity.']
alignment += ['Qed.']
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write('\n'.join(alignment)+'\n')

alias_bridge = r'''
Require Import ReferenceControlWires2 FormalDeclaredConnection.
Lemma reference_redirect_adapt_word bits :
 size bits = 32%nat ->
 adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits).
Proof.
 intro Size. cbn [adapt_hvalue_as_type]. rewrite <- Size, take_size.
 unfold zext_to. rewrite subnn. unfold zext. rewrite zeros0 cats0. reflexivity.
Qed.
Theorem reference_redirect_aliases_history inputs path history limit reset time pc csr :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 7331 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (history time) = Some (Gval (Fuint 32) csr) ->
 size pc = 32%nat -> size csr = 32%nat ->
 VM.find 1749 (history time) = Some (Gval (Fuint 32) pc) /\
 VM.find 1750 (history time) = Some (Gval (Fuint 32) csr).
Proof.
 intros Resets Steps Lower Upper Pc Csr PcSize CsrSize.
 pose proof (Steps time Upper) as Step.
 split.
 - rewrite (reference_control_stable_1749_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (declared_connection_value 1828 flat_statements reference_control_wire_1749_decl reference_control_wire_1749_mid reference_control_wire_1749_tail 1749 7331 32 (Gval (Fuint 32) pc));
   [exact reference_control_wire_1749_position|exact reference_control_wire_1749_split|exact reference_control_wire_1749_straight|exact reference_control_wire_1749_mid_safe|exact reference_control_wire_1749_tail_safe|exact reference_control_wire_1749_nonregister|reflexivity|exact Pc|apply reference_redirect_adapt_word; exact PcSize|exact Step].
 - rewrite (reference_control_stable_1750_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (declared_connection_value 1829 flat_statements reference_control_wire_1750_decl reference_control_wire_1750_mid reference_control_wire_1750_tail 1750 7332 32 (Gval (Fuint 32) csr));
   [exact reference_control_wire_1750_position|exact reference_control_wire_1750_split|exact reference_control_wire_1750_straight|exact reference_control_wire_1750_mid_safe|exact reference_control_wire_1750_tail_safe|exact reference_control_wire_1750_nonregister|reflexivity|exact Csr|apply reference_redirect_adapt_word; exact CsrSize|exact Step].
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(alias_bridge)

function_bridge = r'''
Theorem reference_redirect_function_history inputs path history limit reset time instruction rs1 rs2 immediate pc csr :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (history time) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (history time) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6507 (history time) = Some (Gval (Fuint 1)
 [::reference_redirect_function (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)]).
Proof.
 intros Resets Steps Lower Upper Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (reference_redirect_aliases_history inputs path history limit reset time pc csr Resets Steps Lower Upper Pc Csr PcSize CsrSize) as [PcAlias CsrAlias].
 destruct (reference_redirect_decoders_history inputs path history limit reset time instruction Resets Steps Lower Upper Instruction)
 as [H1974 [H1980 [H1986 [H1992 [H1998 [H2004 [H2010 H2357]]]]]]].
 destruct (reference_redirect_comparisons_history inputs path history limit reset time rs1 rs2 Resets Steps Lower Upper Rs1 Rs2)
 as [H2806 [H2830 [H2850 [H2872 [H2892 H2912]]]]].
 destruct (reference_redirect_alignments_history inputs path history limit reset time csr pc immediate rs1 Resets Steps Lower Upper CsrAlias PcAlias Immediate Rs1 CsrSize)
 as [H2825 [H2847 [H2867 [H2889 [H2909 [H2929 [H2949 H2966]]]]]]].
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) Z.geb_leb in H2830.
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) in H2872.
 rewrite redirect_N_eqb in H2892, H2912.
 rewrite <- (reference_redirect_guards_normalize (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)).
 eapply (reference_redirect_spine_history inputs path history limit reset time); assumption.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(function_bridge)

observed_bridge = r'''
Require Import FormalObservedHistory FormalLocalHistory.
Theorem reference_redirect_function_observed memory inputs k observed instruction rs1 rs2 immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1884 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (top_environment observed) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment observed) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6507 (top_environment observed) = Some (Gval (Fuint 1)
 [::reference_redirect_function (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)]).
Proof.
 intros Observe Legal Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last.
 rewrite <- (reference_control_stable_6507_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 eapply (reference_redirect_function_history (generated_observation_input inputs k) nil history 9259 reset 9258 instruction rs1 rs2 immediate pc csr Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)); try assumption.
 - rewrite (reference_control_stable_1884_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Instruction.
 - rewrite (reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs1.
 - rewrite (reference_control_stable_2804_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs2.
 - rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Immediate.
 - rewrite (reference_control_stable_7331_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Pc.
 - rewrite (reference_control_stable_7332_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Csr.
Qed.
'''
with (REPO_ROOT / 'formal/flat-low/staged-integration/ReferenceRedirectSemantics.v').open('a') as output:
 output.write(observed_bridge)
