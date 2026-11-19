"""Parameterize the three real S-immediate sign-extension paths."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
s='''Require Import CoreSocModel ComparisonNodes ReferenceLoadImmediate ReferenceImmediateTypes ReferenceLoadSemantics ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence1 ReferenceControlStabilityHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition store_imm_aux_node i : VarOrder.T := 2283+N.of_nat i.
Definition store_imm_aux_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) [::'''+ ';'.join(f'reference_control_expr_{n}' for n in range(2283,2298))+'''] i.
Theorem store_imm_aux_value i inputs path history limit reset time width word :
 (i < 15)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (store_imm_aux_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (store_imm_aux_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
'''
for n in range(2283,2298):
 s+=f''' destruct i as [|i].
 {{ change (VM.find {n} (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes {n} reference_control_expr_{n});
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_{n}|exact Eval|apply Steps;lia]. }}
'''
s+=' lia.\nQed.\n'
s+='''Theorem store_imm_sign_history lane inputs path history limit reset time low high :
 (lane < 3)%coq_nat -> size low = 5%nat -> size high = 7%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 2268 (history time) = Some (Gval (Fuint 7) high) ->
 VM.find 2282 (history time) = Some (Gval (Fuint 5) low) ->
 VM.find (load_imm_mux_yes true (Nat.sub 7 lane)) (history time) = Some (Gval (Fuint 32) (sext_to 32 (low++high))).
Proof.
 intros Lane LowSize HighSize Resets Steps Lower Upper High Low.
 assert (Size : size (low++high) = 12%nat) by (rewrite size_cat LowSize HighSize;reflexivity).
'''
for lane in range(3):
 s+=' destruct lane as [|lane].\n {\n'
 for j in range(5):
  n=2283+5*lane+j;value=['low++high','[::msb (low++high)]','[::msb (low++high)]','nseq 20 (msb (low++high))','sext_to 32 (low++high)'][j];width=[12,1,1,20,32][j]
  s+=f''' assert (V{j} : VM.find {n} (history time) = Some (Gval (Fuint {width}) ({value}))).
 {{ eapply (store_imm_aux_value {5*lane+j}%nat inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_imm_aux_expression nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
  if j==0:s+=' rewrite High Low. unfold eval_binop. rewrite immediate_cat_no_absorbing. reflexivity. }\n'
  elif j==1:s+=' rewrite V0. change (Some (Gval (Fuint 1) (drop (12-1)%nat (take 12 (low++high)))) = Some (Gval (Fuint 1) [::msb (low++high)])). rewrite (reference_load_sign_bit 12 (low++high) Size (eq_refl true));reflexivity. }\n'
  elif j==2:s+=' rewrite V1;destruct (msb (low++high));reflexivity. }\n'
  elif j==3:s+=' rewrite V2;destruct (msb (low++high));reflexivity. }\n'
  else:s+=' rewrite V3 V0. unfold eval_binop. rewrite immediate_cat_no_absorbing. cbn. unfold sext_to,sext. rewrite Size. reflexivity. }\n'
 s+=' exact V4. }\n'
s+=' lia.\nQed.\n'
p=base/'ReferenceStoreImmediate.v';mark='(* Store immediate composition. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
