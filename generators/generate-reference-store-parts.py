"""Actual S-immediate extraction and enabled selection, three indexed store lanes."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
nodes=[1942,1943,1947,1948,1952,1953]+list(range(2261,2283))
s='''Require Import CoreSocModel ComparisonNodes ReferenceStoreImmediate ReferenceLoadImmediate ReferenceImmediateTypes ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlStabilityHistory DUTRedirectDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
s+='Definition store_part_node i : VarOrder.T := nth 0 [::'+ ';'.join(map(str,nodes))+'] i.\n'
s+='Definition store_part_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) [::'+ ';'.join(f'reference_control_expr_{n}' for n in nodes)+'] i.\n'
s+='''Lemma store_part_value i inputs path history limit reset time width word :
 (i < 28)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (store_part_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (store_part_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
'''
for n in nodes:
 g=0 if n<2183 else 1
 s+=f''' destruct i as [|i].
 {{ change (VM.find {n} (history time) = Some (Gval (Fuint width) word)).
 rewrite (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step reference_control_{g}_offsets reference_control_{g}_nodes {n} reference_control_expr_{n});
 [exact reference_control_{g}_positions|exact reference_control_{g}_safety|exact reference_control_member_{n}|exact Eval|apply Steps;lia]. }}
'''
s+=' lia.\nQed.\n'
s+=r'''Definition store_immediate_low (instruction : bits) := drop 7 (take 12 instruction).
Definition store_immediate_high (instruction : bits) := drop 25 (take 32 instruction).
Theorem store_immediate_parts_history lane inputs path history limit reset time instruction :
 (lane < 3)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1941 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 0]) ->
 VM.find 1946 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 1]) ->
 VM.find 1951 (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 2]) ->
 VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction)) /\
 VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction)).
Proof.
 intros Lane Size Resets Steps Lower Upper Source Enabled SW SH SB.
 assert (HighSize : size (store_immediate_high instruction) = 7%nat) by (unfold store_immediate_high;rewrite size_drop size_take Size;reflexivity).
 assert (LowSize : size (store_immediate_low instruction) = 5%nat) by (unfold store_immediate_low;rewrite size_drop size_take Size;reflexivity).
'''
# Prove all extracted slices once; nested takes simplify by take_take.
slices={1942:(1884,25,0),1943:(1942,20,0),1947:(1884,25,0),1948:(1947,20,0),1952:(1884,25,0),1953:(1952,20,0),2261:(1884,32,25),2262:(1884,32,25),2263:(1884,32,25),2269:(1943,15,0),2270:(2269,12,0),2271:(2270,12,7),2272:(1948,15,0),2273:(2272,12,0),2274:(2273,12,7),2275:(1953,15,0),2276:(2275,12,0),2277:(2276,12,7)}
for n,(src,take,drop) in slices.items():
 value=f'drop {drop} (take {take} instruction)' if drop else f'take {take} instruction'
 s+=f''' assert (V{n} : VM.find {n} (history time) = Some (Gval (Fuint {take-drop}) ({value}))).
 {{ eapply (store_part_value {nodes.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite {'Source' if src==1884 else 'V'+str(src)}. cbn.
 repeat rewrite drop0. repeat rewrite <- take_min. cbn. reflexivity. }}
'''
# instantiate lane, all mux intermediate values known; adaptation simplify via concrete list sizes.
for lane in range(3):
 s+=' destruct lane as [|lane].\n {\n cbn [Nat.eqb] in SW,SH,SB.\n'
 for n,w,cond,yes,no,active in [(2264,7,'SB',2263,None,lane==2),(2265,7,'SH',2262,2264,lane>=1),(2266,7,'SW',2261,2265,True),(2267,7,'Enabled',2266,None,True),(2268,7,None,2267,None,True),(2278,5,'SB',2277,None,lane==2),(2279,5,'SH',2274,2278,lane>=1),(2280,5,'SW',2271,2279,True),(2281,5,'Enabled',2280,None,True),(2282,5,None,2281,None,True)]:
  v=('store_immediate_high instruction' if w==7 else 'store_immediate_low instruction') if active else f'nseq {w} false'
  s+=f''' assert (V{n} : VM.find {n} (history time) = Some (Gval (Fuint {w}) ({v}))).
 {{ eapply (store_part_value {nodes.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [store_part_expression nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
  if cond is None: s+=f' exact V{yes}. }}\n';continue
  s+=f' rewrite {cond};cbn. try rewrite V{yes}'+ (f';try rewrite V{no}' if no else '')+'.\n'
  s+=f" unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];try rewrite V{yes}"+(f";try rewrite V{no}" if no else "")+".\n"
  s+=f' change (adapt_hvalue_as_type (Gval (Fuint {w}) ({v})) (Gtyp (Fuint {w})) = Some (Gval (Fuint {w}) ({v}))). apply dut_decode_adapt. '+ ('exact HighSize.' if active and w==7 else 'exact LowSize.' if active else 'rewrite size_nseq;reflexivity.')+' }\n'
 s+=' split;[exact V2268|exact V2282]. }\n'
s+=' lia.\nQed.\n'
s+=r'''Definition store_s_immediate instruction := sext_to 32 (store_immediate_low instruction ++ store_immediate_high instruction).
Lemma store_s_immediate_size instruction : size instruction = 32%nat -> size (store_s_immediate instruction) = 32%nat.
Proof.
 intro Size. unfold store_s_immediate,sext_to,sext.
 rewrite size_cat size_nseq size_cat. unfold store_immediate_low,store_immediate_high.
 rewrite !size_drop !size_take Size. reflexivity.
Qed.
Theorem reference_store_immediate_history inputs path history limit reset time instruction lane :
 (lane < 3)%coq_nat -> size instruction = 32%nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (200 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 1884 (history t) = Some (Gval (Fuint 32) instruction)) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true]) ->
 (forall n, (n < load_imm_mux_count true)%coq_nat -> VM.find (load_imm_mux_guard true n) (history time) = Some (Gval (Fuint 1) [::Nat.eqb n (Nat.sub 7 lane)])) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 pose proof (Guards 7%nat ltac:(cbn [load_imm_mux_count];lia)) as SW.
 pose proof (Guards 6%nat ltac:(cbn [load_imm_mux_count];lia)) as SH.
 pose proof (Guards 5%nat ltac:(cbn [load_imm_mux_count];lia)) as SB.
 cbn [load_imm_mux_guard nth] in SW,SH,SB.
 assert (Parts : VM.find 2268 (history time) = Some (Gval (Fuint 7) (store_immediate_high instruction)) /\
 VM.find 2282 (history time) = Some (Gval (Fuint 5) (store_immediate_low instruction))).
 { eapply (store_immediate_parts_history lane inputs path history limit reset time instruction);[exact Lane|exact Size|exact Resets|exact Steps|exact Lower|exact Upper|apply Source;lia|exact Enabled| | |];
 do 3 (destruct lane as [|lane];[assumption|]);lia. }
 destruct Parts as [High Low].
 assert (HighSize : size (store_immediate_high instruction) = 7%nat) by (unfold store_immediate_high;rewrite size_drop size_take Size;reflexivity).
 assert (LowSize : size (store_immediate_low instruction) = 5%nat) by (unfold store_immediate_low;rewrite size_drop size_take Size;reflexivity).
 pose proof (store_imm_sign_history lane inputs path history limit reset time _ _ Lane LowSize HighSize Resets Steps Lower Upper High Low) as Sign.
 assert (Selected : VM.find 2550 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction))).
 { change (VM.find (load_imm_mux_node true 10) (history time) = Some (Gval (Fuint (load_imm_mux_width true)) (store_s_immediate instruction))).
 eapply (load_imm_mux_suffix_history true inputs path history limit reset time (Nat.sub 7 lane) (store_s_immediate instruction));[cbn [load_imm_mux_count];lia|exact (store_s_immediate_size instruction Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact Guards|exact Sign|lia|cbn [load_imm_mux_count];lia].
 intros t L U. exists (Gval (Fuint 32) instruction);split;[apply Source;assumption|reflexivity]. }
 assert (EnabledValue : VM.find 2551 (history time) = Some (Gval (Fuint 32) (store_s_immediate instruction))).
 { eapply (load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn [load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Enabled;cbn;rewrite Selected. change (adapt_hvalue_as_type (Gval (Fuint 32) (store_s_immediate instruction)) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) (store_s_immediate instruction))). apply dut_decode_adapt;exact (store_s_immediate_size instruction Size). }
 eapply (load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. exact EnabledValue.
Qed.
'''
p=base/'ReferenceStoreParts.v';p.write_text(s)
