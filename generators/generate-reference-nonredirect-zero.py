from pathlib import Path
s='''Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3 ReferenceRedirectSpineTypes ReferenceControlExpressions ReferenceControlStabilityHistory SelectedZeroMux.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition reference_nonredirect_guards :seq VarOrder.T := [::2357;2010;2004;1998;1992;1986;1980;1974].
Theorem reference_nonredirect_zero_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_flat_local_step invalid(history t)(history(S t))) ->
 (forall node,List.In node reference_nonredirect_guards ->forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6507(history t)=Some(Gval(Fuint width)(zeros width)).
Proof.
 intros Steps Guards.
'''
rows=[(6325,2357),(6359,2010),(6387,2004),(6411,1998),(6435,1992),(6459,1986),(6483,1980),(6507,1974)]
for i,(n,g) in enumerate(rows):
 s+=f''' assert(Z{n}:forall t,(Nat.add start {i+1}<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find {n}(history t)=Some(Gval(Fuint width)(zeros width))).
 {{ intros[|t] Lower Upper;try lia.
'''
 if i:s+=f' destruct(Z{rows[i-1][0]} t ltac:(lia)ltac:(lia))as[width Zero].\n'
 s+=f''' eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes {n} _ _ _ invalid(history t)(history(S t))false '''+('width'if i else '1')+f''');
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_{n}| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;'''+('exact Zero.'if i else 'reflexivity.')+' }\n'
s+=' exact Z6507.\nQed.\n'
s+='''Theorem reference_nonredirect_zero_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (forall node,List.In node reference_nonredirect_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::false])) ->
 exists width,VM.find 6507(top_environment observed)=Some(Gval(Fuint width)(zeros width)).
Proof.
 intros Observe Legal Guards.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Stable:forall node,List.In node reference_nonredirect_guards ->forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(history 9259%nat)).
 { intros node Member t Lower Upper. cbn[reference_nonredirect_guards List.In]in Member.
'''
for n,g in rows:s+=f' destruct Member as[<-|Member];[apply(reference_control_stable_{g}_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].\n'
s+=' contradiction. }\n rewrite <-Last. apply(reference_nonredirect_zero_history _ history 9259 200 Steps).\n - intros node Member t Lower Upper. rewrite(Stable node Member t Lower Upper)Last. exact(Guards node Member).\n - vm_compute;lia.\n - lia.\nQed.\n'
s+='Theorem reference_nonredirect_false_observed memory inputs k observed :\n generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->\n (forall node,List.In node reference_nonredirect_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::false])) ->\n VM.find 6507(top_environment observed)=Some(Gval(Fuint 1)[::false]).\nProof.\n intros Observe Legal Guards.\n destruct(reference_nonredirect_zero_observed memory inputs k observed Observe Legal Guards)as[width Zero].\n destruct(reference_redirect_spine_types_observed memory inputs k observed 21%nat Observe Legal ltac:(lia))as[value[Value Typed]].\n change(VM.find 6507(top_environment observed)=Some value)in Value.\n rewrite Zero in Value;inversion Value;subst value.\n cbn[type_of_val]in Typed. inversion Typed;subst width. exact Zero.\nQed.\n'
Path('formal/flat-low/staged-integration/ReferenceNonredirectZero.v').write_text(s)
