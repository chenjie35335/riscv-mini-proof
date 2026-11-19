from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
s='''Require Import RFShiftNodes RFShiftNodeStep RFShiftReverseHistory RFWritebackSelection CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_shift_center_word arithmetic word right :=
 take 32(sext_to 33(drop(minn(to_nat(take 5 right))32)
 (word++andB [::arithmetic](drop 31(take 32 word))))).
Theorem rf_shift_center_history invalid history limit arithmetic b1 b2 direction word right :
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::arithmetic;b1;b2;direction])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1222(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)(rf_shift_center_word arithmetic word right)).
Proof.
 intros Modes Rights Words Steps.
'''
values={1171:('Fuint 5','take 5 right',1,[1152]),1223:('Fuint 1','[::arithmetic]',1,[1153]),1224:('Fuint 1','drop 31(take 32 word)',1,[1222]),1225:('Fuint 1','andB [::arithmetic](drop 31(take 32 word))',2,[1223,1224]),1226:('Fuint 33','word++andB [::arithmetic](drop 31(take 32 word))',3,[1225,1222]),1227:('Fsint 33','word++andB [::arithmetic](drop 31(take 32 word))',4,[1226]),1228:('Fsint 33','sext_to 33(drop(minn(to_nat(take 5 right))32)(word++andB [::arithmetic](drop 31(take 32 word))))',5,[1227,1171]),1229:('Fuint 32','rf_shift_center_word arithmetic word right',6,[1228])}
for n,(typ,word,rank,deps) in values.items():
 s+=f''' assert(V{n}:forall t,({rank}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval({typ})({word}))).
 {{ intros [|t] Lower Upper;[lia|]. eapply(rf_shift_node_step {n} rf_shift_expr_{n});
 [apply(List.nth_error_In rf_shift_nodes {n-1171}%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
 for d in deps:
  if d in [1152,1153,1222]:s+=f' rewrite({{1152:"Rights",1153:"Modes",1222:"Words"}}[d]).' if False else f' rewrite({dict([(1152,"Rights"),(1153,"Modes"),(1222,"Words")])[d]} t ltac:(lia)).\n'
  else:s+=f' rewrite(V{d} t ltac:(lia)ltac:(lia)).\n'
 s+=' cbn[eval_unop]. rewrite ?drop0. unfold eval_binop,refine_boolean_result. cbn[eval_binop_basic]. destruct arithmetic;try destruct(absorbing_bit _ _ _);reflexivity. }\n'
s+='intros t Lower Upper. exact(V1229 t Lower Upper).\nQed.\n'
(p/'RFShiftCenter.v').write_text(s)
