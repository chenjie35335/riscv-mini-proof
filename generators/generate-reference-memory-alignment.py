"""Reuse existing actual-node certificates for all four load alignment lanes."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
rows=[[1887,2210]+list(range(2553,2566)),list(range(2635,2650)),list(range(2650,2665)),list(range(2665,2680)),list(range(2694,2709)),list(range(2709,2724))]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceLoadSemantics DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out+='Definition reference_alignment_rows : seq (seq VarOrder.T) := '+seq(seq(row) for row in rows)+'.\n'
out+='Definition reference_alignment_expressions : seq (seq (hfexpr VarOrder.T)) := '+seq(seq('reference_control_expr_'+str(n) for n in row) for row in rows)+'.\n'
out+='''Definition reference_alignment_node lane stage := nth 0 (nth [::] reference_alignment_rows lane) stage.
Definition reference_alignment_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_alignment_expressions lane) stage.
Definition reference_alignment_group lane stage := if Nat.eqb lane 0 then if Nat.eqb stage 0 then 0%nat else if Nat.eqb stage 1 then 1%nat else 2%nat else 2%nat.
Definition reference_alignment_nodes lane stage := match reference_alignment_group lane stage with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_alignment_offsets lane stage := match reference_alignment_group lane stage with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
Lemma reference_alignment_member lane stage : (lane < 6)%coq_nat -> (stage < 15)%coq_nat ->
 List.In (reference_alignment_node lane stage,reference_alignment_expression lane stage) (reference_alignment_nodes lane stage).
Proof.
 intros Lane Stage.
'''
for row in rows:
 out+=' destruct lane as [|lane].\n {\n'
 for n in row:out+=f' destruct stage as [|stage];[exact reference_control_member_{n}|].\n'
 out+=' lia. }\n'
out+=' lia.\nQed.\n'
out+='''Theorem reference_alignment_node_step invalid old result lane stage ground word :
 (lane < 6)%coq_nat -> (stage < 15)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_alignment_expression lane stage) old old = Some (Gval ground word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (reference_alignment_node lane stage) result = Some (Gval ground word).
Proof.
 intros Lane Stage Eval Step.
 eapply (reference_redirect_ground_step (reference_alignment_offsets lane stage) (reference_alignment_nodes lane stage) _ (reference_alignment_expression lane stage));
 [unfold reference_alignment_offsets,reference_alignment_nodes;destruct (reference_alignment_group lane stage) as [|[|group]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold reference_alignment_offsets;destruct (reference_alignment_group lane stage) as [|[|group]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]
 |apply reference_alignment_member;assumption|exact Eval|exact Step].
Qed.
Definition reference_alignment_test lane b0 b1 := if Nat.eqb lane 3 then true else if Nat.eqb lane 1 || Nat.eqb lane 4 then negb (b0 || b1) else negb b0.
Theorem reference_alignment_guard_history invalid history limit start lane b0 b1 b2 rest :
 (lane < 6)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (reference_alignment_node lane 3) (history i) = Some (Gval (Fuint 32) (b0::b1::b2::rest))) ->
 forall time, (Nat.add start 15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_alignment_node lane 14) (history time) = Some (Gval (Fuint 1) [::reference_alignment_test lane b0 b1]).
Proof.
 intros Lane Steps Address.
'''
vals={0:(1,'[::false]',[]),4:(3,'[::b0;b1;b2]',['Address']),5:(1,'[::negb (b0 || b1 || b2)]',['V4']),6:(1,'[::Nat.eqb lane 1 || Nat.eqb lane 4]',[]),7:(2,'[::b0;b1]',['Address']),8:(1,'[::negb (b0 || b1)]',['V7']),9:(1,'[::negb (Nat.eqb lane 1 || Nat.eqb lane 3 || Nat.eqb lane 4)]',[]),10:(1,'[::b0]',['Address']),11:(1,'[::negb b0]',['V10']),12:(1,'[::if Nat.eqb lane 1 || Nat.eqb lane 3 || Nat.eqb lane 4 then true else negb b0]',['V9','V11']),13:(1,'[::reference_alignment_test lane b0 b1]',['V6','V8','V12']),14:(1,'[::reference_alignment_test lane b0 b1]',['V0','V5','V13'])}
for stage,(width,bits,deps) in vals.items():
 out+=f''' assert (V{stage} : forall time, (Nat.add start {stage+1} <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane {stage}) (history time) = Some (Gval (Fuint {width}) ({bits}))).
 {{ intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
'''
 for d in deps:out+=f' pose proof ({d} time ltac:(lia) ltac:(lia)) as H{d}.\n'
 out+=' do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;\n'
 exs=' '.join('reference_control_expr_'+str(row[stage]) for row in rows)
 out+=f' cbn [{exs} eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr\' eval_type_of_ref];\n'
 if deps:
  out+=' cbn [reference_alignment_node reference_alignment_rows nth] in '+','.join('H'+d for d in deps)+';\n'
  out+=' rewrite '+' '.join('H'+d for d in deps)+';unfold eval_type_of_expr;cbn [type_of_expr\' eval_type_of_ref];rewrite '+' '.join('?H'+d for d in deps)+';\n'
 out+=' destruct b0,b1,b2,rest;reflexivity|]);lia. }\n'
out+=' intros time Lower Upper. exact (V14 time Lower Upper).\nQed.\n'
p=base/'ReferenceMemoryAlignment.v';mark='(* Alignment address and observed interfaces. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
