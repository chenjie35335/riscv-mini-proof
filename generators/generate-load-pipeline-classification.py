"""Strengthen the shared load pipeline to full instruction/type classification."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration';old=(base/'LoadTypeCorrespondence.v').read_text()
imports='\n'.join(line for line in old.splitlines() if line.startswith('Require Import '))
out='Require Import LoadTypeCorrespondence.\n'+imports+'''
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top generated_run.
Lemma load_pipeline_row_classify instruction row : (row < 49)%coq_nat -> dut_decode_test instruction row = true ->
 from_N 3 (load_type_row row) = from_N 3 0 \/
 exists lane, (lane < 5)%coq_nat /\\ N.land instruction 28799 = load_type_lane_code lane /\\ from_N 3 (load_type_row row) = from_N 3 (load_type_lane_kind lane).
Proof.
 intros Row Guard.
'''
for row in range(49):
 out+=' destruct row as [|row].\n'
 if 10<=row<=14:
  lane=14-row
  out+=f''' {{ right. exists {lane}%nat. split;[lia|]. split;[|reflexivity].
 cbv [dut_decode_test dut_decode_row dut_decode_certificate_rows nth hd dd_mask dd_code] in Guard.
 apply N.eqb_eq in Guard. exact Guard. }}
'''
 else:out+=' { left;reflexivity. }\n'
out+=' lia.\nQed.\n'
out+='''Theorem load_pipeline_decode_classify instruction count : (count <= 49)%coq_nat ->
 load_type_decode instruction count = from_N 3 0 \/
 exists lane, (lane < 5)%coq_nat /\\ N.land instruction 28799 = load_type_lane_code lane /\\ load_type_decode instruction count = from_N 3 (load_type_lane_kind lane).
Proof.
 induction count as [|count IH];intro Count;[left;reflexivity|].
 cbn [load_type_decode]. destruct (dut_decode_test instruction (Nat.sub 48 count)) eqn:Guard.
 - apply load_pipeline_row_classify;[lia|exact Guard].
 - apply IH;lia.
Qed.
Definition load_pipeline_exact env : Prop := forall instruction,
 VM.find 7750 env = Some (Gval (Fuint 32) instruction) ->
 VM.find 7755 env = Some (Gval (Fuint 3) (load_type_decode (to_N instruction) 49)).
'''
normal=old.split('Theorem load_type_normal_fullhistory',1)[1].split('Require Import StagedCircuitRegisterHold',1)[0]
normal='Theorem load_pipeline_normal_fullhistory'+normal
normal=normal.replace('load_type_invariant result.','load_pipeline_exact result.')
a=normal.index(' intros instruction lane Lane Instruction Load.')
normal=normal[:a]+''' intros instruction Instruction. rewrite NextInst in Instruction. inversion Instruction;subst instruction. exact NextType.
Qed.
'''
out+=normal
p=base/'LoadPipelineClassification.v';mark='(* Reset and reachable classification. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
