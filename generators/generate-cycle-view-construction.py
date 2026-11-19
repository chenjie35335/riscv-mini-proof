"""Construct a cycle snapshot from concrete actual scalar/register observations."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
words=[('front_instruction',7748,32),('commit_instruction',7750,32),('fetch_pc',7768,33),('front_pc',7749,32),('commit_pc',7751,32),('reference_pc',7331,32),('left',7816,32),('right',7819,32),('pending_alu',7752,32),('write_data',786,32),('destination',7805,5)]
bools=[('write_enabled',7757),('early_bubble',7945),('late_bubble',7947),('delayed_redirect',7760),('started',7762)]
fields=[(n,w)for _,n,w in words]+[(n,1)for _,n in bools]+[(7756,2)]
s='''Require Import CycleView CoreSocModel ComparisonNodes RFWriteEffect RFArchitecturalNormalRelation RFReferenceNopHistory RFArchitecturalRelation ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition cycle_word (env:VM.t hvalue) (node:VarOrder.T) : bits :=
 match VM.find node env with Some(Gval _ word)=>word | _=>[::] end.
Lemma cycle_word_concrete env node width : map_uint_concrete node width env ->
 size(cycle_word env node)=width /\ VM.find node env=Some(Gval(Fuint width)(cycle_word env node)).
Proof. intros[word[Size Value]]. unfold cycle_word;rewrite Value;split;[exact Size|reflexivity]. Qed.
Lemma cycle_bool_concrete env node : map_uint_concrete node 1 env ->
 VM.find node env=Some(Gval(Fuint 1)[::nth false(cycle_word env node)0]).
Proof.
 intros[word[Size Value]]. unfold cycle_word;rewrite Value.
 destruct word as[|b[|extra rest]];cbn in Size;try discriminate Size;reflexivity.
Qed.
Lemma cycle_select_concrete env node : map_uint_concrete node 2 env ->
 VM.find node env=Some(Gval(Fuint 2)[::nth false(cycle_word env node)0;nth false(cycle_word env node)1]).
Proof.
 intros[word[Size Value]]. unfold cycle_word;rewrite Value.
 destruct word as[|a[|b[|extra rest]]];cbn in Size;try discriminate Size;reflexivity.
Qed.
'''
s+='Definition cycle_scalar_fields : list(nat*nat) := [::'+';'.join(f'({n}%nat,{w}%nat)'for n,w in fields)+'].\n'
s+='Definition cycle_scalars_concrete env := forall node width, List.In(node,width)cycle_scalar_fields ->map_uint_concrete(N.of_nat node)width env.\n'
s+='Definition cycle_snapshot env : cycle_view := {|\n cv_dut_bank:=fun index=>cycle_word env(N.of_nat(851+index)%nat);\n cv_reference_bank:=fun index=>cycle_word env(N.of_nat(7299+index)%nat);\n'
s+=';\n'.join(f' cv_{name}:=cycle_word env {n}'for name,n,_ in words)+';\n'
s+=';\n'.join(f' cv_{name}:=nth false(cycle_word env {n})0'for name,n in bools)+';\n cv_write_select_low:=nth false(cycle_word env 7756)0;\n cv_write_select_high:=nth false(cycle_word env 7756)1 |}.\n'
s+='''Theorem cycle_snapshot_at env :
 rf_architectural_registers_concrete env ->cycle_scalars_concrete env ->cycle_view_at env(cycle_snapshot env).
Proof.
 intros Registers Scalars. constructor;cbn [cycle_snapshot].
 - intros index Index. apply cycle_word_concrete. apply Registers. apply rf_dut_register_member;exact Index.
 - intros index Index. apply cycle_word_concrete. apply Registers. apply rf_reference_register_member;exact Index.
'''
# projection constructor order follows CycleView.
for name,n,w in words:
 i=fields.index((n,w));s+=f' - apply(proj2(cycle_word_concrete env {n} {w} (Scalars {n}%nat {w}%nat ltac:(apply(List.nth_error_In cycle_scalar_fields {i}%nat);vm_compute;reflexivity)))).\n'
# enabled, select, early,late,redirect,started
for name,n in bools[:1]:
 i=fields.index((n,1));s+=f' - apply cycle_bool_concrete. exact(Scalars {n}%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields {i}%nat);vm_compute;reflexivity)).\n'
s+=f' - apply cycle_select_concrete. exact(Scalars 7756%nat 2%nat ltac:(apply(List.nth_error_In cycle_scalar_fields {fields.index((7756,2))}%nat);vm_compute;reflexivity)).\n'
for name,n in bools[1:]:
 i=fields.index((n,1));s+=f' - apply cycle_bool_concrete. exact(Scalars {n}%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields {i}%nat);vm_compute;reflexivity)).\n'
for n,w in [(7768,33),(7331,32),(7816,32),(7819,32),(7752,32),(786,32)]:
 i=fields.index((n,w));s+=f' - exact(proj1(cycle_word_concrete env {n} {w} (Scalars {n}%nat {w}%nat ltac:(apply(List.nth_error_In cycle_scalar_fields {i}%nat);vm_compute;reflexivity)))).\n'
s+='Qed.\n'
p=base/'CycleViewConstruction.v';mark='(* The abstraction preserves the existing PC invariant in both directions. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(s+mark+tail)
