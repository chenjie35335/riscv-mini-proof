Require Import RFWriteEffect RFReferenceWriteEffect RFReferenceNopHistory.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Local Open Scope N_scope.
Definition ref_write_word (env:VM.t hvalue) stage : bits :=
 match VM.find(rf_reference_write_data stage)env with Some(Gval _ raw)=>take 32 raw|_=>zeros 32 end.
Definition ref_write_bit (env:VM.t hvalue)(node:VarOrder.T) : bool :=
 match VM.find node env with Some(Gval _ (bit::_))=>bit|_=>false end.
Definition ref_write_guard env stage :=ref_write_bit env(rf_reference_chain_guard stage).
Definition ref_write_permission env stage :=ref_write_bit env(rf_reference_permission_node stage).
Definition ref_write_destination (env:VM.t hvalue) : bits :=
 match VM.find 3221 env with Some(Gval _ raw)=>raw|_=>zeros 5 end.
Definition ref_write_effect env :=
 if ref_write_bit env 1707 then rf_reference_effect(ref_write_guard env)(ref_write_permission env)(ref_write_word env)(to_nat(ref_write_destination env))36 else RFNoWrite.
Lemma ref_write_word_actual env stage width raw :
 VM.find(rf_reference_write_data stage)env=Some(Gval(Fuint width)raw) ->ref_write_word env stage=take 32 raw.
Proof. intro Value. unfold ref_write_word;rewrite Value;reflexivity. Qed.
Lemma ref_write_bit_actual env node bit :
 VM.find node env=Some(Gval(Fuint 1)[::bit]) ->ref_write_bit env node=bit.
Proof. intro Value. unfold ref_write_bit;rewrite Value;reflexivity. Qed.
