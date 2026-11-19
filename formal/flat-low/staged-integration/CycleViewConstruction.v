Require Import CycleView CoreSocModel ComparisonNodes RFWriteEffect RFArchitecturalNormalRelation RFReferenceNopHistory RFArchitecturalRelation ConcreteRegisterInitialization.
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
Definition cycle_scalar_fields : list(nat*nat) := [::(7748%nat,32%nat);(7750%nat,32%nat);(7768%nat,33%nat);(7749%nat,32%nat);(7751%nat,32%nat);(7331%nat,32%nat);(7816%nat,32%nat);(7819%nat,32%nat);(7752%nat,32%nat);(786%nat,32%nat);(7805%nat,5%nat);(7757%nat,1%nat);(7945%nat,1%nat);(7947%nat,1%nat);(7760%nat,1%nat);(7762%nat,1%nat);(7756%nat,2%nat)].
Definition cycle_scalars_concrete env := forall node width, List.In(node,width)cycle_scalar_fields ->map_uint_concrete(N.of_nat node)width env.
Definition cycle_snapshot env : cycle_view := {|
 cv_dut_bank:=fun index=>cycle_word env(N.of_nat(851+index)%nat);
 cv_reference_bank:=fun index=>cycle_word env(N.of_nat(7299+index)%nat);
 cv_front_instruction:=cycle_word env 7748;
 cv_commit_instruction:=cycle_word env 7750;
 cv_fetch_pc:=cycle_word env 7768;
 cv_front_pc:=cycle_word env 7749;
 cv_commit_pc:=cycle_word env 7751;
 cv_reference_pc:=cycle_word env 7331;
 cv_left:=cycle_word env 7816;
 cv_right:=cycle_word env 7819;
 cv_pending_alu:=cycle_word env 7752;
 cv_write_data:=cycle_word env 786;
 cv_destination:=cycle_word env 7805;
 cv_write_enabled:=nth false(cycle_word env 7757)0;
 cv_early_bubble:=nth false(cycle_word env 7945)0;
 cv_late_bubble:=nth false(cycle_word env 7947)0;
 cv_delayed_redirect:=nth false(cycle_word env 7760)0;
 cv_started:=nth false(cycle_word env 7762)0;
 cv_write_select_low:=nth false(cycle_word env 7756)0;
 cv_write_select_high:=nth false(cycle_word env 7756)1 |}.
Theorem cycle_snapshot_at env :
 rf_architectural_registers_concrete env ->cycle_scalars_concrete env ->cycle_view_at env(cycle_snapshot env).
Proof.
 intros Registers Scalars. constructor;cbn [cycle_snapshot].
 - intros index Index. apply cycle_word_concrete. apply Registers. apply rf_dut_register_member;exact Index.
 - intros index Index. apply cycle_word_concrete. apply Registers. apply rf_reference_register_member;exact Index.
 - apply(proj2(cycle_word_concrete env 7748 32 (Scalars 7748%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 0%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7750 32 (Scalars 7750%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 1%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7768 33 (Scalars 7768%nat 33%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 2%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7749 32 (Scalars 7749%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 3%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7751 32 (Scalars 7751%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 4%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7331 32 (Scalars 7331%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 5%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7816 32 (Scalars 7816%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 6%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7819 32 (Scalars 7819%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 7%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7752 32 (Scalars 7752%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 8%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 786 32 (Scalars 786%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 9%nat);vm_compute;reflexivity)))).
 - apply(proj2(cycle_word_concrete env 7805 5 (Scalars 7805%nat 5%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 10%nat);vm_compute;reflexivity)))).
 - apply cycle_bool_concrete. exact(Scalars 7757%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 11%nat);vm_compute;reflexivity)).
 - apply cycle_select_concrete. exact(Scalars 7756%nat 2%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 16%nat);vm_compute;reflexivity)).
 - apply cycle_bool_concrete. exact(Scalars 7945%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 12%nat);vm_compute;reflexivity)).
 - apply cycle_bool_concrete. exact(Scalars 7947%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 13%nat);vm_compute;reflexivity)).
 - apply cycle_bool_concrete. exact(Scalars 7760%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 14%nat);vm_compute;reflexivity)).
 - apply cycle_bool_concrete. exact(Scalars 7762%nat 1%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 15%nat);vm_compute;reflexivity)).
 - exact(proj1(cycle_word_concrete env 7768 33 (Scalars 7768%nat 33%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 2%nat);vm_compute;reflexivity)))).
 - exact(proj1(cycle_word_concrete env 7331 32 (Scalars 7331%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 5%nat);vm_compute;reflexivity)))).
 - exact(proj1(cycle_word_concrete env 7816 32 (Scalars 7816%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 6%nat);vm_compute;reflexivity)))).
 - exact(proj1(cycle_word_concrete env 7819 32 (Scalars 7819%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 7%nat);vm_compute;reflexivity)))).
 - exact(proj1(cycle_word_concrete env 7752 32 (Scalars 7752%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 8%nat);vm_compute;reflexivity)))).
 - exact(proj1(cycle_word_concrete env 786 32 (Scalars 786%nat 32%nat ltac:(apply(List.nth_error_In cycle_scalar_fields 9%nat);vm_compute;reflexivity)))).
Qed.
(* The abstraction preserves the existing PC invariant in both directions. *)
Require Import PipelinePCRelation.
Theorem cycle_pc_relation_complete env v :
 cycle_view_at env v ->pipeline_pc_relation env ->cycle_pc_aligned v.
Proof.
 intros View [pc [Width [Aligned [PC Phase]]]].
 assert(Eq:pc=cv_reference_pc v) by (pose proof(cva_reference_pc _ _ View);congruence).
 subst pc. split;[exact Aligned|]. unfold cycle_pc_phase.
 destruct Phase as [[Late Commit]|[[Late[Early Front]]|[Late[Early[fetch[Size[Fetch Started]]]]]]].
 - left;split;[pose proof(cva_late_bubble _ _ View);congruence|pose proof(cva_commit_pc _ _ View);congruence].
 - right;left;split;[pose proof(cva_late_bubble _ _ View);congruence|].
   split;[pose proof(cva_early_bubble _ _ View);congruence|pose proof(cva_front_pc _ _ View);congruence].
 - right;right;split;[pose proof(cva_late_bubble _ _ View);congruence|].
   split;[pose proof(cva_early_bubble _ _ View);congruence|].
   assert(Eq:fetch=cv_fetch_pc v)by(pose proof(cva_fetch_pc _ _ View);congruence). subst fetch.
   destruct Started as [[Started NextPC]|[Started NextPC]];[left|right];split;try exact NextPC;
   pose proof(cva_started _ _ View);congruence.
Qed.
Theorem cycle_pc_relation_exact env v :
 cycle_view_at env v ->(cycle_pc_aligned v <-> pipeline_pc_relation env).
Proof. intro View;split;[apply cycle_pc_relation_sound|apply cycle_pc_relation_complete];exact View. Qed.
