Require Import RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ReferenceInstructionDecode CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma rf_execute_decode_selected which instruction target count :(target<count)%coq_nat ->
 (forall stage,(stage<count)%coq_nat ->dut_decode_test instruction(Nat.sub 48 stage)=Nat.eqb stage target) ->
 load_execute_decode which instruction count=from_N(load_execute_width which)(load_execute_row which(Nat.sub 48 target)).
Proof.
 induction count as[|count IH];intros Bound Choices;[lia|].
 cbn[load_execute_decode]. rewrite(Choices count ltac:(lia)).
 destruct(Nat.eq_dec count target)as[Same|Different].
 - subst count. rewrite Nat.eqb_refl;reflexivity.
 - rewrite(proj2(Nat.eqb_neq count target)Different). apply IH;[lia|intros stage Stage;apply Choices;lia].
Qed.
Definition rf_isa_execute_control row which :=load_execute_row which(Nat.sub 48(rf_wb_class_index row)).
Theorem rf_isa_execute_decode instruction row which :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(rf_isa_execute_control row which).
Proof.
 intros Row Match. destruct(rf_wb_class_certificate row Row)as[Bound Rest].
 apply(rf_execute_decode_selected which(to_N instruction)(rf_wb_class_index row)49 Bound).
 intros stage Stage. rewrite(rf_dut_decode_wb_choice instruction(Nat.sub 48 stage)ltac:(lia)).
 assert(Inverse:Nat.sub 48(Nat.sub 48 stage)=stage)by lia. rewrite Inverse.
 exact(rf_wb_choice_onehot instruction row stage Row Stage Match).
Qed.
Theorem rf_isa_execute_control_history inputs path history limit instruction row which :
 (row<37)%coq_nat ->(which<4)%coq_nat ->size instruction=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 forall time,(55<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(load_execute_wire_target which true)(history time)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(rf_isa_execute_control row which))).
Proof.
 intros Row Which Size Match Steps Front time Lower Upper.
 rewrite -(rf_isa_execute_decode instruction row which Row Match).
 exact(load_execute_decode_history inputs path history limit instruction which Which Steps Front Size time Lower Upper).
Qed.
