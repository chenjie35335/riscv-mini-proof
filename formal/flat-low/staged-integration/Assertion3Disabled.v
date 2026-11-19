Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_expr_7579 := (@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 1394))).
Definition reference_event_tail_7579 := match straight_drop 8049 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7579 : straight_drop 8048 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7579 reference_event_expr_7579) reference_event_tail_7579).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7579 : memory_suffix_safe flat_memories 7579 reference_event_tail_7579.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7579 : has_register 7579 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7579 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7579 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7579 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7579 reference_event_suffix_7579 reference_event_nonregister_7579 Step).
Qed.
Definition reference_event_expr_7580 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7579)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition reference_event_tail_7580 := match straight_drop 8050 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_7580 : straight_drop 8049 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7580 reference_event_expr_7580) reference_event_tail_7580).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_7580 : memory_suffix_safe flat_memories 7580 reference_event_tail_7580.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_7580 : has_register 7580 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_7580 invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7580 result = eval_hfexpr_with_memory flat_memories reference_event_expr_7580 old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_7580 reference_event_suffix_7580 reference_event_nonregister_7580 Step).
Qed.

Require Import ComparisonNodes Assertion0GuardNodes Assertion2ResetGuard Assertion44Enable CoreSocModel FormalObservedHistory FormalLocalHistory ExternalReset FormalResetPreparation FormalTopResetHold StagedIterationCount CycleView.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma assertion3_guard_after_two invalid s0 s1 s2 bit :
 VM.find 1394 s0 = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7580 s2 = Some (Gval (Fuint 1) [::negb bit]).
Proof.
 intros Reset S1 S2.
 assert (Extract : VM.find 7579 s1 = Some (Gval (Fuint 1) [::bit])).
 { rewrite (reference_event_equation_7579 invalid s0 s0 s1 S1).
   cbn [reference_event_expr_7579 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Reset. destruct bit; reflexivity. }
 rewrite (reference_event_equation_7580 invalid s1 s1 s2 S2).
 cbn [reference_event_expr_7580 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Extract. destruct bit; reflexivity.
Qed.
Theorem assertion3_reset_guard_observed memory inputs k observed bit :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k bit ->
 VM.find 7580(top_environment observed)=Some(Gval(Fuint 1)[::negb bit]).
Proof.
 intros Observe Reset.
 destruct(assertion2_history_with_reset memory inputs k observed bit Observe Reset)as[history[Last[Steps Resets]]].
 pose proof(assertion44_checker_reset_after_three _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)bit
 (Resets 9254%nat ltac:(vm_compute;lia))(Steps 9254%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as CheckerReset.
 rewrite <- Last.
 exact(assertion3_guard_after_two _ (history 9257%nat)(history 9258%nat)(history 9259%nat)bit CheckerReset
 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
Theorem assertion3_reset_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->cycle_reset inputs k true ->generated_assert_m0_3_local(top_environment observed).
Proof.
 intros Observe Reset. pose proof(assertion3_reset_guard_observed memory inputs k observed true Observe Reset)as Guard.
 unfold generated_assert_m0_3_local,generated_expr_true. cbn[eval_hfexpr eval_href]. rewrite Guard. vm_compute;intro Impossible;discriminate Impossible.
Qed.

Require Import FormalAssertionDischarge StoreNonStoreReachable ReferenceNonStoreWriteObserved MemoryRequestObservedSemantics StoreTypeCorrespondence
 StoreWriteGateHistory StoreWriteValidRegister ObservedLegalNoTrap ExceptionSourceNoTrap
 CoreSocModel ComparisonNodes FormalLocalHistory ObservedJointRegisterConcrete
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization FormalResetPreparation
 Assertion5NoWrite Assertion5ResetGuard CycleView.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nonstore_write_valid_assertion_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 generated_assert_m0_3_local(top_environment observed).
Proof.
 intros Observe Legal Reset Instruction NonStore.
 pose proof(store_nonstore_write_valid_observed memory inputs k observed instruction Observe Legal Instruction NonStore)as Valid.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 destruct(reference_nonstore_decode_observed memory inputs k observed instruction enabled Observe Legal Instruction Enabled NonStore)as[SB[SH SW]].
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
   exists word;split;[exact Size|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(ValidHistory:forall t,(41<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::false])).
 { intros t Lower Upper.
   rewrite(store_write_valid_register_history _ history 9259 Steps t Upper).
   rewrite <-(store_write_valid_register_history _ history 9259 Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Valid. }
 destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[env[Env InitialReset]].
 assert(Reset0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof(legal_local_reset_history _ history 9259 false Steps Reset0)as Resets.
 assert(DUT:VM.find 1478(history 9258%nat)=Some(Gval(Fuint 1)[::false])).
 { eapply(store_write_valid_false_no_exception_history _ history 9259 41 Steps ValidHistory).
   - exact(exception_source_false_after_settling (generated_observation_input inputs k)nil history Boundary Steps NoTrap).
   - vm_compute;lia.
   - vm_compute;lia. }
 assert(Reference:VM.find 1523(history 9258%nat)=Some(Gval(Fuint 1)[::false])).
 { apply(reference_write_false_history_from_last (generated_observation_input inputs k)nil history false enabled Steps Resets);
   try(rewrite Last;assumption);vm_compute;lia. }
 rewrite <-Last.
 eapply(assertion_3_from_enabled_agreement _ (history 9258%nat)(history 9258%nat)(history 9259%nat)(Steps 9258%nat ltac:(vm_compute;lia))).
 intro EnabledAssertion. exists 1%nat,1%nat,[::false],[::false]. repeat split;try assumption;reflexivity.
Qed.
