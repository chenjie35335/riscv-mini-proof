Require Import WriteEnableNormalized FormalDeclaredWireCheck DUTRedirectDecode StoreWriteGateHistory.
From Coq Require Import Lia.
Require Import StoreWriteValidNodes CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_valid_true_8030 invalid old current result :
 VM.find 8028 old=Some(Gval(Fuint 1)[::true]) ->
 VM.find 8029 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8030 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Guard Step. eapply(store_write_valid_node_step 8030 store_write_valid_expr_8030 invalid old current result).
 - unfold store_write_valid_nodes. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8030 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source Guard. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_true_8081 invalid old current result :
 VM.find 8030 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8081 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8081 store_write_valid_expr_8081 invalid old current result).
 - unfold store_write_valid_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8081 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_true_8082 invalid old current result :
 VM.find 8081 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8082 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8082 store_write_valid_expr_8082 invalid old current result).
 - unfold store_write_valid_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8082 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_true_8202 invalid old current result :
 VM.find 8082 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8202 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Step. eapply(store_write_valid_node_step 8202 store_write_valid_expr_8202 invalid old current result).
 - unfold store_write_valid_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_write_valid_expr_8202 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.
Lemma store_write_valid_port_true invalid old current result :
 VM.find 8202 old=Some(Gval(Fuint 1)[::true]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 1478 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Step. eapply declared_wire_checked_value;
 [exact write_valid_certificate_1478|exact Source|reflexivity|exact Step].
Qed.
Theorem store_write_valid_true_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::true])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8029(history t)=Some(Gval(Fuint 1)[::true])) ->
 forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1478(history t)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Steps Valid Gate [|[|[|[|[|t]]]]] Lower Upper;try lia.
 eapply(store_write_valid_port_true invalid (history(S(S(S(S t)))))(history(S(S(S(S t)))))(history(S(S(S(S(S t)))))));[|apply Steps;lia].
 eapply(store_write_valid_true_8202 invalid (history(S(S(S t))))(history(S(S(S t))))(history(S(S(S(S t))))));[|apply Steps;lia].
 eapply(store_write_valid_true_8082 invalid (history(S(S t)))(history(S(S t)))(history(S(S(S t)))));[|apply Steps;lia].
 eapply(store_write_valid_true_8081 invalid (history(S t))(history(S t))(history(S(S t))));[|apply Steps;lia].
 pose proof(Gate t ltac:(lia)ltac:(lia))as Bit.
 exact(store_write_valid_true_8030 invalid (history t)(history t)(history(S t))(Valid t ltac:(lia)ltac:(lia))Bit(Steps t ltac:(lia))).
Qed.
Theorem store_write_valid_true_no_exception_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::true])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 128(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1478(history t)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Steps Valid NoException t Lower Upper.
 eapply(store_write_valid_true_history invalid history limit (S start) Steps).
 - intros u Low High. apply Valid;lia.
 - intros [|u] Low High;[lia|].
   exact(store_write_gate_true_step invalid (history u) (history u) (history(S u))
     (NoException u ltac:(lia) ltac:(lia)) (Steps u ltac:(lia))).
 - lia.
 - exact Upper.
Qed.
Require Import StoreWriteGateHistory StoreWriteValidRegister ObservedLegalNoTrap ExceptionSourceNoTrap
 CoreSocModel ComparisonNodes FormalLocalHistory ObservedJointRegisterConcrete
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_write_valid_true_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 8028(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 1478(top_environment observed)=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Observe Legal Reset Valid.
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
   exists word;split;[exact Size|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(ValidHistory:forall t,(41<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::true])).
 { intros t Lower Upper.
   rewrite(store_write_valid_register_history _ history 9259 Steps t Upper).
   rewrite <-(store_write_valid_register_history _ history 9259 Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Valid. }
 rewrite <-Last.
 eapply(store_write_valid_true_no_exception_history _ history 9259 41 Steps ValidHistory).
 - exact(exception_source_false_after_settling (generated_observation_input inputs k) nil history Boundary Steps NoTrap).
 - vm_compute;lia.
 - vm_compute;lia.
Qed.
