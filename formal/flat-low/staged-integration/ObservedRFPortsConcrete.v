Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory ObservedJointRegisterConcrete JointUpdateBoundaryHistory JointUpdateFromBoundaryHistory JointUpdateDependencyRanks JointUpdateGraphPropagation JointBoundaryRegisters ConcreteRegisterInitialization FormalDeclaredConnectionObservation FormalDeclaredUnaryObservation DataAddressConnectionCertificates JointUpdateConnectionCertificates ReferenceImmediateTypes RFReadForwarding FormalSuccessfulNodeEvaluation FormalTypedNodeEquation SelectedNodeSafety DataAddressPositionCertificate DataAddressSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_adapted_ground_uint source width ground word :
 adapt_hvalue_as_type source(Gtyp(Fuint width))=Some(Gval ground word) ->
 ground=Fuint width /\size word=width.
Proof.
 destruct source as[g raw|e a|f|t|t|t];cbn[adapt_hvalue_as_type];try discriminate.
 - destruct g;try discriminate. intro Equal;inversion Equal;subst. split;[reflexivity|].
 unfold zext_to. rewrite size_zext. apply subnKC. rewrite size_take. exact(geq_minl _ _).
 - destruct(ftype_mux false t(Gtyp(Fuint width)));discriminate.
 - destruct(ftype_mux false t(Gtyp(Fuint width)));discriminate.
 - destruct(ftype_mux false t(Gtyp(Fuint width)));discriminate.
Qed.
Lemma rf_mux_ground_uint invalid site old condition yes no yw nw ground word :
 immediate_leaf old yes yw ->immediate_leaf old no nw ->
 eval_hfexpr_validif_policy invalid site flat_memories(@Emux VarOrder.T condition yes no)old old=Some(Gval ground word) ->
 ground=Fuint(maxn yw nw) /\size word=maxn yw nw.
Proof.
 intros Yes No Eval. destruct(immediate_leaf_value old yes yw Yes)as[yv[YT[YE YV]]].
 destruct(immediate_leaf_value old no nw No)as[nv[NT[NE NV]]].
 cbn[eval_hfexpr_validif_policy]in Eval.
 destruct(eval_hfexpr_validif_policy invalid _ flat_memories condition old old)as[value|]eqn:C;[|discriminate].
 destruct value as[g bits|elt values|fields|typ|typ|typ];try discriminate.
 - destruct g;try discriminate. destruct(is_zero bits);rewrite ?YV ?NV ?YE ?NE in Eval;
 unfold extend_hvalue_as_type in Eval;rewrite ?YT ?NT in Eval;cbn[ftype_mux fgtyp_mux]in Eval;
 try rewrite(maxnC nw yw)in Eval;eapply rf_adapted_ground_uint;exact Eval.
 - destruct typ as[g|elt count|fields];try discriminate;destruct g;try discriminate;
 rewrite YE NE in Eval;cbn[ftype_mux fgtyp_mux option_map]in Eval;discriminate.
 - destruct typ as[g|elt count|fields];try discriminate;destruct g;try discriminate;
 rewrite YE NE in Eval;cbn[ftype_mux fgtyp_mux option_map]in Eval;discriminate.
 - destruct typ as[g|elt count|fields];try discriminate;destruct g;try discriminate;
 rewrite YE NE in Eval;cbn[ftype_mux fgtyp_mux option_map]in Eval;discriminate.
Qed.
Definition rf_concrete_wire which :VarOrder.T:=nth 0[::782;783;786]which.
Lemma rf_concrete_wire_step which invalid old result ground word :(which<3)%coq_nat ->
 VM.find(rf_concrete_wire which)result=Some(Gval ground word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 map_uint_concrete(rf_concrete_wire which)32 result.
Proof. intros Bound Ground Step.
destruct which as[|which]. {
 destruct(declared_connection_observation 791 flat_statements data_address_connection_782_decl data_address_connection_782_mid data_address_connection_782_tail 782 917 32 invalid flat_memories old old result data_address_connection_782_position data_address_connection_782_split data_address_connection_782_straight data_address_connection_782_mid_safe data_address_connection_782_tail_safe data_address_connection_782_nonregister (Logic.eq_refl _) Step)as[source[value[Source[Adapt Value]]]].
 change(VM.find 782 result=Some(Gval ground word))in Ground. rewrite Ground in Value;inversion Value;subst value.
 destruct(rf_adapted_ground_uint source 32 ground word Adapt)as[Shape Size]. subst ground. exists word;split;assumption. }
destruct which as[|which]. {
 destruct(declared_connection_observation 792 flat_statements data_address_connection_783_decl data_address_connection_783_mid data_address_connection_783_tail 783 952 32 invalid flat_memories old old result data_address_connection_783_position data_address_connection_783_split data_address_connection_783_straight data_address_connection_783_mid_safe data_address_connection_783_tail_safe data_address_connection_783_nonregister (Logic.eq_refl _) Step)as[source[value[Source[Adapt Value]]]].
 change(VM.find 783 result=Some(Gval ground word))in Ground. rewrite Ground in Value;inversion Value;subst value.
 destruct(rf_adapted_ground_uint source 32 ground word Adapt)as[Shape Size]. subst ground. exists word;split;assumption. }
destruct which as[|which]. {
 destruct(declared_unary_connection_observation 795 flat_statements joint_update_connection_786_decl joint_update_connection_786_mid joint_update_connection_786_tail 786 7937 (Uextr 31 0) 32 invalid flat_memories old old result joint_update_connection_786_position joint_update_connection_786_split joint_update_connection_786_straight joint_update_connection_786_mid_safe joint_update_connection_786_tail_safe joint_update_connection_786_nonregister (Logic.eq_refl _) Step)as[source[value[Source[Adapt Value]]]].
 change(VM.find 786 result=Some(Gval ground word))in Ground. rewrite Ground in Value;inversion Value;subst value.
 destruct(rf_adapted_ground_uint source 32 ground word Adapt)as[Shape Size]. subst ground. exists word;split;assumption. }
lia. Qed.
Lemma rf_forward_ground_concrete second invalid old result alu raw ground word :
 VM.find 7752 old=Some(Gval(Fuint 32)alu) ->
 VM.find(rf_forward_raw second)old=Some raw ->type_of_val raw=Gtyp(Fuint 32) ->
 VM.find(rf_forward_node second)result=Some(Gval ground word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 map_uint_concrete(rf_forward_node second)32 result.
Proof.
 intros Alu Raw Typed Ground Step.
 destruct(selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes _ _ data_address_actual_node_expressions data_address_actual_nodes_safe(rf_forward_members second))as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step)as[value Eval].
 assert(Yes:immediate_leaf old(@Eref VarOrder.T(@Eid VarOrder.T 7752))32).
 { eapply immediate_ref;[exact Alu|reflexivity]. }
 assert(No:immediate_leaf old(@Eref VarOrder.T(@Eid VarOrder.T(rf_forward_raw second)))32).
 { eapply immediate_ref;[exact Raw|exact Typed]. }
 pose proof(immediate_mux_type _ _ old _ _ _ 32 32 value Yes No Eval)as Shape.
 assert(Output:VM.find(rf_forward_node second)result=Some value).
 { eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Shape|exact Step]. }
 rewrite Ground in Output;inversion Output;subst value.
 destruct(rf_mux_ground_uint _ _ old _ _ _ 32 32 ground word Yes No Eval)as[G Size].
 change(ground=Fuint 32)in G. subst ground. exists word;split;assumption.
Qed.
Definition rf_port_ground_node which :nat:=nth 0%nat [::782%nat;783%nat;786%nat;7816%nat;7819%nat]which.
Lemma rf_port_history_ground inputs path history limit which :
 (which<5)%coq_nat ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<=limit)%coq_nat ->exists bit,VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(100<=t)%coq_nat ->(t<=limit)%coq_nat ->exists ground word,VM.find(N.of_nat(rf_port_ground_node which))(history t)=Some(Gval ground word).
Proof. intros Bound Boundary Reset Steps t Lower Upper.
destruct which as[|which];[exact(joint_update_from_boundary_history inputs path history limit Boundary Reset Steps t 782%nat 37%nat [::917%nat] Upper ltac:(apply(List.nth_error_In joint_update_dependency_ranks 1298%nat);vm_compute;reflexivity)ltac:(lia))|].
destruct which as[|which];[exact(joint_update_from_boundary_history inputs path history limit Boundary Reset Steps t 783%nat 37%nat [::952%nat] Upper ltac:(apply(List.nth_error_In joint_update_dependency_ranks 1299%nat);vm_compute;reflexivity)ltac:(lia))|].
destruct which as[|which];[exact(joint_update_from_boundary_history inputs path history limit Boundary Reset Steps t 786%nat 38%nat [::7937%nat] Upper ltac:(apply(List.nth_error_In joint_update_dependency_ranks 1334%nat);vm_compute;reflexivity)ltac:(lia))|].
destruct which as[|which];[exact(joint_update_from_boundary_history inputs path history limit Boundary Reset Steps t 7816%nat 38%nat [::782%nat;7752%nat;7815%nat] Upper ltac:(apply(List.nth_error_In joint_update_dependency_ranks 1335%nat);vm_compute;reflexivity)ltac:(lia))|].
destruct which as[|which];[exact(joint_update_from_boundary_history inputs path history limit Boundary Reset Steps t 7819%nat 38%nat [::783%nat;7752%nat;7818%nat] Upper ltac:(apply(List.nth_error_In joint_update_dependency_ranks 1336%nat);vm_compute;reflexivity)ltac:(lia))|].
lia. Qed.
Require Import FormalRFDestination.
Theorem rf_ports_concrete_history inputs path history limit :
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<=limit)%coq_nat ->exists bit,VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(102<=t)%coq_nat ->(t<=limit)%coq_nat ->
 map_uint_concrete 7816 32(history t) /\map_uint_concrete 7819 32(history t) /\map_uint_concrete 786 32(history t) /\map_uint_concrete 7805 5(history t).
Proof.
 intros Boundary Reset Steps [|[|t]] Lower Upper;try lia.
 pose proof(rf_port_history_ground inputs path history limit)as Ground.
 assert(Forward:forall second,map_uint_concrete(rf_forward_node second)32(history(S(S t)))).
 { intro second.
 assert(Raw:map_uint_concrete(rf_forward_raw second)32(history(S t))).
 { destruct second.
 - destruct(Ground 1%nat ltac:(lia)Boundary Reset Steps (S t)ltac:(lia)ltac:(lia))as[g[w V]]. exact(rf_concrete_wire_step 1%nat _ (history t)(history(S t))g w ltac:(lia)V(Steps t ltac:(lia))).
 - destruct(Ground 0%nat ltac:(lia)Boundary Reset Steps (S t)ltac:(lia)ltac:(lia))as[g[w V]]. exact(rf_concrete_wire_step 0%nat _ (history t)(history(S t))g w ltac:(lia)V(Steps t ltac:(lia))). }
 destruct Raw as[raw[Size Raw]].
 assert(Member:List.In(7752%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity. }
 destruct(joint_update_register_history_concrete _ history limit 7752 32 Member(Boundary _ _ Member)Steps(S t)ltac:(lia))as[alu[AS Alu]].
 destruct(Ground (if second then 4%nat else 3%nat)ltac:(destruct second;lia)Boundary Reset Steps (S(S t))ltac:(lia)Upper)as[g[w V]].
 apply(rf_forward_ground_concrete second (formal_invalid_policy inputs path) (history(S t))(history(S(S t)))alu(Gval(Fuint 32)raw)g w Alu Raw (Logic.eq_refl _));[destruct second;exact V|apply Steps;lia]. }
 split;[exact(Forward false)|]. split;[exact(Forward true)|]. split.
 - destruct(Ground 2%nat ltac:(lia)Boundary Reset Steps (S(S t))ltac:(lia)Upper)as[g[w V]]. exact(rf_concrete_wire_step 2%nat _ (history(S t))(history(S(S t)))g w ltac:(lia)V(Steps(S t)ltac:(lia))).
 - assert(Member:List.In(7750%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity. }
 destruct(joint_update_register_history_concrete _ history limit 7750 32 Member(Boundary _ _ Member)Steps(S t)ltac:(lia))as[instruction[Size Instruction]].
 exists(drop 7(take 12 instruction));split;[exact(rf_destination_width instruction Size)|].
 exact(rf_destination_node _ (history(S t))(history(S t))(history(S(S t)))instruction Instruction(Steps(S t)ltac:(lia))).
Qed.
Theorem observed_rf_ports_concrete memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 map_uint_concrete 7816 32(top_environment observed) /\map_uint_concrete 7819 32(top_environment observed) /\map_uint_concrete 786 32(top_environment observed) /\map_uint_concrete 7805 5(top_environment observed).
Proof.
 intros Observe Legal.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member. destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]]. exists word;split;[exact Size|].
 pose proof(joint_update_register_history_same _ history 9259 node width Member Steps 9259%nat ltac:(vm_compute;lia))as Hold.
 rewrite Last in Hold. rewrite<-Hold;exact Value. }
 assert(R:forall t,(t<=9259)%coq_nat ->exists bit,VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])).
 { intros t Upper. exists reset;apply Resets;exact Upper. }
 rewrite<-Last. exact(rf_ports_concrete_history (generated_observation_input inputs k)nil history 9259 Boundary R Steps 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
Qed.
