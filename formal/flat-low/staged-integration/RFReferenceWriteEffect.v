Require Import CoreSocModel ComparisonNodes RFWriteEffect RFReferenceNopEntry RFReferenceNopStorageCertificates RFPreviewEffect ConcreteDecodeOperations FormalGroundNodeEquation SelectedNodeSafety.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* The reference mux tree widens intermediate arithmetic values.  Only its
   low 32 bits are architectural; upper bits need not be zero. *)
Definition rf_reference_low_word word value := exists width raw,
 value=Gval(Fuint width)raw /\size raw=width /\(32<=width)%nat /\take 32 raw=word.
Lemma rf_reference_low_word_size word value :rf_reference_low_word word value ->size word=32%nat.
Proof. intros[width[raw[Value[Size[Width Low]]]]]. rewrite -Low size_take Size. exact(minn_idPl Width). Qed.
Lemma rf_reference_take_extension raw amount : (32<=size raw)%nat ->take 32(zext amount raw)=take 32 raw.
Proof.
 intro Bound. unfold zext. rewrite take_cat.
 destruct(ltnP 32(size raw))as[Strict|Wide];[reflexivity|].
 assert(Equal:size raw=32%nat)by(apply/eqP;rewrite eqn_leq;apply/andP;split;assumption).
 rewrite Equal subnn take0 cats0. symmetry. apply take_oversize. rewrite Equal. reflexivity.
Qed.
Lemma rf_reference_low_resize word value width :rf_reference_low_word word value ->
 (forall source raw,value=Gval(Fuint source)raw ->(source<=width)%nat) ->
 exists adapted,adapt_hvalue_as_type value(Gtyp(Fuint width))=Some adapted /\rf_reference_low_word word adapted.
Proof.
 intros[source[raw[Value[Size[Wide Low]]]]] Width. subst value.
 specialize(Width source raw (Logic.eq_refl _)).
 exists(Gval(Fuint width)(zext_to width(take width raw))). split;[reflexivity|].
 exists width,(zext_to width(take width raw)). split;[reflexivity|].
 assert(Take:take width raw=raw)by(apply take_oversize;rewrite Size;exact Width).
 rewrite Take. split.
 - unfold zext_to. rewrite size_zext Size. exact(subnKC Width).
 - split;[exact(leq_trans Wide Width)|]. unfold zext_to. rewrite rf_reference_take_extension;[exact Low|rewrite Size;exact Wide].
Qed.
Lemma rf_reference_low_mux mm old condition (yes no:VarOrder.T) invalid site bit left right left_word right_word :
 (forall subsite,eval_hfexpr_validif_policy(isolated_validif_policy invalid)subsite mm condition old old=Some(Gval(Fuint 1)[::bit])) ->
 VM.find yes old=Some left ->rf_reference_low_word left_word left ->
 VM.find no old=Some right ->rf_reference_low_word right_word right ->
 exists value,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site mm
 (@Emux VarOrder.T condition(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))old old=Some value /\
 rf_reference_low_word(if bit then left_word else right_word)value.
Proof.
 intros Condition Left[wl[bl[LValue[LSize[LWidth LLow]]]]] Right[wr[br[RValue[RSize[RWidth RLow]]]]]. subst left right.
 cbn [eval_hfexpr_validif_policy]. rewrite Condition.
 destruct bit;cbn [is_zero eval_hfexpr_validif_policy eval_href_validif_policy];
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Left Right;
 cbn [option_map type_of_val make_ftype_explicit ftype_mux fgtyp_mux extend_hvalue_as_type];
 eapply rf_reference_low_resize.
 - exists wl,bl. repeat split;assumption.
 - intros source raw Equal. inversion Equal;subst. apply leq_maxl.
 - exists wr,br. repeat split;assumption.
 - intros source raw Equal. inversion Equal;subst. apply leq_maxl.
Qed.


(* Generated selector schema: actual model nodes, checked by Coq. *)
Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
Definition rf_reference_write_rows : seq(nat*nat*nat*nat) := [::(3224%nat,3222%nat,1%nat,0%nat);(3539%nat,3537%nat,1%nat,0%nat);(3541%nat,3531%nat,1%nat,0%nat);(3543%nat,3527%nat,1%nat,0%nat);(3545%nat,3524%nat,1%nat,0%nat);(3547%nat,3521%nat,1%nat,0%nat);(3549%nat,3518%nat,1%nat,0%nat);(3551%nat,3514%nat,1%nat,0%nat);(3553%nat,3510%nat,1%nat,0%nat);(3555%nat,3504%nat,1%nat,0%nat);(3557%nat,3503%nat,1%nat,0%nat);(3559%nat,3500%nat,1%nat,0%nat);(3561%nat,3495%nat,1%nat,0%nat);(3563%nat,3488%nat,1%nat,0%nat);(3565%nat,3483%nat,1%nat,0%nat);(3567%nat,3479%nat,1%nat,0%nat);(3569%nat,3475%nat,1%nat,0%nat);(3571%nat,3471%nat,1%nat,0%nat);(3573%nat,3466%nat,1%nat,0%nat);(3575%nat,3461%nat,1%nat,0%nat);(3577%nat,3456%nat,1%nat,0%nat);(3579%nat,3449%nat,2%nat,2966%nat);(3582%nat,3446%nat,2%nat,2949%nat);(3585%nat,3443%nat,2%nat,2679%nat);(3588%nat,3422%nat,2%nat,2664%nat);(3591%nat,3401%nat,2%nat,2649%nat);(3594%nat,3383%nat,1%nat,0%nat);(3596%nat,3365%nat,2%nat,2565%nat);(3599%nat,3346%nat,1%nat,0%nat);(3601%nat,3341%nat,1%nat,0%nat);(3603%nat,3333%nat,1%nat,0%nat);(3605%nat,3323%nat,1%nat,0%nat);(3607%nat,3318%nat,1%nat,0%nat);(3609%nat,3294%nat,1%nat,0%nat);(3611%nat,3286%nat,1%nat,0%nat);(3613%nat,3265%nat,1%nat,0%nat)].
Definition rf_reference_write_row stage := nth(0%nat,0%nat,0%nat,0%nat)rf_reference_write_rows stage.
Definition rf_reference_write_depth stage := let '(_,_,depth,_):=rf_reference_write_row stage in depth.
Definition rf_reference_write_data stage : VarOrder.T := let '(_,data,_,_):=rf_reference_write_row stage in N.of_nat data.
Definition rf_reference_write_selector index stage slot : VarOrder.T :=
 if stage==0%nat then N.of_nat(3223+index)%nat else
 let '(base,_,_,_):=rf_reference_write_row stage in N.of_nat(base+slot+80*(index-1))%nat.
Definition rf_reference_write_prior index stage : VarOrder.T :=
 if stage==0%nat then N.of_nat(2177-index)%nat else rf_reference_chain_node index(stage-1).
Definition rf_reference_write_input index stage slot : VarOrder.T :=
 if slot==0%nat then rf_reference_write_data stage else rf_reference_write_selector index stage(slot-1).
Definition rf_reference_write_condition index stage slot := if slot==0%nat then rf_reference_entry_condition index else
 let '(_,_,_,guard):=rf_reference_write_row stage in @Eref VarOrder.T(@Eid VarOrder.T(N.of_nat guard)).
Definition rf_reference_write_expr index stage slot := @Emux VarOrder.T(rf_reference_write_condition index stage slot)
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_input index stage slot)))
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_prior index stage))).
Definition rf_reference_write_nodes : seq(VarOrder.T*hfexpr VarOrder.T) :=
 List.map(fun index=>(rf_reference_write_selector index 0 0,rf_reference_write_expr index 0 0))(List.seq 1 31) ++
 List.flat_map(fun index=>List.flat_map(fun stage=>List.map(fun slot=>(rf_reference_write_selector index stage slot,rf_reference_write_expr index stage slot))(List.seq 0(rf_reference_write_depth stage)))(List.seq 1 35))(List.seq 1 31).
Definition rf_reference_write_offsets : seq nat := [::3303%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;284%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;5%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;0%nat;1%nat;1%nat;0%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat].
Lemma rf_reference_write_positions : select_node_offsets rf_reference_write_offsets flat_statements=Some rf_reference_write_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_write_safety : selected_node_safety flat_memories flat_statements rf_reference_write_offsets flat_statements=true.
Proof. vm_compute. reflexivity. Qed.
(* Reference effect semantic composition. *)
Lemma rf_reference_write_member index stage slot : (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->(slot<rf_reference_write_depth stage)%coq_nat ->
 List.In(rf_reference_write_selector index stage slot,rf_reference_write_expr index stage slot)rf_reference_write_nodes.
Proof.
 intros Lower Upper Stage Slot. unfold rf_reference_write_nodes. apply List.in_or_app.
 destruct stage as[|stage].
 - left. assert(slot=0%nat)by(change(slot<1)%coq_nat in Slot;lia). subst slot.
   apply List.in_map_iff. exists index. split;[reflexivity|apply List.in_seq;lia].
 - right. apply List.in_flat_map. exists index. split;[apply List.in_seq;lia|].
   apply List.in_flat_map. exists(S stage). split;[apply List.in_seq;lia|].
   apply List.in_map_iff. exists slot. split;[reflexivity|apply List.in_seq;lia].
Qed.
Lemma rf_reference_condition_exact index invalid site mm old rd : (1<=index)%coq_nat ->(index<32)%coq_nat ->
 VM.find 3221 old=Some(Gval(Fuint 5)rd) ->
 eval_hfexpr_validif_policy(isolated_validif_policy invalid)site mm(rf_reference_entry_condition index)old old=Some(Gval(Fuint 1)[::index==to_nat rd]).
Proof.
 intros Lower Upper Rd.
 assert(Expr:rf_reference_entry_condition index=@Eprim_binop VarOrder.T(Bcomp Beq)
 (@Econst VarOrder.T(Fuint(rf_preview_index_width index))(from_N(rf_preview_index_width index)(N.of_nat index)))
 (@Eref VarOrder.T(@Eid VarOrder.T 3221))).
 { destruct index as[|index];[lia|]. do 31(destruct index as[|index];[vm_compute;reflexivity|]);lia. }
 rewrite Expr. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Rd size_from_N ltnn.
 assert(Constant:zext_to(rf_preview_index_width index)(from_N(rf_preview_index_width index)(N.of_nat index))=from_N(rf_preview_index_width index)(N.of_nat index)).
 { unfold zext_to,zext. rewrite size_from_N subnn cats0. reflexivity. }
 rewrite Constant. unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint (rf_preview_index_exact index Upper) rf_preview_rd_match. reflexivity.
Qed.
Theorem rf_reference_write_step index stage slot invalid old result bit left right left_word right_word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->(slot<rf_reference_write_depth stage)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_reference_write_condition index stage slot)old old=Some(Gval(Fuint 1)[::bit])) ->
 VM.find(rf_reference_write_input index stage slot)old=Some left ->rf_reference_low_word left_word left ->
 VM.find(rf_reference_write_prior index stage)old=Some right ->rf_reference_low_word right_word right ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(rf_reference_write_selector index stage slot)result=Some value /\rf_reference_low_word(if bit then left_word else right_word)value.
Proof.
 intros Lower Upper Stage Slot Condition Left LLow Right RLow Step.
 destruct(selected_node_safe_position flat_memories flat_statements rf_reference_write_offsets flat_statements rf_reference_write_nodes _ _ rf_reference_write_positions rf_reference_write_safety(rf_reference_write_member index stage slot Lower Upper Stage Slot))as[count[tail[Position[Safe Nonreg]]]].
 destruct(rf_reference_low_mux flat_memories old _ _ _ invalid(validif_raw_address nil count 0 nil)bit left right left_word right_word Condition Left LLow Right RLow)as[value[Eval Low]].
 exists value. split;[|exact Low].
 destruct Low as[width[raw[Value[Size[Wide Prefix]]]]].
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg|exact Eval|rewrite Value;reflexivity|exact Step].
Qed.
Require Import RFReferenceNopHistory.
Local Opaque N.of_nat muln.
Definition rf_reference_write_final_base stage :=let '(base,_,depth,_):=rf_reference_write_row stage in(base+(depth-1))%nat.
Definition rf_reference_gate_yes_base stage :=let '(_,_,yes):=nth(0%nat,0%nat,0%nat)rf_reference_chain_specs stage in yes.
Lemma rf_reference_gate_base stage :(0<stage)%coq_nat ->(stage<36)%coq_nat ->rf_reference_write_final_base stage=rf_reference_gate_yes_base stage.
Proof. intros Lower Upper. destruct stage as[|stage];[lia|]. do 35(destruct stage as[|stage];[vm_compute;reflexivity|]);lia. Qed.
Lemma rf_reference_gate_expression index stage : (stage<36)%coq_nat ->
 rf_reference_chain_expr index stage=@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_chain_guard stage)))
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_selector index stage(rf_reference_write_depth stage-1))))
 (@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_write_prior index stage))).
Proof.
 intro Bound. destruct stage as[|stage];[reflexivity|].
 pose proof(rf_reference_gate_base(S stage)ltac:(lia)Bound)as Base.
 unfold rf_reference_write_final_base,rf_reference_gate_yes_base in Base.
 unfold rf_reference_chain_expr,rf_reference_chain_guard,rf_reference_write_selector,rf_reference_write_depth,rf_reference_write_prior.
 destruct(nth(0%nat,0%nat,0%nat)rf_reference_chain_specs(S stage))as[[node guard]yes]eqn:Spec.
 destruct(rf_reference_write_row(S stage))as[[[base data]depth]permission]eqn:Row.
 change((base+(depth-1))%nat=yes)in Base. cbn -[addn muln subn N.of_nat]. rewrite Base. reflexivity.
Qed.
Lemma rf_reference_gate_step index stage invalid old result bit chosen prior chosen_word prior_word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->
 VM.find(rf_reference_chain_guard stage)old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(rf_reference_write_selector index stage(rf_reference_write_depth stage-1))old=Some chosen ->rf_reference_low_word chosen_word chosen ->
 VM.find(rf_reference_write_prior index stage)old=Some prior ->rf_reference_low_word prior_word prior ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(rf_reference_chain_node index stage)result=Some value /\rf_reference_low_word(if bit then chosen_word else prior_word)value.
Proof.
 intros Lower Upper Stage Guard Chosen CLow Prior PLow Step.
 destruct(selected_node_safe_position flat_memories flat_statements rf_reference_chain_offsets flat_statements rf_reference_chain_nodes _ _ rf_reference_chain_positions rf_reference_chain_safety(rf_reference_chain_member index stage (conj Lower Upper)Stage))as[count[tail[Position[Safe Nonreg]]]].
 assert(Condition:forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(@Eref VarOrder.T(@Eid VarOrder.T(rf_reference_chain_guard stage)))old old=Some(Gval(Fuint 1)[::bit]))by(intro site;exact Guard).
 destruct(rf_reference_low_mux flat_memories old _ _ _ invalid(validif_raw_address nil count 0 nil)bit chosen prior chosen_word prior_word Condition Chosen CLow Prior PLow)as[value[Eval Low]].
 exists value. split;[|exact Low]. destruct Low as[width[raw[Value[Size[Wide Prefix]]]]].
 eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg| |rewrite Value;reflexivity|exact Step].
 rewrite(rf_reference_gate_expression index stage Stage). exact Eval.
Qed.
Definition rf_reference_permission_node stage : VarOrder.T :=let '(_,_,_,guard):=rf_reference_write_row stage in N.of_nat guard.
Definition rf_reference_permission_value stage (permitted:bool) := if rf_reference_write_depth stage==1%nat then true else permitted.
Lemma rf_reference_write_depth_cases stage : (stage<36)%coq_nat ->rf_reference_write_depth stage=1%nat \/rf_reference_write_depth stage=2%nat.
Proof. intro Bound. do 36(destruct stage as[|stage];[vm_compute;tauto|]);lia. Qed.
Theorem rf_reference_write_stage_three_steps index stage invalid s0 s1 s2 s3 rd opcode permitted data_word prior_word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->(stage<36)%coq_nat ->
 VM.find 3221 s0=Some(Gval(Fuint 5)rd) ->VM.find 3221 s1=Some(Gval(Fuint 5)rd) ->
 (exists value,VM.find(rf_reference_write_data stage)s0=Some value /\rf_reference_low_word data_word value) ->
 (exists value,VM.find(rf_reference_write_data stage)s1=Some value /\rf_reference_low_word data_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s0=Some value /\rf_reference_low_word prior_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s1=Some value /\rf_reference_low_word prior_word value) ->
 (exists value,VM.find(rf_reference_write_prior index stage)s2=Some value /\rf_reference_low_word prior_word value) ->
 (rf_reference_write_depth stage=2%nat ->VM.find(rf_reference_permission_node stage)s1=Some(Gval(Fuint 1)[::permitted])) ->
 VM.find(rf_reference_chain_guard stage)s2=Some(Gval(Fuint 1)[::opcode]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 exists value,VM.find(rf_reference_chain_node index stage)s3=Some value /\
 rf_reference_low_word(if opcode && rf_reference_permission_value stage permitted && (index==to_nat rd) then data_word else prior_word)value.
Proof.
 intros Lower Upper Stage Rd0 Rd1[D0[Data0 DL0]][D1[Data1 DL1]][P0[Prior0 PL0]][P1[Prior1 PL1]][P2[Prior2 PL2]]Permission Opcode S1 S2 S3.
 assert(Selected:exists value,VM.find(rf_reference_write_selector index stage(rf_reference_write_depth stage-1))s2=Some value /\
 rf_reference_low_word(if rf_reference_permission_value stage permitted && (index==to_nat rd) then data_word else prior_word)value).
 { destruct(rf_reference_write_depth_cases stage Stage)as[Depth|Depth].
   - unfold rf_reference_permission_value. rewrite Depth. cbn.
     eapply(rf_reference_write_step index stage 0 invalid s1 s2 (index==to_nat rd) D1 P1 data_word prior_word Lower Upper Stage).
     + rewrite Depth. lia.
     + intros site. exact(rf_reference_condition_exact index invalid site flat_memories s1 rd Lower Upper Rd1).
     + exact Data1.
     + exact DL1.
     + exact Prior1.
     + exact PL1.
     + exact S2.
   - destruct(rf_reference_write_step index stage 0 invalid s0 s1 (index==to_nat rd) D0 P0 data_word prior_word Lower Upper Stage ltac:(rewrite Depth;lia) (fun site=>rf_reference_condition_exact index invalid site flat_memories s0 rd Lower Upper Rd0) Data0 DL0 Prior0 PL0 S1)as[inner[Inner ILow]].
     assert(Cond:forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_reference_write_condition index stage 1)s1 s1=Some(Gval(Fuint 1)[::permitted])).
     { intros site. unfold rf_reference_write_condition. unfold rf_reference_permission_node in Permission. destruct(rf_reference_write_row stage)as[[[base data]depth]guard]. exact(Permission Depth). }
     destruct(rf_reference_write_step index stage 1 invalid s1 s2 permitted inner P1 (if index==to_nat rd then data_word else prior_word) prior_word Lower Upper Stage ltac:(rewrite Depth;lia) Cond Inner ILow Prior1 PL1 S2)as[value[Value Low]].
     exists value. split;[rewrite Depth;exact Value|].
     unfold rf_reference_permission_value. rewrite Depth.
     change(rf_reference_low_word(if permitted && (index==to_nat rd)then data_word else prior_word)value).
     destruct permitted,(index==to_nat rd);exact Low. }
 destruct Selected as[value[Value Low]].
 destruct(rf_reference_gate_step index stage invalid s2 s3 opcode value P2 _ prior_word Lower Upper Stage Opcode Value Low Prior2 PL2 S3)as[result[Result Word]].
 exists result. split;[exact Result|].
 destruct opcode,(rf_reference_permission_value stage permitted),(index==to_nat rd);exact Word.
Qed.
Lemma rf_reference_low_adapt32 word value :rf_reference_low_word word value ->
 adapt_hvalue_as_type value(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word).
Proof.
 intros[width[raw[Value[Size[Wide Low]]]]]. subst value. cbn [adapt_hvalue_as_type]. rewrite -Low.
 assert(Prefix:size(take 32 raw)=32%nat)by(rewrite size_take Size;exact(minn_idPl Wide)).
 unfold zext_to,zext. rewrite Prefix subnn cats0. reflexivity.
Qed.
Fixpoint rf_reference_effect (guards permissions:nat->bool)(words:nat->bits)(destination:nat)(count:nat) :rf_write_effect :=
 match count with O=>RFNoWrite|S stage=>
 if guards stage && rf_reference_permission_value stage(permissions stage)
 then RFWrite destination(words stage) else rf_reference_effect guards permissions words destination stage end.
Fixpoint rf_reference_fold_word (guards permissions:nat->bool)(words:nat->bits)(destination index:nat)(initial:bits)(count:nat) :bits :=
 match count with O=>initial|S stage=>
 if guards stage && rf_reference_permission_value stage(permissions stage) &&(index==destination)
 then words stage else rf_reference_fold_word guards permissions words destination index initial stage end.
Lemma rf_reference_fold_miss guards permissions words destination index initial count : (index==destination)=false ->
 rf_reference_fold_word guards permissions words destination index initial count=initial.
Proof. intro Miss. induction count as[|count IH];[reflexivity|]. cbn [rf_reference_fold_word]. rewrite Miss andbF. exact IH. Qed.
Lemma rf_reference_fold_effect guards permissions words destination index bank count :(1<=index)%coq_nat ->
 rf_reference_fold_word guards permissions words destination index(bank index)count=rf_apply_effect bank(rf_reference_effect guards permissions words destination count)index.
Proof.
 intros Nonzero. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia).
 induction count as[|count IH];[unfold rf_apply_effect;rewrite Zero;reflexivity|].
 cbn [rf_reference_fold_word rf_reference_effect]. destruct(guards count && rf_reference_permission_value count(permissions count))eqn:Enable.
 - unfold rf_apply_effect. rewrite Zero.
   change((if index==destination then words count else rf_reference_fold_word guards permissions words destination index(bank index)count)=(if index==destination then words count else bank index)).
   destruct(index==destination)eqn:Hit;[reflexivity|]. exact(rf_reference_fold_miss guards permissions words destination index(bank index)count Hit).
 - cbn. exact IH.
Qed.
Definition rf_reference_fold_node index count :VarOrder.T :=if count is S stage then rf_reference_chain_node index stage else N.of_nat(2177-index)%nat.
Lemma rf_reference_prior_fold index stage :rf_reference_write_prior index stage=rf_reference_fold_node index stage.
Proof. destruct stage as[|stage];[reflexivity|]. unfold rf_reference_write_prior,rf_reference_fold_node. rewrite subn1. reflexivity. Qed.
Theorem rf_reference_effect_history invalid history (limit start:nat) index rd initial guards permissions words :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word initial value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall count time,(count<=36)%coq_nat ->(Nat.add start(Nat.mul 3 count)<=time)%coq_nat ->(time<=limit)%coq_nat ->
 exists value,VM.find(rf_reference_fold_node index count)(history time)=Some value /\
 rf_reference_low_word(rf_reference_fold_word guards permissions words(to_nat rd)index initial count)value.
Proof.
 intros Lower Upper Rd Initial Data Guards Permissions Steps count. induction count as[|count IH];intros time Bound Ready Within.
 - apply Initial;lia.
 - destruct time as[|[|[|time]]];try lia.
   cbn [rf_reference_fold_node rf_reference_fold_word].
   eapply(rf_reference_write_stage_three_steps index count invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))rd(guards count)(permissions count)(words count)(rf_reference_fold_word guards permissions words(to_nat rd)index initial count)Lower Upper ltac:(lia)).
   + apply Rd;lia.
   + apply Rd;lia.
   + apply Data;lia.
   + apply Data;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + rewrite rf_reference_prior_fold. apply IH;lia.
   + intro Depth. apply Permissions;try assumption;lia.
   + apply Guards;lia.
   + apply Steps;lia.
   + apply Steps;lia.
   + apply Steps;lia.
Qed.
Require Import RFReferenceNopExit FormalDeclaredWireCheck.
Local Transparent muln.
Lemma rf_reference_final_node index :rf_reference_chain_node index 35=rf_exit_node 3614 index.
Proof. change(N.of_nat(3614+80*(index-1))%nat=rf_exit_node 3614 index). unfold rf_exit_node. rewrite subn1. reflexivity. Qed.
Theorem rf_reference_effect_exit index invalid s0 s1 s2 s3 active chosen prior chosen_word prior_word :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 VM.find 1707 s0=Some(Gval(Fuint 1)[::active]) ->
 VM.find(rf_reference_chain_node index 35)s0=Some chosen ->rf_reference_low_word chosen_word chosen ->
 VM.find(N.of_nat(2177-index)%nat)s0=Some prior ->rf_reference_low_word prior_word prior ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_exit_port index)s3=Some(Gval(Fuint 32)(if active then chosen_word else prior_word)).
Proof.
 intros Lower Upper Active Chosen CLow Prior PLow S1 S2 S3.
 destruct(rf_exit_members index Lower Upper)as[Member _].
 destruct(selected_node_safe_position flat_memories flat_statements rf_exit_offsets flat_statements rf_exit_nodes _ _ rf_exit_positions rf_exit_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 rewrite rf_reference_final_node in Chosen.
 assert(Condition:forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(@Eref VarOrder.T(@Eid VarOrder.T 1707))s0 s0=Some(Gval(Fuint 1)[::active]))by(intro site;exact Active).
 destruct(rf_reference_low_mux flat_memories s0 _ _ _ invalid(validif_raw_address nil count 0 nil)active chosen prior chosen_word prior_word Condition Chosen CLow Prior PLow)as[value[Eval Low]].
 assert(Out:VM.find(rf_exit_node 3615 index)s1=Some value).
 { destruct Low as[width[raw[Value[Size[Wide Prefix]]]]].
   eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg|exact Eval|rewrite Value;reflexivity|exact S1]. }
 assert(Alias:VM.find(rf_exit_node 3616 index)s2=Some value).
 { eapply rf_exit_alias_step;[exact Lower|exact Upper|exact Out| |exact S2].
   destruct Low as[width[raw[Value Rest]]]. exists width,raw. exact Value. }
 eapply(declared_wire_checked_value flat_memories flat_statements(rf_exit_decl_position index)
 (Nat.sub(rf_exit_connect_position index)(S(rf_exit_decl_position index)))(rf_exit_port index)(rf_exit_node 3616 index)32);
 [exact(rf_exit_wire_certificates index Lower Upper)|exact Alias|exact(rf_reference_low_adapt32 _ _ Low)|exact S3].
Qed.
Require Import RFReferenceNopObservedOutputs RFReferenceNopIngress.
Theorem rf_reference_effect_preview_history invalid history (limit start:nat) index rd bank guards permissions words active :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 112<=time)%coq_nat ->(time<=limit)%coq_nat ->
 let word:=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index in
 size word=32%nat /\VM.find(N.of_nat(Nat.add 1597 index))(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lower Upper Rd Start Bank Data Guards Permissions Active Steps time Ready Within.
 assert(Initial:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word(bank index)value).
 { intros t L U. destruct t as[|[|t]];try lia.
   destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps t ltac:(lia) index Upper)as[Size Value].
   exists(Gval(Fuint 32)(bank index)). split.
   - exact(rf_reference_old_word_ingress index invalid(history t)(history(S t))(history(S(S t)))(bank index)Upper Size Value(Steps t ltac:(lia))(Steps(S t)ltac:(lia))).
   - exists 32%nat,(bank index). repeat split;try assumption;try reflexivity. rewrite -Size take_size. reflexivity. }
 destruct time as[|[|[|[|time]]]];try lia.
 destruct(rf_reference_effect_history invalid history limit start index rd(bank index)guards permissions words Lower Upper Rd Initial Data Guards Permissions Steps 36 time ltac:(lia) ltac:(change(Nat.add start 108<=time)%coq_nat;lia) ltac:(lia))as[value[Value Low]].
 destruct(Initial time ltac:(lia) ltac:(lia))as[prior[Prior PLow]].
 assert(Choice:(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index).
 { destruct active;[exact(rf_reference_fold_effect guards permissions words(to_nat rd)index bank 36 Lower)|].
   unfold rf_apply_effect. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia). rewrite Zero. reflexivity. }
 assert(Size:size(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=32%nat).
 { destruct active;[exact(rf_reference_low_word_size _ _ Low)|exact(rf_reference_low_word_size _ _ PLow)]. }
 pose proof(rf_reference_effect_exit index invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))active value prior _ _ Lower Upper (Active time ltac:(lia) ltac:(lia)) Value Low Prior PLow (Steps time ltac:(lia))(Steps(S time)ltac:(lia))(Steps(S(S time))ltac:(lia)))as Port.
 rewrite Choice in Size,Port. split;[exact Size|].
 exact(rf_reference_output_step index invalid(history(S(S(S time))))(history(S(S(S time))))(history(S(S(S(S time)))))_ Upper Size Port(Steps(S(S(S time)))ltac:(lia))).
Qed.
