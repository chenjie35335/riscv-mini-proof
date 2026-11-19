Require Import ReferenceRedirectSpine ReferenceControlStabilityHistory ReferenceControlExpressions ReferenceControlNodeCongruence3.
From Coq Require Import ZArith Lia btauto.Btauto.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Require Import CoreSocModel ComparisonNodes.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Six-input branch/jump specification.  Immediate decoding is a separate interface.
   Inputs are unsigned numerical representations of 32-bit words. *)
Definition reference_redirect_aligned compressed target :=
 N.eqb (N.land target (if compressed then 1 else 3)) 0.
Definition reference_redirect_signed word :=
 if N.testbit word 31 then (Z.of_N word - 4294967296)%Z else Z.of_N word.
Definition reference_redirect_function instruction rs1 rs2 immediate pc csr : bool :=
 let code := N.land instruction 28799 in
 let compressed := N.testbit csr 2 in
 let aligned := reference_redirect_aligned compressed (pc + immediate) in
 let taken :=
 (N.eqb code 28771 && N.leb rs2 rs1) ||
 (N.eqb code 20579 && Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1)) ||
 (N.eqb code 24675 && N.ltb rs1 rs2) ||
 (N.eqb code 16483 && Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2)) ||
 (N.eqb code 4195 && negb (N.eqb rs1 rs2)) ||
 (N.eqb code 99 && N.eqb rs1 rs2) || N.eqb (N.land instruction 127) 111 in
 (taken && aligned) ||
 (N.eqb code 103 && reference_redirect_aligned compressed (N.clearbit (rs1 + immediate) 0)).

Definition reference_redirect_guards (b1974 : bool) (b1980 : bool) (b1986 : bool) (b1992 : bool) (b1998 : bool) (b2004 : bool) (b2010 : bool) (b2357 : bool) (b2806 : bool) (b2825 : bool) (b2830 : bool) (b2847 : bool) (b2850 : bool) (b2867 : bool) (b2872 : bool) (b2889 : bool) (b2892 : bool) (b2909 : bool) (b2912 : bool) (b2929 : bool) (b2949 : bool) (b2966 : bool) := (b1974 && b2806 && b2825) || (b1980 && b2830 && b2847) || (b1986 && b2850 && b2867) || (b1992 && b2872 && b2889) || (b1998 && b2892 && b2909) || (b2004 && b2912 && b2929) || (b2010 && b2949) || (b2357 && b2966).
Theorem reference_redirect_spine_history inputs path history limit reset time b1974 b1980 b1986 b1992 b1998 b2004 b2010 b2357 b2806 b2825 b2830 b2847 b2850 b2867 b2872 b2889 b2892 b2909 b2912 b2929 b2949 b2966 :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1974 (history time) = Some (Gval (Fuint 1) [::b1974]) ->
 VM.find 1980 (history time) = Some (Gval (Fuint 1) [::b1980]) ->
 VM.find 1986 (history time) = Some (Gval (Fuint 1) [::b1986]) ->
 VM.find 1992 (history time) = Some (Gval (Fuint 1) [::b1992]) ->
 VM.find 1998 (history time) = Some (Gval (Fuint 1) [::b1998]) ->
 VM.find 2004 (history time) = Some (Gval (Fuint 1) [::b2004]) ->
 VM.find 2010 (history time) = Some (Gval (Fuint 1) [::b2010]) ->
 VM.find 2357 (history time) = Some (Gval (Fuint 1) [::b2357]) ->
 VM.find 2806 (history time) = Some (Gval (Fuint 1) [::b2806]) ->
 VM.find 2825 (history time) = Some (Gval (Fuint 1) [::b2825]) ->
 VM.find 2830 (history time) = Some (Gval (Fuint 1) [::b2830]) ->
 VM.find 2847 (history time) = Some (Gval (Fuint 1) [::b2847]) ->
 VM.find 2850 (history time) = Some (Gval (Fuint 1) [::b2850]) ->
 VM.find 2867 (history time) = Some (Gval (Fuint 1) [::b2867]) ->
 VM.find 2872 (history time) = Some (Gval (Fuint 1) [::b2872]) ->
 VM.find 2889 (history time) = Some (Gval (Fuint 1) [::b2889]) ->
 VM.find 2892 (history time) = Some (Gval (Fuint 1) [::b2892]) ->
 VM.find 2909 (history time) = Some (Gval (Fuint 1) [::b2909]) ->
 VM.find 2912 (history time) = Some (Gval (Fuint 1) [::b2912]) ->
 VM.find 2929 (history time) = Some (Gval (Fuint 1) [::b2929]) ->
 VM.find 2949 (history time) = Some (Gval (Fuint 1) [::b2949]) ->
 VM.find 2966 (history time) = Some (Gval (Fuint 1) [::b2966]) ->
 VM.find 6507 (history time) = Some (Gval (Fuint 1) [::reference_redirect_guards b1974 b1980 b1986 b1992 b1998 b2004 b2010 b2357 b2806 b2825 b2830 b2847 b2850 b2867 b2872 b2889 b2892 b2909 b2912 b2929 b2949 b2966]).
Proof.
 intros Resets Steps Lower Upper H1974 H1980 H1986 H1992 H1998 H2004 H2010 H2357 H2806 H2825 H2830 H2847 H2850 H2867 H2872 H2889 H2892 H2909 H2912 H2929 H2949 H2966.
 pose proof (Steps time Upper) as Step.
 set b6314 := (if b2966 then true else false).
 assert (H6314 : VM.find 6314 (history (S time)) = Some (Gval (Fuint 1) [::b6314])).
 { eapply (reference_redirect_mux_step 6314 reference_control_expr_6314 (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Econst VarOrder.T (Fuint 1) [::false]) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2966 true false);
 [exact reference_control_member_6314|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6314_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6314.
 set b6325 := (if b2357 then b6314 else false).
 assert (H6325 : VM.find 6325 (history (S time)) = Some (Gval (Fuint 1) [::b6325])).
 { eapply (reference_redirect_mux_step 6325 reference_control_expr_6325 (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6314)) (@Econst VarOrder.T (Fuint 1) [::false]) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2357 b6314 false);
 [exact reference_control_member_6325|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6325_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6325.
 set b6346 := (if b2949 then true else b6325).
 assert (H6346 : VM.find 6346 (history (S time)) = Some (Gval (Fuint 1) [::b6346])).
 { eapply (reference_redirect_mux_step 6346 reference_control_expr_6346 (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6325)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2949 true b6325);
 [exact reference_control_member_6346|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6346_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6346.
 set b6359 := (if b2010 then b6346 else b6325).
 assert (H6359 : VM.find 6359 (history (S time)) = Some (Gval (Fuint 1) [::b6359])).
 { eapply (reference_redirect_mux_step 6359 reference_control_expr_6359 (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6346)) (@Eref VarOrder.T (@Eid VarOrder.T 6325)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2010 b6346 b6325);
 [exact reference_control_member_6359|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6359_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6359.
 set b6373 := (if b2929 then true else b6359).
 assert (H6373 : VM.find 6373 (history (S time)) = Some (Gval (Fuint 1) [::b6373])).
 { eapply (reference_redirect_mux_step 6373 reference_control_expr_6373 (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6359)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2929 true b6359);
 [exact reference_control_member_6373|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6373_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6373.
 set b6377 := (if b2912 then b6373 else b6359).
 assert (H6377 : VM.find 6377 (history (S time)) = Some (Gval (Fuint 1) [::b6377])).
 { eapply (reference_redirect_mux_step 6377 reference_control_expr_6377 (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6373)) (@Eref VarOrder.T (@Eid VarOrder.T 6359)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2912 b6373 b6359);
 [exact reference_control_member_6377|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6377_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6377.
 set b6387 := (if b2004 then b6377 else b6359).
 assert (H6387 : VM.find 6387 (history (S time)) = Some (Gval (Fuint 1) [::b6387])).
 { eapply (reference_redirect_mux_step 6387 reference_control_expr_6387 (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6377)) (@Eref VarOrder.T (@Eid VarOrder.T 6359)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2004 b6377 b6359);
 [exact reference_control_member_6387|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6387_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6387.
 set b6397 := (if b2909 then true else b6387).
 assert (H6397 : VM.find 6397 (history (S time)) = Some (Gval (Fuint 1) [::b6397])).
 { eapply (reference_redirect_mux_step 6397 reference_control_expr_6397 (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6387)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2909 true b6387);
 [exact reference_control_member_6397|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6397_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6397.
 set b6401 := (if b2892 then b6397 else b6387).
 assert (H6401 : VM.find 6401 (history (S time)) = Some (Gval (Fuint 1) [::b6401])).
 { eapply (reference_redirect_mux_step 6401 reference_control_expr_6401 (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6397)) (@Eref VarOrder.T (@Eid VarOrder.T 6387)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2892 b6397 b6387);
 [exact reference_control_member_6401|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6401_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6401.
 set b6411 := (if b1998 then b6401 else b6387).
 assert (H6411 : VM.find 6411 (history (S time)) = Some (Gval (Fuint 1) [::b6411])).
 { eapply (reference_redirect_mux_step 6411 reference_control_expr_6411 (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6401)) (@Eref VarOrder.T (@Eid VarOrder.T 6387)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b1998 b6401 b6387);
 [exact reference_control_member_6411|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6411_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6411.
 set b6421 := (if b2889 then true else b6411).
 assert (H6421 : VM.find 6421 (history (S time)) = Some (Gval (Fuint 1) [::b6421])).
 { eapply (reference_redirect_mux_step 6421 reference_control_expr_6421 (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6411)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2889 true b6411);
 [exact reference_control_member_6421|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6421_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6421.
 set b6425 := (if b2872 then b6421 else b6411).
 assert (H6425 : VM.find 6425 (history (S time)) = Some (Gval (Fuint 1) [::b6425])).
 { eapply (reference_redirect_mux_step 6425 reference_control_expr_6425 (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6421)) (@Eref VarOrder.T (@Eid VarOrder.T 6411)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2872 b6421 b6411);
 [exact reference_control_member_6425|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6425_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6425.
 set b6435 := (if b1992 then b6425 else b6411).
 assert (H6435 : VM.find 6435 (history (S time)) = Some (Gval (Fuint 1) [::b6435])).
 { eapply (reference_redirect_mux_step 6435 reference_control_expr_6435 (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6425)) (@Eref VarOrder.T (@Eid VarOrder.T 6411)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b1992 b6425 b6411);
 [exact reference_control_member_6435|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6435_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6435.
 set b6445 := (if b2867 then true else b6435).
 assert (H6445 : VM.find 6445 (history (S time)) = Some (Gval (Fuint 1) [::b6445])).
 { eapply (reference_redirect_mux_step 6445 reference_control_expr_6445 (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6435)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2867 true b6435);
 [exact reference_control_member_6445|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6445_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6445.
 set b6449 := (if b2850 then b6445 else b6435).
 assert (H6449 : VM.find 6449 (history (S time)) = Some (Gval (Fuint 1) [::b6449])).
 { eapply (reference_redirect_mux_step 6449 reference_control_expr_6449 (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6445)) (@Eref VarOrder.T (@Eid VarOrder.T 6435)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2850 b6445 b6435);
 [exact reference_control_member_6449|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6449_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6449.
 set b6459 := (if b1986 then b6449 else b6435).
 assert (H6459 : VM.find 6459 (history (S time)) = Some (Gval (Fuint 1) [::b6459])).
 { eapply (reference_redirect_mux_step 6459 reference_control_expr_6459 (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6449)) (@Eref VarOrder.T (@Eid VarOrder.T 6435)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b1986 b6449 b6435);
 [exact reference_control_member_6459|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6459_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6459.
 set b6469 := (if b2847 then true else b6459).
 assert (H6469 : VM.find 6469 (history (S time)) = Some (Gval (Fuint 1) [::b6469])).
 { eapply (reference_redirect_mux_step 6469 reference_control_expr_6469 (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6459)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2847 true b6459);
 [exact reference_control_member_6469|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6469_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6469.
 set b6473 := (if b2830 then b6469 else b6459).
 assert (H6473 : VM.find 6473 (history (S time)) = Some (Gval (Fuint 1) [::b6473])).
 { eapply (reference_redirect_mux_step 6473 reference_control_expr_6473 (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6469)) (@Eref VarOrder.T (@Eid VarOrder.T 6459)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2830 b6469 b6459);
 [exact reference_control_member_6473|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6473_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6473.
 set b6483 := (if b1980 then b6473 else b6459).
 assert (H6483 : VM.find 6483 (history (S time)) = Some (Gval (Fuint 1) [::b6483])).
 { eapply (reference_redirect_mux_step 6483 reference_control_expr_6483 (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6473)) (@Eref VarOrder.T (@Eid VarOrder.T 6459)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b1980 b6473 b6459);
 [exact reference_control_member_6483|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6483_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6483.
 set b6493 := (if b2825 then true else b6483).
 assert (H6493 : VM.find 6493 (history (S time)) = Some (Gval (Fuint 1) [::b6493])).
 { eapply (reference_redirect_mux_step 6493 reference_control_expr_6493 (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6483)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2825 true b6483);
 [exact reference_control_member_6493|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6493_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6493.
 set b6497 := (if b2806 then b6493 else b6483).
 assert (H6497 : VM.find 6497 (history (S time)) = Some (Gval (Fuint 1) [::b6497])).
 { eapply (reference_redirect_mux_step 6497 reference_control_expr_6497 (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6493)) (@Eref VarOrder.T (@Eid VarOrder.T 6483)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b2806 b6493 b6483);
 [exact reference_control_member_6497|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6497_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6497.
 set b6507 := (if b1974 then b6497 else b6483).
 assert (H6507 : VM.find 6507 (history (S time)) = Some (Gval (Fuint 1) [::b6507])).
 { eapply (reference_redirect_mux_step 6507 reference_control_expr_6507 (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6497)) (@Eref VarOrder.T (@Eid VarOrder.T 6483)) (formal_invalid_policy inputs path) (history time) (history time) (history (S time)) b1974 b6497 b6483);
 [exact reference_control_member_6507|reflexivity| | | | | |exact Step];
 try intros site; cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; repeat match goal with H : VM.find _ _ = _ |- _ => rewrite H end; reflexivity. }
 rewrite <- (reference_control_stable_6507_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H6507.
 rewrite H6507. f_equal. f_equal. f_equal. unfold reference_redirect_guards in *. subst b6507 b6497 b6493 b6483 b6473 b6469 b6459 b6449 b6445 b6435 b6425 b6421 b6411 b6401 b6397 b6387 b6377 b6373 b6359 b6346 b6325 b6314. btauto.
Qed.

Lemma reference_redirect_guards_normalize instruction rs1 rs2 immediate pc csr :
 reference_redirect_guards
  (N.eqb (N.land instruction 28799) 28771)
  (N.eqb (N.land instruction 28799) 20579)
  (N.eqb (N.land instruction 28799) 24675)
  (N.eqb (N.land instruction 28799) 16483)
  (N.eqb (N.land instruction 28799) 4195)
  (N.eqb (N.land instruction 28799) 99)
  (N.eqb (N.land instruction 28799) 103)
  (N.eqb (N.land instruction 127) 111)
  (N.leb rs2 rs1)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.leb (reference_redirect_signed rs2) (reference_redirect_signed rs1))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.ltb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (Z.ltb (reference_redirect_signed rs1) (reference_redirect_signed rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (negb (N.eqb rs1 rs2))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (N.eqb rs1 rs2)
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate))
  (reference_redirect_aligned (N.testbit csr 2) (N.clearbit (rs1 + immediate) 0))
  (reference_redirect_aligned (N.testbit csr 2) (pc + immediate)) =
 reference_redirect_function instruction rs1 rs2 immediate pc csr.
Proof. unfold reference_redirect_guards, reference_redirect_function. btauto. Qed.

Require Import ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1.
From nbits Require Import NBitsDef NBitsOp.
From firrtl Require Import Firrtl_with_implicit_widths.
Theorem reference_redirect_decoders_history inputs path history limit reset time instruction :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
VM.find 1974 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 28771]) /\
 VM.find 1980 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 20579]) /\
 VM.find 1986 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 24675]) /\
 VM.find 1992 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 16483]) /\
 VM.find 1998 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 4195]) /\
 VM.find 2004 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 99]) /\
 VM.find 2010 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 103]) /\
 VM.find 2357 (history time) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 127) 111]).
Proof.
 intros Resets Steps Lower Upper Instruction.
 pose proof (Steps time Upper) as Step.
 assert (H1973 : VM.find 1973 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1973 reference_control_expr_1973);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1973| |exact Step].
 intros site. unfold reference_control_expr_1973. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_1973_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1973.
 assert (H1974 : VM.find 1974 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 28771])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1974 reference_control_expr_1974);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1974| |exact Step].
 intros site. unfold reference_control_expr_1974. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1973. change (eval_binop (Bcomp Beq) (Gval (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; true; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 28771])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true; false; false; false; false; false; true; true; true] 32 15 15). }
 rewrite <- (reference_control_stable_1974_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1974.
 assert (H1979 : VM.find 1979 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1979 reference_control_expr_1979);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1979| |exact Step].
 intros site. unfold reference_control_expr_1979. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_1979_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1979.
 assert (H1980 : VM.find 1980 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 20579])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1980 reference_control_expr_1980);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1980| |exact Step].
 intros site. unfold reference_control_expr_1980. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1979. change (eval_binop (Bcomp Beq) (Gval (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; false; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 20579])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true; false; false; false; false; false; true; false; true] 32 15 15). }
 rewrite <- (reference_control_stable_1980_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1980.
 assert (H1985 : VM.find 1985 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1985 reference_control_expr_1985);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1985| |exact Step].
 intros site. unfold reference_control_expr_1985. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_1985_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1985.
 assert (H1986 : VM.find 1986 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 24675])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1986 reference_control_expr_1986);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1986| |exact Step].
 intros site. unfold reference_control_expr_1986. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1985. change (eval_binop (Bcomp Beq) (Gval (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; true; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 24675])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true; false; false; false; false; false; false; true; true] 32 15 15). }
 rewrite <- (reference_control_stable_1986_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1986.
 assert (H1991 : VM.find 1991 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1991 reference_control_expr_1991);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1991| |exact Step].
 intros site. unfold reference_control_expr_1991. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_1991_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1991.
 assert (H1992 : VM.find 1992 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 16483])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1992 reference_control_expr_1992);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1992| |exact Step].
 intros site. unfold reference_control_expr_1992. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1991. change (eval_binop (Bcomp Beq) (Gval (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; false; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 16483])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true; false; false; false; false; false; false; false; true] 32 15 15). }
 rewrite <- (reference_control_stable_1992_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1992.
 assert (H1997 : VM.find 1997 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1997 reference_control_expr_1997);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1997| |exact Step].
 intros site. unfold reference_control_expr_1997. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_1997_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1997.
 assert (H1998 : VM.find 1998 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 4195])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 1998 reference_control_expr_1998);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_1998| |exact Step].
 intros site. unfold reference_control_expr_1998. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H1997. change (eval_binop (Bcomp Beq) (Gval (Fuint 13) [::true; true; false; false; false; true; true; false; false; false; false; false; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 4195])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true; false; false; false; false; false; true] 32 15 13). }
 rewrite <- (reference_control_stable_1998_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H1998.
 assert (H2003 : VM.find 2003 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2003 reference_control_expr_2003);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2003| |exact Step].
 intros site. unfold reference_control_expr_2003. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_2003_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2003.
 assert (H2004 : VM.find 2004 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 99])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2004 reference_control_expr_2004);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2004| |exact Step].
 intros site. unfold reference_control_expr_2004. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2003. change (eval_binop (Bcomp Beq) (Gval (Fuint 7) [::true; true; false; false; false; true; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 99])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; false; false; false; true; true] 32 15 7). }
 rewrite <- (reference_control_stable_2004_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2004.
 assert (H2009 : VM.find 2009 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2009 reference_control_expr_2009);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2009| |exact Step].
 intros site. unfold reference_control_expr_2009. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_2009_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2009.
 assert (H2010 : VM.find 2010 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 103])).
 { eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2010 reference_control_expr_2010);
 [exact reference_control_0_positions|exact reference_control_0_safety|exact reference_control_member_2010| |exact Step].
 intros site. unfold reference_control_expr_2010. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2009. change (eval_binop (Bcomp Beq) (Gval (Fuint 7) [::true; true; true; false; false; true; true]) (Gval (Fuint (maxn 32 15)) (andB instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 28799) 103])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true; false; false; false; false; false; true; true; true] [::true; true; true; false; false; true; true] 32 15 7). }
 rewrite <- (reference_control_stable_2010_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2010.
 assert (H2356 : VM.find 2356 (history (S time)) = Some (Gval (Fuint 32) (andB instruction [::true; true; true; true; true; true; true]))).
 { eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2356 reference_control_expr_2356);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2356| |exact Step].
 intros site. unfold reference_control_expr_2356. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Instruction. reflexivity. }
 rewrite <- (reference_control_stable_2356_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2356.
 assert (H2357 : VM.find 2357 (history (S time)) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 127) 111])).
 { eapply (reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes 2357 reference_control_expr_2357);
 [exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_2357| |exact Step].
 intros site. unfold reference_control_expr_2357. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2356. change (eval_binop (Bcomp Beq) (Gval (Fuint 7) [::true; true; true; true; false; true; true]) (Gval (Fuint (maxn 32 7)) (andB instruction [::true; true; true; true; true; true; true])) = Some (Gval (Fuint 1) [::N.eqb (N.land (to_N instruction) 127) 111])).
 exact (redirect_mask_decode instruction [::true; true; true; true; true; true; true] [::true; true; true; true; false; true; true] 32 7 7). }
 rewrite <- (reference_control_stable_2357_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2357.
 repeat split; assumption.
Qed.

Require Import ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence2.
Theorem reference_redirect_comparisons_history inputs path history limit reset time rs1 rs2 :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (history time) = Some (Gval (Fuint 32) rs2) ->
VM.find 2806 (history time) = Some (Gval (Fuint 1) [::N.leb (to_N rs2) (to_N rs1)]) /\
 VM.find 2830 (history time) = Some (Gval (Fuint 1) [::Z.geb (to_Z rs1) (to_Z rs2)]) /\
 VM.find 2850 (history time) = Some (Gval (Fuint 1) [::N.ltb (to_N rs1) (to_N rs2)]) /\
 VM.find 2872 (history time) = Some (Gval (Fuint 1) [::Z.ltb (to_Z rs1) (to_Z rs2)]) /\
 VM.find 2892 (history time) = Some (Gval (Fuint 1) [::(to_N rs1 != to_N rs2)]) /\
 VM.find 2912 (history time) = Some (Gval (Fuint 1) [::(to_N rs1 == to_N rs2)]).
Proof.
 intros Resets Steps Lower Upper H2209 H2804.
 pose proof (Steps time Upper) as Step.
 assert (H2772 : VM.find 2772 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2772 reference_control_expr_2772);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2772| |exact Step].
 intros site. unfold reference_control_expr_2772. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2772_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2772.
 assert (H2805 : VM.find 2805 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2805 reference_control_expr_2805);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2805| |exact Step].
 intros site. unfold reference_control_expr_2805. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2805_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2805.
 assert (H2806 : VM.find 2806 (history (S time)) = Some (Gval (Fuint 1) [::N.leb (to_N rs2) (to_N rs1)])).
 { eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2806 reference_control_expr_2806);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2806| |exact Step].
 intros site. unfold reference_control_expr_2806. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2772 H2805. reflexivity. }
 rewrite <- (reference_control_stable_2806_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2806.
 assert (H2826 : VM.find 2826 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2826 reference_control_expr_2826);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2826| |exact Step].
 intros site. unfold reference_control_expr_2826. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2826_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2826.
 assert (H2827 : VM.find 2827 (history (S time)) = Some (Gval (Fsint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2827 reference_control_expr_2827);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2827| |exact Step].
 intros site. unfold reference_control_expr_2827. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2826. reflexivity. }
 rewrite <- (reference_control_stable_2827_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2827.
 assert (H2828 : VM.find 2828 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2828 reference_control_expr_2828);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2828| |exact Step].
 intros site. unfold reference_control_expr_2828. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2828_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2828.
 assert (H2829 : VM.find 2829 (history (S time)) = Some (Gval (Fsint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2829 reference_control_expr_2829);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2829| |exact Step].
 intros site. unfold reference_control_expr_2829. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2828. reflexivity. }
 rewrite <- (reference_control_stable_2829_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2829.
 assert (H2830 : VM.find 2830 (history (S time)) = Some (Gval (Fuint 1) [::Z.geb (to_Z rs1) (to_Z rs2)])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2830 reference_control_expr_2830);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2830| |exact Step].
 intros site. unfold reference_control_expr_2830. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2827 H2829. reflexivity. }
 rewrite <- (reference_control_stable_2830_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2830.
 assert (H2848 : VM.find 2848 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2848 reference_control_expr_2848);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2848| |exact Step].
 intros site. unfold reference_control_expr_2848. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2848_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2848.
 assert (H2849 : VM.find 2849 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2849 reference_control_expr_2849);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2849| |exact Step].
 intros site. unfold reference_control_expr_2849. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2849_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2849.
 assert (H2850 : VM.find 2850 (history (S time)) = Some (Gval (Fuint 1) [::N.ltb (to_N rs1) (to_N rs2)])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2850 reference_control_expr_2850);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2850| |exact Step].
 intros site. unfold reference_control_expr_2850. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2848 H2849. reflexivity. }
 rewrite <- (reference_control_stable_2850_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2850.
 assert (H2868 : VM.find 2868 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2868 reference_control_expr_2868);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2868| |exact Step].
 intros site. unfold reference_control_expr_2868. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2868_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2868.
 assert (H2869 : VM.find 2869 (history (S time)) = Some (Gval (Fsint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2869 reference_control_expr_2869);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2869| |exact Step].
 intros site. unfold reference_control_expr_2869. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2868. reflexivity. }
 rewrite <- (reference_control_stable_2869_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2869.
 assert (H2870 : VM.find 2870 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2870 reference_control_expr_2870);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2870| |exact Step].
 intros site. unfold reference_control_expr_2870. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2870_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2870.
 assert (H2871 : VM.find 2871 (history (S time)) = Some (Gval (Fsint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2871 reference_control_expr_2871);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2871| |exact Step].
 intros site. unfold reference_control_expr_2871. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2870. reflexivity. }
 rewrite <- (reference_control_stable_2871_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2871.
 assert (H2872 : VM.find 2872 (history (S time)) = Some (Gval (Fuint 1) [::Z.ltb (to_Z rs1) (to_Z rs2)])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2872 reference_control_expr_2872);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2872| |exact Step].
 intros site. unfold reference_control_expr_2872. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2869 H2871. reflexivity. }
 rewrite <- (reference_control_stable_2872_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2872.
 assert (H2890 : VM.find 2890 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2890 reference_control_expr_2890);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2890| |exact Step].
 intros site. unfold reference_control_expr_2890. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2890_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2890.
 assert (H2891 : VM.find 2891 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2891 reference_control_expr_2891);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2891| |exact Step].
 intros site. unfold reference_control_expr_2891. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2891_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2891.
 assert (H2892 : VM.find 2892 (history (S time)) = Some (Gval (Fuint 1) [::(to_N rs1 != to_N rs2)])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2892 reference_control_expr_2892);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2892| |exact Step].
 intros site. unfold reference_control_expr_2892. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2890 H2891. reflexivity. }
 rewrite <- (reference_control_stable_2892_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2892.
 assert (H2910 : VM.find 2910 (history (S time)) = Some (Gval (Fuint 32) rs1)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2910 reference_control_expr_2910);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2910| |exact Step].
 intros site. unfold reference_control_expr_2910. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2209. reflexivity. }
 rewrite <- (reference_control_stable_2910_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2910.
 assert (H2911 : VM.find 2911 (history (S time)) = Some (Gval (Fuint 32) rs2)).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2911 reference_control_expr_2911);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2911| |exact Step].
 intros site. unfold reference_control_expr_2911. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2804. reflexivity. }
 rewrite <- (reference_control_stable_2911_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2911.
 assert (H2912 : VM.find 2912 (history (S time)) = Some (Gval (Fuint 1) [::(to_N rs1 == to_N rs2)])).
 { eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes 2912 reference_control_expr_2912);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_2912| |exact Step].
 intros site. unfold reference_control_expr_2912. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H2910 H2911. reflexivity. }
 rewrite <- (reference_control_stable_2912_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in H2912.
 repeat split; assumption.
Qed.

Lemma reference_redirect_signed32 bits :
 size bits = 32%nat -> to_Z bits = reference_redirect_signed (to_N bits).
Proof.
 intro Size. unfold reference_redirect_signed.
 change (to_Z bits = if N.testbit (to_N bits) (N.of_nat 31) then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 rewrite redirect_to_N_testbit to_Z_to_Zpos to_Zpos_N redirect_msb_nth Size.
 change ((Z.of_N (to_N bits) - Z.b2z (nth false bits 31) * 4294967296)%Z = if nth false bits 31 then (Z.of_N (to_N bits) - 4294967296)%Z else Z.of_N (to_N bits)).
 destruct (nth false bits 31); cbn [Z.b2z]; rewrite ?Z.mul_1_l ?Z.mul_0_l ?Z.sub_0_r; reflexivity.
Qed.

Lemma reference_redirect_aligned_bits compressed target :
 reference_redirect_aligned compressed target =
 negb (N.testbit target 0) && (compressed || negb (N.testbit target 1)).
Proof.
 unfold reference_redirect_aligned.
 destruct compressed; destruct target as [|[p|p|]]; try reflexivity; destruct p; reflexivity.
Qed.
Lemma reference_redirect_alignment_select compressed bits :
 (if compressed then (to_N (take 1 bits) == 0) else (to_N (take 2 bits) == 0)) =
 reference_redirect_aligned compressed (to_N bits).
Proof.
 rewrite reference_redirect_aligned_bits
  (redirect_to_N_testbit bits 0) (redirect_to_N_testbit bits 1).
 destruct compressed; destruct bits as [|a [|b bits]]; try reflexivity;
 destruct a; try reflexivity; destruct b; cbn [take]; rewrite ?take0; vm_compute; reflexivity.
Qed.
Lemma reference_redirect_aligned_take32_from33 compressed value :
 reference_redirect_aligned compressed (to_N (take 32 (from_N 33 value))) =
 reference_redirect_aligned compressed value.
Proof.
 rewrite !reference_redirect_aligned_bits
  (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 rewrite !nth_take //.
 rewrite -(redirect_to_N_testbit (from_N 33 value) 0)
  -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite !N.mod_pow2_bits_low; reflexivity.
Qed.
Lemma reference_redirect_aligned_jalr compressed value :
 reference_redirect_aligned compressed
  (to_N (false :: take 31 (drop 1 (take 32 (from_N 33 value))))) =
 reference_redirect_aligned compressed (N.clearbit value 0).
Proof.
 rewrite !reference_redirect_aligned_bits N.clearbit_eq
  N.clearbit_neq; [|discriminate].
 rewrite (redirect_to_N_testbit _ 0) (redirect_to_N_testbit _ 1).
 cbn [nth]. rewrite !nth_take // nth_drop.
 change ((true && (compressed || ~~ nth false (take 32 (from_N 33 value)) 1)) =
  (true && (compressed || ~~ N.testbit value 1))).
 rewrite nth_take // -(redirect_to_N_testbit (from_N 33 value) 1) to_N_from_N.
 rewrite N.mod_pow2_bits_low; reflexivity.
Qed.
Theorem reference_redirect_alignments_history inputs path history limit reset time csr pc immediate rs1 :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1750 (history time) = Some (Gval (Fuint 32) csr) ->
 VM.find 1749 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) immediate) ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 size csr = 32%nat ->
 VM.find 2825 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2847 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2867 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2889 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2909 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2929 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]) /\
 VM.find 2949 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (N.clearbit (to_N rs1 + to_N immediate) 0)]) /\
 VM.find 2966 (history time) = Some (Gval (Fuint 1) [::reference_redirect_aligned (N.testbit (to_N csr) 2) (to_N pc + to_N immediate)]).
Proof.
 intros Resets Steps Lower Upper Csr Pc Immediate Rs1 Size.
 pose proof (Steps time Upper) as Step.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2807 reference_control_expr_2807 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2807 ltac:(apply reference_control_ready_2807; first [exact (reference_control_ground_1750_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2807_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2807 E2807].
 unfold reference_control_expr_2807 in E2807.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2808 reference_control_expr_2808 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2808 ltac:(apply reference_control_ready_2808; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2808_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2808 E2808].
 unfold reference_control_expr_2808 in E2808.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2809 reference_control_expr_2809 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2809 ltac:(apply reference_control_ready_2809; first [exact (reference_control_ground_2808_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2809_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2809 E2809].
 unfold reference_control_expr_2809 in E2809.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2810 reference_control_expr_2810 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2810 ltac:(apply reference_control_ready_2810; first [exact (reference_control_ground_2809_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2810_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2810 E2810].
 unfold reference_control_expr_2810 in E2810.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2811 reference_control_expr_2811 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2811 ltac:(apply reference_control_ready_2811; first [exact (reference_control_ground_2810_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2811_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2811 E2811].
 unfold reference_control_expr_2811 in E2811.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2812 reference_control_expr_2812 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2812 ltac:(apply reference_control_ready_2812; first [exact (reference_control_ground_1749_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2812_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2812 E2812].
 unfold reference_control_expr_2812 in E2812.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2813 reference_control_expr_2813 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2813 ltac:(apply reference_control_ready_2813; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2813_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2813 E2813].
 unfold reference_control_expr_2813 in E2813.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2814 reference_control_expr_2814 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2814 ltac:(apply reference_control_ready_2814; first [exact (reference_control_ground_2813_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2814_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2814 E2814].
 unfold reference_control_expr_2814 in E2814.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2815 reference_control_expr_2815 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2815 ltac:(apply reference_control_ready_2815; first [exact (reference_control_ground_2814_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2815_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2815 E2815].
 unfold reference_control_expr_2815 in E2815.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2816 reference_control_expr_2816 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2816 ltac:(apply reference_control_ready_2816; first [exact (reference_control_ground_2815_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2816_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2816 E2816].
 unfold reference_control_expr_2816 in E2816.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2817 reference_control_expr_2817 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2817 ltac:(apply reference_control_ready_2817; first [exact (reference_control_ground_2810_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2817_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2817 E2817].
 unfold reference_control_expr_2817 in E2817.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2818 reference_control_expr_2818 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2818 ltac:(apply reference_control_ready_2818; first [exact (reference_control_ground_2814_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2818_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2818 E2818].
 unfold reference_control_expr_2818 in E2818.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2819 reference_control_expr_2819 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2819 ltac:(apply reference_control_ready_2819; first [exact (reference_control_ground_2818_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2819_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2819 E2819].
 unfold reference_control_expr_2819 in E2819.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2820 reference_control_expr_2820 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2820 ltac:(apply reference_control_ready_2820; first [exact (reference_control_ground_2810_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2820_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2820 E2820].
 unfold reference_control_expr_2820 in E2820.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2821 reference_control_expr_2821 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2821 ltac:(apply reference_control_ready_2821; first [exact (reference_control_ground_2814_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2821_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2821 E2821].
 unfold reference_control_expr_2821 in E2821.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2822 reference_control_expr_2822 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2822 ltac:(apply reference_control_ready_2822; first [exact (reference_control_ground_2821_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2822_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2822 E2822].
 unfold reference_control_expr_2822 in E2822.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2823 reference_control_expr_2823 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2823 ltac:(apply reference_control_ready_2823; first [exact (reference_control_ground_2820_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2822_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2823_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2823 E2823].
 unfold reference_control_expr_2823 in E2823.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2824 reference_control_expr_2824 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2824 ltac:(apply reference_control_ready_2824; first [exact (reference_control_ground_2817_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2819_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2823_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2824_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2824 E2824].
 unfold reference_control_expr_2824 in E2824.
 destruct (reference_redirect_node_equation reference_control_2_offsets reference_control_2_nodes 2825 reference_control_expr_2825 inputs path (history time) (history (S time)) reference_control_2_positions reference_control_2_safety reference_control_member_2825 ltac:(apply reference_control_ready_2825; first [exact (reference_control_ground_2811_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2816_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2824_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2825_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2825 E2825].
 unfold reference_control_expr_2825 in E2825.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2831 reference_control_expr_2831 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2831 ltac:(apply reference_control_ready_2831; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2831_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2831 E2831].
 unfold reference_control_expr_2831 in E2831.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2832 reference_control_expr_2832 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2832 ltac:(apply reference_control_ready_2832; first [exact (reference_control_ground_2831_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2832_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2832 E2832].
 unfold reference_control_expr_2832 in E2832.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2833 reference_control_expr_2833 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2833 ltac:(apply reference_control_ready_2833; first [exact (reference_control_ground_2832_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2833_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2833 E2833].
 unfold reference_control_expr_2833 in E2833.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2834 reference_control_expr_2834 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2834 ltac:(apply reference_control_ready_2834; first [exact (reference_control_ground_2833_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2834_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2834 E2834].
 unfold reference_control_expr_2834 in E2834.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2835 reference_control_expr_2835 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2835 ltac:(apply reference_control_ready_2835; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2835_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2835 E2835].
 unfold reference_control_expr_2835 in E2835.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2836 reference_control_expr_2836 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2836 ltac:(apply reference_control_ready_2836; first [exact (reference_control_ground_2835_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2836_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2836 E2836].
 unfold reference_control_expr_2836 in E2836.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2837 reference_control_expr_2837 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2837 ltac:(apply reference_control_ready_2837; first [exact (reference_control_ground_2836_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2837_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2837 E2837].
 unfold reference_control_expr_2837 in E2837.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2838 reference_control_expr_2838 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2838 ltac:(apply reference_control_ready_2838; first [exact (reference_control_ground_2837_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2838_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2838 E2838].
 unfold reference_control_expr_2838 in E2838.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2839 reference_control_expr_2839 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2839 ltac:(apply reference_control_ready_2839; first [exact (reference_control_ground_2833_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2839_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2839 E2839].
 unfold reference_control_expr_2839 in E2839.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2840 reference_control_expr_2840 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2840 ltac:(apply reference_control_ready_2840; first [exact (reference_control_ground_2836_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2840_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2840 E2840].
 unfold reference_control_expr_2840 in E2840.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2841 reference_control_expr_2841 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2841 ltac:(apply reference_control_ready_2841; first [exact (reference_control_ground_2840_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2841_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2841 E2841].
 unfold reference_control_expr_2841 in E2841.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2842 reference_control_expr_2842 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2842 ltac:(apply reference_control_ready_2842; first [exact (reference_control_ground_2833_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2842_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2842 E2842].
 unfold reference_control_expr_2842 in E2842.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2843 reference_control_expr_2843 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2843 ltac:(apply reference_control_ready_2843; first [exact (reference_control_ground_2836_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2843_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2843 E2843].
 unfold reference_control_expr_2843 in E2843.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2844 reference_control_expr_2844 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2844 ltac:(apply reference_control_ready_2844; first [exact (reference_control_ground_2843_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2844_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2844 E2844].
 unfold reference_control_expr_2844 in E2844.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2845 reference_control_expr_2845 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2845 ltac:(apply reference_control_ready_2845; first [exact (reference_control_ground_2842_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2844_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2845_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2845 E2845].
 unfold reference_control_expr_2845 in E2845.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2846 reference_control_expr_2846 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2846 ltac:(apply reference_control_ready_2846; first [exact (reference_control_ground_2839_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2841_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2845_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2846_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2846 E2846].
 unfold reference_control_expr_2846 in E2846.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2847 reference_control_expr_2847 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2847 ltac:(apply reference_control_ready_2847; first [exact (reference_control_ground_2834_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2838_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2846_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2847_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2847 E2847].
 unfold reference_control_expr_2847 in E2847.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2851 reference_control_expr_2851 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2851 ltac:(apply reference_control_ready_2851; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2851_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2851 E2851].
 unfold reference_control_expr_2851 in E2851.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2852 reference_control_expr_2852 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2852 ltac:(apply reference_control_ready_2852; first [exact (reference_control_ground_2851_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2852_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2852 E2852].
 unfold reference_control_expr_2852 in E2852.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2853 reference_control_expr_2853 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2853 ltac:(apply reference_control_ready_2853; first [exact (reference_control_ground_2852_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2853_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2853 E2853].
 unfold reference_control_expr_2853 in E2853.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2854 reference_control_expr_2854 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2854 ltac:(apply reference_control_ready_2854; first [exact (reference_control_ground_2853_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2854_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2854 E2854].
 unfold reference_control_expr_2854 in E2854.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2855 reference_control_expr_2855 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2855 ltac:(apply reference_control_ready_2855; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2855_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2855 E2855].
 unfold reference_control_expr_2855 in E2855.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2856 reference_control_expr_2856 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2856 ltac:(apply reference_control_ready_2856; first [exact (reference_control_ground_2855_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2856_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2856 E2856].
 unfold reference_control_expr_2856 in E2856.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2857 reference_control_expr_2857 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2857 ltac:(apply reference_control_ready_2857; first [exact (reference_control_ground_2856_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2857_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2857 E2857].
 unfold reference_control_expr_2857 in E2857.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2858 reference_control_expr_2858 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2858 ltac:(apply reference_control_ready_2858; first [exact (reference_control_ground_2857_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2858_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2858 E2858].
 unfold reference_control_expr_2858 in E2858.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2859 reference_control_expr_2859 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2859 ltac:(apply reference_control_ready_2859; first [exact (reference_control_ground_2853_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2859_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2859 E2859].
 unfold reference_control_expr_2859 in E2859.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2860 reference_control_expr_2860 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2860 ltac:(apply reference_control_ready_2860; first [exact (reference_control_ground_2856_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2860_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2860 E2860].
 unfold reference_control_expr_2860 in E2860.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2861 reference_control_expr_2861 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2861 ltac:(apply reference_control_ready_2861; first [exact (reference_control_ground_2860_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2861_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2861 E2861].
 unfold reference_control_expr_2861 in E2861.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2862 reference_control_expr_2862 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2862 ltac:(apply reference_control_ready_2862; first [exact (reference_control_ground_2853_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2862_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2862 E2862].
 unfold reference_control_expr_2862 in E2862.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2863 reference_control_expr_2863 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2863 ltac:(apply reference_control_ready_2863; first [exact (reference_control_ground_2856_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2863_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2863 E2863].
 unfold reference_control_expr_2863 in E2863.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2864 reference_control_expr_2864 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2864 ltac:(apply reference_control_ready_2864; first [exact (reference_control_ground_2863_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2864_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2864 E2864].
 unfold reference_control_expr_2864 in E2864.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2865 reference_control_expr_2865 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2865 ltac:(apply reference_control_ready_2865; first [exact (reference_control_ground_2862_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2864_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2865_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2865 E2865].
 unfold reference_control_expr_2865 in E2865.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2866 reference_control_expr_2866 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2866 ltac:(apply reference_control_ready_2866; first [exact (reference_control_ground_2859_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2861_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2865_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2866_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2866 E2866].
 unfold reference_control_expr_2866 in E2866.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2867 reference_control_expr_2867 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2867 ltac:(apply reference_control_ready_2867; first [exact (reference_control_ground_2854_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2858_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2866_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2867_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2867 E2867].
 unfold reference_control_expr_2867 in E2867.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2873 reference_control_expr_2873 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2873 ltac:(apply reference_control_ready_2873; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2873_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2873 E2873].
 unfold reference_control_expr_2873 in E2873.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2874 reference_control_expr_2874 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2874 ltac:(apply reference_control_ready_2874; first [exact (reference_control_ground_2873_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2874_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2874 E2874].
 unfold reference_control_expr_2874 in E2874.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2875 reference_control_expr_2875 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2875 ltac:(apply reference_control_ready_2875; first [exact (reference_control_ground_2874_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2875_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2875 E2875].
 unfold reference_control_expr_2875 in E2875.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2876 reference_control_expr_2876 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2876 ltac:(apply reference_control_ready_2876; first [exact (reference_control_ground_2875_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2876_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2876 E2876].
 unfold reference_control_expr_2876 in E2876.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2877 reference_control_expr_2877 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2877 ltac:(apply reference_control_ready_2877; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2877_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2877 E2877].
 unfold reference_control_expr_2877 in E2877.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2878 reference_control_expr_2878 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2878 ltac:(apply reference_control_ready_2878; first [exact (reference_control_ground_2877_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2878_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2878 E2878].
 unfold reference_control_expr_2878 in E2878.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2879 reference_control_expr_2879 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2879 ltac:(apply reference_control_ready_2879; first [exact (reference_control_ground_2878_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2879_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2879 E2879].
 unfold reference_control_expr_2879 in E2879.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2880 reference_control_expr_2880 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2880 ltac:(apply reference_control_ready_2880; first [exact (reference_control_ground_2879_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2880_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2880 E2880].
 unfold reference_control_expr_2880 in E2880.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2881 reference_control_expr_2881 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2881 ltac:(apply reference_control_ready_2881; first [exact (reference_control_ground_2875_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2881_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2881 E2881].
 unfold reference_control_expr_2881 in E2881.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2882 reference_control_expr_2882 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2882 ltac:(apply reference_control_ready_2882; first [exact (reference_control_ground_2878_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2882_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2882 E2882].
 unfold reference_control_expr_2882 in E2882.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2883 reference_control_expr_2883 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2883 ltac:(apply reference_control_ready_2883; first [exact (reference_control_ground_2882_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2883_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2883 E2883].
 unfold reference_control_expr_2883 in E2883.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2884 reference_control_expr_2884 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2884 ltac:(apply reference_control_ready_2884; first [exact (reference_control_ground_2875_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2884_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2884 E2884].
 unfold reference_control_expr_2884 in E2884.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2885 reference_control_expr_2885 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2885 ltac:(apply reference_control_ready_2885; first [exact (reference_control_ground_2878_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2885_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2885 E2885].
 unfold reference_control_expr_2885 in E2885.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2886 reference_control_expr_2886 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2886 ltac:(apply reference_control_ready_2886; first [exact (reference_control_ground_2885_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2886_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2886 E2886].
 unfold reference_control_expr_2886 in E2886.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2887 reference_control_expr_2887 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2887 ltac:(apply reference_control_ready_2887; first [exact (reference_control_ground_2884_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2886_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2887_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2887 E2887].
 unfold reference_control_expr_2887 in E2887.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2888 reference_control_expr_2888 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2888 ltac:(apply reference_control_ready_2888; first [exact (reference_control_ground_2881_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2883_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2887_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2888_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2888 E2888].
 unfold reference_control_expr_2888 in E2888.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2889 reference_control_expr_2889 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2889 ltac:(apply reference_control_ready_2889; first [exact (reference_control_ground_2876_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2880_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2888_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2889_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2889 E2889].
 unfold reference_control_expr_2889 in E2889.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2893 reference_control_expr_2893 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2893 ltac:(apply reference_control_ready_2893; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2893_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2893 E2893].
 unfold reference_control_expr_2893 in E2893.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2894 reference_control_expr_2894 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2894 ltac:(apply reference_control_ready_2894; first [exact (reference_control_ground_2893_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2894_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2894 E2894].
 unfold reference_control_expr_2894 in E2894.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2895 reference_control_expr_2895 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2895 ltac:(apply reference_control_ready_2895; first [exact (reference_control_ground_2894_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2895_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2895 E2895].
 unfold reference_control_expr_2895 in E2895.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2896 reference_control_expr_2896 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2896 ltac:(apply reference_control_ready_2896; first [exact (reference_control_ground_2895_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2896_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2896 E2896].
 unfold reference_control_expr_2896 in E2896.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2897 reference_control_expr_2897 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2897 ltac:(apply reference_control_ready_2897; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2897_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2897 E2897].
 unfold reference_control_expr_2897 in E2897.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2898 reference_control_expr_2898 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2898 ltac:(apply reference_control_ready_2898; first [exact (reference_control_ground_2897_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2898_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2898 E2898].
 unfold reference_control_expr_2898 in E2898.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2899 reference_control_expr_2899 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2899 ltac:(apply reference_control_ready_2899; first [exact (reference_control_ground_2898_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2899_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2899 E2899].
 unfold reference_control_expr_2899 in E2899.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2900 reference_control_expr_2900 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2900 ltac:(apply reference_control_ready_2900; first [exact (reference_control_ground_2899_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2900_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2900 E2900].
 unfold reference_control_expr_2900 in E2900.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2901 reference_control_expr_2901 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2901 ltac:(apply reference_control_ready_2901; first [exact (reference_control_ground_2895_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2901_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2901 E2901].
 unfold reference_control_expr_2901 in E2901.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2902 reference_control_expr_2902 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2902 ltac:(apply reference_control_ready_2902; first [exact (reference_control_ground_2898_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2902_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2902 E2902].
 unfold reference_control_expr_2902 in E2902.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2903 reference_control_expr_2903 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2903 ltac:(apply reference_control_ready_2903; first [exact (reference_control_ground_2902_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2903_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2903 E2903].
 unfold reference_control_expr_2903 in E2903.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2904 reference_control_expr_2904 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2904 ltac:(apply reference_control_ready_2904; first [exact (reference_control_ground_2895_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2904_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2904 E2904].
 unfold reference_control_expr_2904 in E2904.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2905 reference_control_expr_2905 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2905 ltac:(apply reference_control_ready_2905; first [exact (reference_control_ground_2898_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2905_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2905 E2905].
 unfold reference_control_expr_2905 in E2905.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2906 reference_control_expr_2906 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2906 ltac:(apply reference_control_ready_2906; first [exact (reference_control_ground_2905_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2906_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2906 E2906].
 unfold reference_control_expr_2906 in E2906.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2907 reference_control_expr_2907 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2907 ltac:(apply reference_control_ready_2907; first [exact (reference_control_ground_2904_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2906_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2907_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2907 E2907].
 unfold reference_control_expr_2907 in E2907.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2908 reference_control_expr_2908 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2908 ltac:(apply reference_control_ready_2908; first [exact (reference_control_ground_2901_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2903_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2907_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2908_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2908 E2908].
 unfold reference_control_expr_2908 in E2908.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2909 reference_control_expr_2909 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2909 ltac:(apply reference_control_ready_2909; first [exact (reference_control_ground_2896_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2900_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2908_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2909_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2909 E2909].
 unfold reference_control_expr_2909 in E2909.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2913 reference_control_expr_2913 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2913 ltac:(apply reference_control_ready_2913; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2913_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2913 E2913].
 unfold reference_control_expr_2913 in E2913.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2914 reference_control_expr_2914 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2914 ltac:(apply reference_control_ready_2914; first [exact (reference_control_ground_2913_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2914_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2914 E2914].
 unfold reference_control_expr_2914 in E2914.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2915 reference_control_expr_2915 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2915 ltac:(apply reference_control_ready_2915; first [exact (reference_control_ground_2914_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2915_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2915 E2915].
 unfold reference_control_expr_2915 in E2915.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2916 reference_control_expr_2916 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2916 ltac:(apply reference_control_ready_2916; first [exact (reference_control_ground_2915_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2916_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2916 E2916].
 unfold reference_control_expr_2916 in E2916.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2917 reference_control_expr_2917 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2917 ltac:(apply reference_control_ready_2917; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2917_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2917 E2917].
 unfold reference_control_expr_2917 in E2917.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2918 reference_control_expr_2918 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2918 ltac:(apply reference_control_ready_2918; first [exact (reference_control_ground_2917_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2918_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2918 E2918].
 unfold reference_control_expr_2918 in E2918.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2919 reference_control_expr_2919 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2919 ltac:(apply reference_control_ready_2919; first [exact (reference_control_ground_2918_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2919_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2919 E2919].
 unfold reference_control_expr_2919 in E2919.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2920 reference_control_expr_2920 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2920 ltac:(apply reference_control_ready_2920; first [exact (reference_control_ground_2919_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2920_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2920 E2920].
 unfold reference_control_expr_2920 in E2920.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2921 reference_control_expr_2921 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2921 ltac:(apply reference_control_ready_2921; first [exact (reference_control_ground_2915_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2921_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2921 E2921].
 unfold reference_control_expr_2921 in E2921.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2922 reference_control_expr_2922 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2922 ltac:(apply reference_control_ready_2922; first [exact (reference_control_ground_2918_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2922_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2922 E2922].
 unfold reference_control_expr_2922 in E2922.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2923 reference_control_expr_2923 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2923 ltac:(apply reference_control_ready_2923; first [exact (reference_control_ground_2922_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2923_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2923 E2923].
 unfold reference_control_expr_2923 in E2923.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2924 reference_control_expr_2924 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2924 ltac:(apply reference_control_ready_2924; first [exact (reference_control_ground_2915_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2924_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2924 E2924].
 unfold reference_control_expr_2924 in E2924.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2925 reference_control_expr_2925 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2925 ltac:(apply reference_control_ready_2925; first [exact (reference_control_ground_2918_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2925_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2925 E2925].
 unfold reference_control_expr_2925 in E2925.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2926 reference_control_expr_2926 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2926 ltac:(apply reference_control_ready_2926; first [exact (reference_control_ground_2925_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2926_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2926 E2926].
 unfold reference_control_expr_2926 in E2926.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2927 reference_control_expr_2927 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2927 ltac:(apply reference_control_ready_2927; first [exact (reference_control_ground_2924_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2926_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2927_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2927 E2927].
 unfold reference_control_expr_2927 in E2927.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2928 reference_control_expr_2928 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2928 ltac:(apply reference_control_ready_2928; first [exact (reference_control_ground_2921_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2923_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2927_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2928_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2928 E2928].
 unfold reference_control_expr_2928 in E2928.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2929 reference_control_expr_2929 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2929 ltac:(apply reference_control_ready_2929; first [exact (reference_control_ground_2916_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2920_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2928_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2929_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2929 E2929].
 unfold reference_control_expr_2929 in E2929.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2930 reference_control_expr_2930 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2930 ltac:(apply reference_control_ready_2930; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2930_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2930 E2930].
 unfold reference_control_expr_2930 in E2930.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2931 reference_control_expr_2931 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2931 ltac:(apply reference_control_ready_2931; first [exact (reference_control_ground_2930_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2931_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2931 E2931].
 unfold reference_control_expr_2931 in E2931.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2932 reference_control_expr_2932 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2932 ltac:(apply reference_control_ready_2932; first [exact (reference_control_ground_2931_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2932_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2932 E2932].
 unfold reference_control_expr_2932 in E2932.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2933 reference_control_expr_2933 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2933 ltac:(apply reference_control_ready_2933; first [exact (reference_control_ground_2932_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2933_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2933 E2933].
 unfold reference_control_expr_2933 in E2933.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2934 reference_control_expr_2934 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2934 ltac:(apply reference_control_ready_2934; first [exact (reference_control_ground_2209_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2934_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2934 E2934].
 unfold reference_control_expr_2934 in E2934.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2935 reference_control_expr_2935 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2935 ltac:(apply reference_control_ready_2935; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2934_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2935_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2935 E2935].
 unfold reference_control_expr_2935 in E2935.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2936 reference_control_expr_2936 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2936 ltac:(apply reference_control_ready_2936; first [exact (reference_control_ground_2935_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2936_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2936 E2936].
 unfold reference_control_expr_2936 in E2936.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2937 reference_control_expr_2937 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2937 ltac:(apply reference_control_ready_2937; first [exact (reference_control_ground_2936_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2937_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2937 E2937].
 unfold reference_control_expr_2937 in E2937.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2938 reference_control_expr_2938 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2938 ltac:(apply reference_control_ready_2938; first [exact (reference_control_ground_2937_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2938_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2938 E2938].
 unfold reference_control_expr_2938 in E2938.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2939 reference_control_expr_2939 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2939 ltac:(apply reference_control_ready_2939; first [exact (reference_control_ground_2938_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2939_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2939 E2939].
 unfold reference_control_expr_2939 in E2939.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2940 reference_control_expr_2940 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2940 ltac:(apply reference_control_ready_2940; first [exact (reference_control_ground_2939_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2940_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2940 E2940].
 unfold reference_control_expr_2940 in E2940.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2941 reference_control_expr_2941 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2941 ltac:(apply reference_control_ready_2941; first [exact (reference_control_ground_2932_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2941_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2941 E2941].
 unfold reference_control_expr_2941 in E2941.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2942 reference_control_expr_2942 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2942 ltac:(apply reference_control_ready_2942; first [exact (reference_control_ground_2938_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2942_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2942 E2942].
 unfold reference_control_expr_2942 in E2942.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2943 reference_control_expr_2943 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2943 ltac:(apply reference_control_ready_2943; first [exact (reference_control_ground_2942_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2943_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2943 E2943].
 unfold reference_control_expr_2943 in E2943.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2944 reference_control_expr_2944 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2944 ltac:(apply reference_control_ready_2944; first [exact (reference_control_ground_2932_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2944_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2944 E2944].
 unfold reference_control_expr_2944 in E2944.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2945 reference_control_expr_2945 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2945 ltac:(apply reference_control_ready_2945; first [exact (reference_control_ground_2938_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2945_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2945 E2945].
 unfold reference_control_expr_2945 in E2945.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2946 reference_control_expr_2946 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2946 ltac:(apply reference_control_ready_2946; first [exact (reference_control_ground_2945_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2946_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2946 E2946].
 unfold reference_control_expr_2946 in E2946.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2947 reference_control_expr_2947 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2947 ltac:(apply reference_control_ready_2947; first [exact (reference_control_ground_2944_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2946_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2947_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2947 E2947].
 unfold reference_control_expr_2947 in E2947.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2948 reference_control_expr_2948 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2948 ltac:(apply reference_control_ready_2948; first [exact (reference_control_ground_2941_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2943_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2947_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2948_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2948 E2948].
 unfold reference_control_expr_2948 in E2948.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2949 reference_control_expr_2949 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2949 ltac:(apply reference_control_ready_2949; first [exact (reference_control_ground_2933_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2940_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2948_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2949_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2949 E2949].
 unfold reference_control_expr_2949 in E2949.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2950 reference_control_expr_2950 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2950 ltac:(apply reference_control_ready_2950; first [exact (reference_control_ground_2807_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2950_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2950 E2950].
 unfold reference_control_expr_2950 in E2950.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2951 reference_control_expr_2951 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2951 ltac:(apply reference_control_ready_2951; first [exact (reference_control_ground_2950_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2951_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2951 E2951].
 unfold reference_control_expr_2951 in E2951.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2952 reference_control_expr_2952 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2952 ltac:(apply reference_control_ready_2952; first [exact (reference_control_ground_2951_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2952_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2952 E2952].
 unfold reference_control_expr_2952 in E2952.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2953 reference_control_expr_2953 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2953 ltac:(apply reference_control_ready_2953; first [exact (reference_control_ground_2952_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2953_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2953 E2953].
 unfold reference_control_expr_2953 in E2953.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2954 reference_control_expr_2954 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2954 ltac:(apply reference_control_ready_2954; first [exact (reference_control_ground_2552_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2812_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2954_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2954 E2954].
 unfold reference_control_expr_2954 in E2954.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2955 reference_control_expr_2955 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2955 ltac:(apply reference_control_ready_2955; first [exact (reference_control_ground_2954_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2955_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2955 E2955].
 unfold reference_control_expr_2955 in E2955.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2956 reference_control_expr_2956 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2956 ltac:(apply reference_control_ready_2956; first [exact (reference_control_ground_2955_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2956_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2956 E2956].
 unfold reference_control_expr_2956 in E2956.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2957 reference_control_expr_2957 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2957 ltac:(apply reference_control_ready_2957; first [exact (reference_control_ground_2956_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2957_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2957 E2957].
 unfold reference_control_expr_2957 in E2957.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2958 reference_control_expr_2958 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2958 ltac:(apply reference_control_ready_2958; first [exact (reference_control_ground_2952_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2958_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2958 E2958].
 unfold reference_control_expr_2958 in E2958.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2959 reference_control_expr_2959 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2959 ltac:(apply reference_control_ready_2959; first [exact (reference_control_ground_2955_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2959_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2959 E2959].
 unfold reference_control_expr_2959 in E2959.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2960 reference_control_expr_2960 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2960 ltac:(apply reference_control_ready_2960; first [exact (reference_control_ground_2959_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2960_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2960 E2960].
 unfold reference_control_expr_2960 in E2960.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2961 reference_control_expr_2961 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2961 ltac:(apply reference_control_ready_2961; first [exact (reference_control_ground_2952_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2961_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2961 E2961].
 unfold reference_control_expr_2961 in E2961.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2962 reference_control_expr_2962 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2962 ltac:(apply reference_control_ready_2962; first [exact (reference_control_ground_2955_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2962_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2962 E2962].
 unfold reference_control_expr_2962 in E2962.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2963 reference_control_expr_2963 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2963 ltac:(apply reference_control_ready_2963; first [exact (reference_control_ground_2962_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2963_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2963 E2963].
 unfold reference_control_expr_2963 in E2963.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2964 reference_control_expr_2964 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2964 ltac:(apply reference_control_ready_2964; first [exact (reference_control_ground_2961_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2963_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2964_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2964 E2964].
 unfold reference_control_expr_2964 in E2964.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2965 reference_control_expr_2965 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2965 ltac:(apply reference_control_ready_2965; first [exact (reference_control_ground_2958_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2960_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2964_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2965_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2965 E2965].
 unfold reference_control_expr_2965 in E2965.
 destruct (reference_redirect_node_equation reference_control_3_offsets reference_control_3_nodes 2966 reference_control_expr_2966 inputs path (history time) (history (S time)) reference_control_3_positions reference_control_3_safety reference_control_member_2966 ltac:(apply reference_control_ready_2966; first [exact (reference_control_ground_2953_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2957_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))|exact (reference_control_ground_2965_history inputs path history limit reset Resets Steps time ltac:(lia) ltac:(lia))]) Step (reference_control_stable_2966_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))) as [site2966 E2966].
 unfold reference_control_expr_2966 in E2966.
 repeat split.
 - rewrite E2825.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2825 ?E2824 ?E2823 ?E2822 ?E2821 ?E2820 ?E2819 ?E2818 ?E2817 ?E2816 ?E2815 ?E2814 ?E2813 ?E2812 ?E2811 ?E2810 ?E2809 ?E2808 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2847.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2847 ?E2846 ?E2845 ?E2844 ?E2843 ?E2842 ?E2841 ?E2840 ?E2839 ?E2838 ?E2837 ?E2836 ?E2835 ?E2834 ?E2833 ?E2832 ?E2831 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2867.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2867 ?E2866 ?E2865 ?E2864 ?E2863 ?E2862 ?E2861 ?E2860 ?E2859 ?E2858 ?E2857 ?E2856 ?E2855 ?E2854 ?E2853 ?E2852 ?E2851 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2889.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2889 ?E2888 ?E2887 ?E2886 ?E2885 ?E2884 ?E2883 ?E2882 ?E2881 ?E2880 ?E2879 ?E2878 ?E2877 ?E2876 ?E2875 ?E2874 ?E2873 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2909.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2909 ?E2908 ?E2907 ?E2906 ?E2905 ?E2904 ?E2903 ?E2902 ?E2901 ?E2900 ?E2899 ?E2898 ?E2897 ?E2896 ?E2895 ?E2894 ?E2893 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2929.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2929 ?E2928 ?E2927 ?E2926 ?E2925 ?E2924 ?E2923 ?E2922 ?E2921 ?E2920 ?E2919 ?E2918 ?E2917 ?E2916 ?E2915 ?E2914 ?E2913 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
 - rewrite E2949.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2949 ?E2948 ?E2947 ?E2946 ?E2945 ?E2944 ?E2943 ?E2942 ?E2941 ?E2940 ?E2939 ?E2938 ?E2937 ?E2936 ?E2935 ?E2934 ?E2933 ?E2932 ?E2931 ?E2930 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (false :: take 31 (drop 1 (take 32 (from_N 33 (to_N rs1 + to_N immediate)))))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (N.clearbit (to_N rs1 + to_N immediate) 0)])).
     rewrite (reference_redirect_alignment_select true (false :: take 31 (drop 1 (take 32 (from_N 33 (to_N rs1 + to_N immediate)))))).
     rewrite reference_redirect_aligned_jalr. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (false :: take 31 (drop 1 (take 32 (from_N 33 (to_N rs1 + to_N immediate)))))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (N.clearbit (to_N rs1 + to_N immediate) 0)])).
     rewrite (reference_redirect_alignment_select false (false :: take 31 (drop 1 (take 32 (from_N 33 (to_N rs1 + to_N immediate)))))).
     rewrite reference_redirect_aligned_jalr. reflexivity.
 - rewrite E2966.
   repeat (progress (cbn [eval_hfexpr_validif_policy eval_href_validif_policy]; try unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite ?E2966 ?E2965 ?E2964 ?E2963 ?E2962 ?E2961 ?E2960 ?E2959 ?E2958 ?E2957 ?E2956 ?E2955 ?E2954 ?E2953 ?E2952 ?E2951 ?E2950 ?E2812 ?E2807 ?Csr ?Pc ?Immediate ?Rs1)).
   cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
   rewrite (reference_redirect_csr_compressed csr Size).
   destruct (N.testbit (to_N csr) 2);
   cbn [eval_binop eval_binop_basic absorbing_bit exact_bit refine_boolean_result eval_unop type_of_val ftype_mux make_ftype_explicit extend_hvalue_as_type size ltn leq zext_to zext zeros copy to_N foldr];
   cbv -[from_N reference_redirect_aligned].
   + change (Some (Gval (Fuint 1) [::to_N (take 1 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned true (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select true (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
   + change (Some (Gval (Fuint 1) [::to_N (take 2 (take 32 (from_N 33 (to_N pc + to_N immediate)))) == 0]) = Some (Gval (Fuint 1) [::reference_redirect_aligned false (to_N pc + to_N immediate)])).
     rewrite (reference_redirect_alignment_select false (take 32 (from_N 33 (to_N pc + to_N immediate)))).
     rewrite reference_redirect_aligned_take32_from33. reflexivity.
Qed.

Require Import ReferenceControlWires2 FormalDeclaredConnection.
Lemma reference_redirect_adapt_word bits :
 size bits = 32%nat ->
 adapt_hvalue_as_type (Gval (Fuint 32) bits) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) bits).
Proof.
 intro Size. cbn [adapt_hvalue_as_type]. rewrite <- Size, take_size.
 unfold zext_to. rewrite subnn. unfold zext. rewrite zeros0 cats0. reflexivity.
Qed.
Theorem reference_redirect_aliases_history inputs path history limit reset time pc csr :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 7331 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (history time) = Some (Gval (Fuint 32) csr) ->
 size pc = 32%nat -> size csr = 32%nat ->
 VM.find 1749 (history time) = Some (Gval (Fuint 32) pc) /\
 VM.find 1750 (history time) = Some (Gval (Fuint 32) csr).
Proof.
 intros Resets Steps Lower Upper Pc Csr PcSize CsrSize.
 pose proof (Steps time Upper) as Step.
 split.
 - rewrite (reference_control_stable_1749_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (declared_connection_value 1828 flat_statements reference_control_wire_1749_decl reference_control_wire_1749_mid reference_control_wire_1749_tail 1749 7331 32 (Gval (Fuint 32) pc));
   [exact reference_control_wire_1749_position|exact reference_control_wire_1749_split|exact reference_control_wire_1749_straight|exact reference_control_wire_1749_mid_safe|exact reference_control_wire_1749_tail_safe|exact reference_control_wire_1749_nonregister|reflexivity|exact Pc|apply reference_redirect_adapt_word; exact PcSize|exact Step].
 - rewrite (reference_control_stable_1750_history inputs path history limit reset Resets Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
   eapply (declared_connection_value 1829 flat_statements reference_control_wire_1750_decl reference_control_wire_1750_mid reference_control_wire_1750_tail 1750 7332 32 (Gval (Fuint 32) csr));
   [exact reference_control_wire_1750_position|exact reference_control_wire_1750_split|exact reference_control_wire_1750_straight|exact reference_control_wire_1750_mid_safe|exact reference_control_wire_1750_tail_safe|exact reference_control_wire_1750_nonregister|reflexivity|exact Csr|apply reference_redirect_adapt_word; exact CsrSize|exact Step].
Qed.

Theorem reference_redirect_function_history inputs path history limit reset time instruction rs1 rs2 immediate pc csr :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (127 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 1884 (history time) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (history time) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (history time) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (history time) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (history time) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (history time) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6507 (history time) = Some (Gval (Fuint 1)
 [::reference_redirect_function (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)]).
Proof.
 intros Resets Steps Lower Upper Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (reference_redirect_aliases_history inputs path history limit reset time pc csr Resets Steps Lower Upper Pc Csr PcSize CsrSize) as [PcAlias CsrAlias].
 destruct (reference_redirect_decoders_history inputs path history limit reset time instruction Resets Steps Lower Upper Instruction)
 as [H1974 [H1980 [H1986 [H1992 [H1998 [H2004 [H2010 H2357]]]]]]].
 destruct (reference_redirect_comparisons_history inputs path history limit reset time rs1 rs2 Resets Steps Lower Upper Rs1 Rs2)
 as [H2806 [H2830 [H2850 [H2872 [H2892 H2912]]]]].
 destruct (reference_redirect_alignments_history inputs path history limit reset time csr pc immediate rs1 Resets Steps Lower Upper CsrAlias PcAlias Immediate Rs1 CsrSize)
 as [H2825 [H2847 [H2867 [H2889 [H2909 [H2929 [H2949 H2966]]]]]]].
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) Z.geb_leb in H2830.
 rewrite (reference_redirect_signed32 rs1 Rs1Size) (reference_redirect_signed32 rs2 Rs2Size) in H2872.
 rewrite redirect_N_eqb in H2892, H2912.
 rewrite <- (reference_redirect_guards_normalize (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)).
 eapply (reference_redirect_spine_history inputs path history limit reset time); assumption.
Qed.

Require Import FormalObservedHistory FormalLocalHistory.
Theorem reference_redirect_function_observed memory inputs k observed instruction rs1 rs2 immediate pc csr :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1884 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2804 (top_environment observed) = Some (Gval (Fuint 32) rs2) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 7332 (top_environment observed) = Some (Gval (Fuint 32) csr) ->
 size rs1 = 32%nat -> size rs2 = 32%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 6507 (top_environment observed) = Some (Gval (Fuint 1)
 [::reference_redirect_function (to_N instruction) (to_N rs1) (to_N rs2) (to_N immediate) (to_N pc) (to_N csr)]).
Proof.
 intros Observe Legal Instruction Rs1 Rs2 Immediate Pc Csr Rs1Size Rs2Size PcSize CsrSize.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last.
 rewrite <- (reference_control_stable_6507_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
 eapply (reference_redirect_function_history (generated_observation_input inputs k) nil history 9259 reset 9258 instruction rs1 rs2 immediate pc csr Resets Steps ltac:(vm_compute;lia) ltac:(vm_compute;lia)); try assumption.
 - rewrite (reference_control_stable_1884_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Instruction.
 - rewrite (reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs1.
 - rewrite (reference_control_stable_2804_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Rs2.
 - rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Immediate.
 - rewrite (reference_control_stable_7331_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Pc.
 - rewrite (reference_control_stable_7332_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9258 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Last. exact Csr.
Qed.
