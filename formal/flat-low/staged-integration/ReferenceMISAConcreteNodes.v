Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip DUTRedirectDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_misa_word := from_N 32 1073746176.
Definition misa_7270_expr := (@Eprim_unop VarOrder.T (Ushl 30) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition misa_7270_tail := match straight_drop 7442 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7270_position : straight_drop 7441 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7270 misa_7270_expr)misa_7270_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7270_safe : formal_typed_suffix_safe flat_memories 7270 misa_7270_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7270_nonreg : has_register 7270 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7270_step invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7270 result=Some(Gval(Fuint 31)(from_N 31 1073741824)).
Proof.
 intros  Step.
 eapply formal_combinational_known_node;[exact misa_7270_position|exact misa_7270_safe|exact misa_7270_nonreg| |reflexivity|exact Step].
 cbn [misa_7270_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity.
Qed.
Lemma misa_7270_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7270(history t)=Some(Gval(Fuint 31)(from_N 31 1073741824)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7270_step.
 - apply Steps;lia.
Qed.
Definition misa_7271_expr := (@Eprim_unop VarOrder.T (Ushl 8) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition misa_7271_tail := match straight_drop 7443 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7271_position : straight_drop 7442 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7271 misa_7271_expr)misa_7271_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7271_safe : formal_typed_suffix_safe flat_memories 7271 misa_7271_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7271_nonreg : has_register 7271 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7271_step invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7271 result=Some(Gval(Fuint 9)(from_N 9 256)).
Proof.
 intros  Step.
 eapply formal_combinational_known_node;[exact misa_7271_position|exact misa_7271_safe|exact misa_7271_nonreg| |reflexivity|exact Step].
 cbn [misa_7271_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity.
Qed.
Lemma misa_7271_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7271(history t)=Some(Gval(Fuint 9)(from_N 9 256)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7271_step.
 - apply Steps;lia.
Qed.
Definition misa_7272_expr := (@Eprim_binop VarOrder.T Bor (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7271))).
Definition misa_7272_tail := match straight_drop 7444 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7272_position : straight_drop 7443 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7272 misa_7272_expr)misa_7272_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7272_safe : formal_typed_suffix_safe flat_memories 7272 misa_7272_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7272_nonreg : has_register 7272 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7272_step invalid old result :
 VM.find 7271 old=Some(Gval(Fuint 9)(from_N 9 256)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7272 result=Some(Gval(Fuint 9)(from_N 9 256)).
Proof.
 intros H7271 Step.
 eapply formal_combinational_known_node;[exact misa_7272_position|exact misa_7272_safe|exact misa_7272_nonreg| |reflexivity|exact Step].
 cbn [misa_7272_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7271.
 reflexivity.
Qed.
Lemma misa_7272_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7272(history t)=Some(Gval(Fuint 9)(from_N 9 256)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7272_step.
 - apply(misa_7271_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_7273_expr := (@Eprim_unop VarOrder.T (Ushl 12) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition misa_7273_tail := match straight_drop 7445 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7273_position : straight_drop 7444 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7273 misa_7273_expr)misa_7273_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7273_safe : formal_typed_suffix_safe flat_memories 7273 misa_7273_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7273_nonreg : has_register 7273 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7273_step invalid old result :
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7273 result=Some(Gval(Fuint 13)(from_N 13 4096)).
Proof.
 intros  Step.
 eapply formal_combinational_known_node;[exact misa_7273_position|exact misa_7273_safe|exact misa_7273_nonreg| |reflexivity|exact Step].
 cbn [misa_7273_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity.
Qed.
Lemma misa_7273_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7273(history t)=Some(Gval(Fuint 13)(from_N 13 4096)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7273_step.
 - apply Steps;lia.
Qed.
Definition misa_7274_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7272)) (@Eref VarOrder.T (@Eid VarOrder.T 7273))).
Definition misa_7274_tail := match straight_drop 7446 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7274_position : straight_drop 7445 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7274 misa_7274_expr)misa_7274_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7274_safe : formal_typed_suffix_safe flat_memories 7274 misa_7274_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7274_nonreg : has_register 7274 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7274_step invalid old result :
 VM.find 7272 old=Some(Gval(Fuint 9)(from_N 9 256)) ->
 VM.find 7273 old=Some(Gval(Fuint 13)(from_N 13 4096)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7274 result=Some(Gval(Fuint 13)(from_N 13 4352)).
Proof.
 intros H7272 H7273 Step.
 eapply formal_combinational_known_node;[exact misa_7274_position|exact misa_7274_safe|exact misa_7274_nonreg| |reflexivity|exact Step].
 cbn [misa_7274_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7272 H7273.
 reflexivity.
Qed.
Lemma misa_7274_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7274(history t)=Some(Gval(Fuint 13)(from_N 13 4352)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7274_step.
 - apply(misa_7272_history invalid history limit Steps t);lia.
 - apply(misa_7273_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_7275_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7270)) (@Eref VarOrder.T (@Eid VarOrder.T 7274))).
Definition misa_7275_tail := match straight_drop 7447 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7275_position : straight_drop 7446 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7275 misa_7275_expr)misa_7275_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7275_safe : formal_typed_suffix_safe flat_memories 7275 misa_7275_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7275_nonreg : has_register 7275 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7275_step invalid old result :
 VM.find 7270 old=Some(Gval(Fuint 31)(from_N 31 1073741824)) ->
 VM.find 7274 old=Some(Gval(Fuint 13)(from_N 13 4352)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7275 result=Some(Gval(Fuint 31)(from_N 31 1073746176)).
Proof.
 intros H7270 H7274 Step.
 eapply formal_combinational_known_node;[exact misa_7275_position|exact misa_7275_safe|exact misa_7275_nonreg| |reflexivity|exact Step].
 cbn [misa_7275_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7270 H7274.
 reflexivity.
Qed.
Lemma misa_7275_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7275(history t)=Some(Gval(Fuint 31)(from_N 31 1073746176)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7275_step.
 - apply(misa_7270_history invalid history limit Steps t);lia.
 - apply(misa_7274_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_7434_expr := (@Eprim_unop VarOrder.T (Upad 32) (@Eref VarOrder.T (@Eid VarOrder.T 7275))).
Definition misa_7434_tail := match straight_drop 7606 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7434_position : straight_drop 7605 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7434 misa_7434_expr)misa_7434_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7434_safe : formal_typed_suffix_safe flat_memories 7434 misa_7434_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7434_nonreg : has_register 7434 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7434_step invalid old result :
 VM.find 7275 old=Some(Gval(Fuint 31)(from_N 31 1073746176)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7434 result=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros H7275 Step.
 eapply formal_combinational_known_node;[exact misa_7434_position|exact misa_7434_safe|exact misa_7434_nonreg| |reflexivity|exact Step].
 cbn [misa_7434_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7275.
 reflexivity.
Qed.
Lemma misa_7434_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7434(history t)=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7434_step.
 - apply(misa_7275_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_7435_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7434)).
Definition misa_7435_tail := match straight_drop 7607 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7435_position : straight_drop 7606 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7435 misa_7435_expr)misa_7435_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7435_safe : formal_typed_suffix_safe flat_memories 7435 misa_7435_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7435_nonreg : has_register 7435 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7435_step invalid old result :
 VM.find 7434 old=Some(Gval(Fuint 32)(from_N 32 1073746176)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7435 result=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros H7434 Step.
 eapply formal_combinational_known_node;[exact misa_7435_position|exact misa_7435_safe|exact misa_7435_nonreg| |reflexivity|exact Step].
 cbn [misa_7435_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7434.
 reflexivity.
Qed.
Lemma misa_7435_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7435(history t)=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7435_step.
 - apply(misa_7434_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_7436_expr := (@Eref VarOrder.T (@Eid VarOrder.T 7435)).
Definition misa_7436_tail := match straight_drop 7608 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7436_position : straight_drop 7607 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7436 misa_7436_expr)misa_7436_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7436_safe : formal_typed_suffix_safe flat_memories 7436 misa_7436_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7436_nonreg : has_register 7436 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7436_step invalid old result :
 VM.find 7435 old=Some(Gval(Fuint 32)(from_N 32 1073746176)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find 7436 result=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros H7435 Step.
 eapply formal_combinational_known_node;[exact misa_7436_position|exact misa_7436_safe|exact misa_7436_nonreg| |reflexivity|exact Step].
 cbn [misa_7436_expr eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite H7435.
 reflexivity.
Qed.
Lemma misa_7436_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7436(history t)=Some(Gval(Fuint 32)(from_N 32 1073746176)).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply misa_7436_step.
 - apply(misa_7435_history invalid history limit Steps t);lia.
 - apply Steps;lia.
Qed.
Definition misa_1750_decl := match straight_drop 1830 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_1750_tail := match straight_drop 7998 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_1750_mid := take_statements 6167 misa_1750_decl.
Lemma misa_1750_position : straight_drop 1829 flat_statements=Some(@Qcons VarOrder.T(@Swire VarOrder.T 1750(Gtyp(Fuint 32)))misa_1750_decl).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1750_split : misa_1750_decl=statement_append misa_1750_mid(@Qcons VarOrder.T(@Sfcnct VarOrder.T(@Eid VarOrder.T 1750)(@Eref VarOrder.T (@Eid VarOrder.T 7332)))misa_1750_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1750_straight : straight_statements misa_1750_mid.
Proof. vm_compute;exact I. Qed.
Lemma misa_1750_mid_safe : formal_typed_suffix_safe flat_memories 1750 misa_1750_mid.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_1750_tail_safe : formal_typed_suffix_safe flat_memories 1750 misa_1750_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_1750_nonreg : has_register 1750 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1750_step invalid old result word :
 size word=32%nat ->VM.find 7332 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 1750 result=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source Step.
 eapply(declared_connection_value 1829 flat_statements misa_1750_decl misa_1750_mid misa_1750_tail 1750 7332 32);
 [exact misa_1750_position|exact misa_1750_split|exact misa_1750_straight|exact misa_1750_mid_safe|exact misa_1750_tail_safe|exact misa_1750_nonreg|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step].
Qed.
Definition misa_2807_expr := (@Eref VarOrder.T (@Eid VarOrder.T 1750)).
Definition misa_2807_tail := match straight_drop 2887 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_2807_position : straight_drop 2886 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 2807 misa_2807_expr)misa_2807_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_2807_safe : formal_typed_suffix_safe flat_memories 2807 misa_2807_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_2807_nonreg : has_register 2807 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_2807_step invalid old result word :
 size word=32%nat ->VM.find 1750 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 2807 result=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source Step.
 eapply formal_combinational_known_node;[exact misa_2807_position|exact misa_2807_safe|exact misa_2807_nonreg|exact Source|reflexivity|exact Step].
Qed.
Definition misa_7150_expr := (@Eref VarOrder.T (@Eid VarOrder.T 2807)).
Definition misa_7150_tail := match straight_drop 7230 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma misa_7150_position : straight_drop 7229 flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7150 misa_7150_expr)misa_7150_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7150_safe : formal_typed_suffix_safe flat_memories 7150 misa_7150_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_7150_nonreg : has_register 7150 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_7150_step invalid old result word :
 size word=32%nat ->VM.find 2807 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 7150 result=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source Step.
 eapply formal_combinational_known_node;[exact misa_7150_position|exact misa_7150_safe|exact misa_7150_nonreg|exact Source|reflexivity|exact Step].
Qed.
Definition misa_1820_decl := match straight_drop 1900 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_1820_tail := match straight_drop 7391 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_1820_mid := take_statements 5490 misa_1820_decl.
Lemma misa_1820_position : straight_drop 1899 flat_statements=Some(@Qcons VarOrder.T(@Swire VarOrder.T 1820(Gtyp(Fuint 32)))misa_1820_decl).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1820_split : misa_1820_decl=statement_append misa_1820_mid(@Qcons VarOrder.T(@Sfcnct VarOrder.T(@Eid VarOrder.T 1820)(@Eref VarOrder.T (@Eid VarOrder.T 7150)))misa_1820_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1820_straight : straight_statements misa_1820_mid.
Proof. vm_compute;exact I. Qed.
Lemma misa_1820_mid_safe : formal_typed_suffix_safe flat_memories 1820 misa_1820_mid.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_1820_tail_safe : formal_typed_suffix_safe flat_memories 1820 misa_1820_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_1820_nonreg : has_register 1820 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma misa_1820_step invalid old result word :
 size word=32%nat ->VM.find 7150 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find 1820 result=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source Step.
 eapply(declared_connection_value 1899 flat_statements misa_1820_decl misa_1820_mid misa_1820_tail 1820 7150 32);
 [exact misa_1820_position|exact misa_1820_split|exact misa_1820_straight|exact misa_1820_mid_safe|exact misa_1820_tail_safe|exact misa_1820_nonreg|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step].
Qed.
Definition misa_register_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7332)))).
Definition misa_register_decl := match straight_drop 7504 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_register_tail := match straight_drop 7923 flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition misa_register_mid := take_statements 418 misa_register_decl.
Lemma misa_register_position : straight_drop 7503 flat_statements=Some(@Qcons VarOrder.T(@Sreg VarOrder.T 7332 misa_register_reg)misa_register_decl).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_register_split : misa_register_decl=statement_append misa_register_mid(@Qcons VarOrder.T(@Sfcnct VarOrder.T(@Eid VarOrder.T 7332)(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7436)) (@Eref VarOrder.T (@Eid VarOrder.T 1820))))misa_register_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma misa_register_straight : straight_statements misa_register_mid.
Proof. vm_compute;exact I. Qed.
Lemma misa_register_mid_safe : formal_typed_suffix_safe flat_memories 7332 misa_register_mid.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_register_tail_safe : formal_typed_suffix_safe flat_memories 7332 misa_register_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma misa_register_identity : register_identity_b 7332 flat_statements.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem misa_commit invalid old result word bit :
 size word=32%nat ->VM.find 7332 old=Some(Gval(Fuint 32)word) ->
 VM.find 1515 old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find 7436 old=Some(Gval(Fuint 32)reference_misa_word) ->
 VM.find 1820 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old true old flat_statements=Some result ->
 VM.find 7332 result=Some(Gval(Fuint 32)(if bit then reference_misa_word else word)).
Proof.
 intros Size Old Reset Yes No Step.
 destruct(formal_committed_uint_register_mux_observation 7503 flat_statements misa_register_decl misa_register_mid misa_register_tail 7332 misa_register_reg
 (@Eref VarOrder.T(@Eid VarOrder.T 1515))(@Eref VarOrder.T(@Eid VarOrder.T 7436))(@Eref VarOrder.T(@Eid VarOrder.T 1820)) invalid flat_memories old old result(Gval(Fuint 32)word)32
 misa_register_position misa_register_split misa_register_straight misa_register_mid_safe misa_register_tail_safe Old(Logic.eq_refl _)misa_register_identity Step)as[source[value[Source[Adapt Value]]]].
 change(eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7436)) (@Eref VarOrder.T (@Eid VarOrder.T 1820))) old old=Some source)in Source.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]in Source.
 rewrite Reset in Source. destruct bit;cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]in Source;rewrite ?Yes ?No in Source;
 unfold eval_type_of_expr in Source;cbn [type_of_expr' eval_type_of_ref]in Source;rewrite ?Yes ?No in Source.
 - inversion Source;subst source. cbn [adapt_hvalue_as_type]in Adapt. inversion Adapt;subst value. exact Value.
 - inversion Source;subst source.
   cbn [extend_hvalue_as_type adapt_hvalue_as_type]in Adapt.
   inversion Adapt;subst value. rewrite(resize_uint_roundtrip 32 32 word Size (leqnn 32))in Value. exact Value.
Qed.
