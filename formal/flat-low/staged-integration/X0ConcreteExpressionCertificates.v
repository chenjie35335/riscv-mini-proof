Require Import ConcreteExpressionClosure ConcreteScalarExpressions ConcreteGroundOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* Generated expressions; circuit membership and history propagation are separate obligations. *)
Ltac solve_x0_ready :=
 first [apply closure_scalar; solve [repeat first [eapply scalar_ready_ref; eassumption | apply scalar_ready_const | apply scalar_ready_unary | apply scalar_ready_binary | apply scalar_ready_cast]]
       | apply closure_mux; solve_x0_ready
       | apply closure_unary; solve_x0_ready
       | apply closure_binary; solve_x0_ready].
Definition x0_concrete_expr_140 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 31 20) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Lemma x0_concrete_ready_140 old :
 (exists g bits, VM.find 123 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_140.
Proof.
 intros [g123 [b123 H123]].
 unfold x0_concrete_expr_140. solve_x0_ready.
Qed.
Definition x0_concrete_expr_141 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 19 15) (@Eref VarOrder.T (@Eid VarOrder.T 123))).
Lemma x0_concrete_ready_141 old :
 (exists g bits, VM.find 123 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_141.
Proof.
 intros [g123 [b123 H123]].
 unfold x0_concrete_expr_141. solve_x0_ready.
Qed.
Definition x0_concrete_expr_282 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 9 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_282 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_282.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_282. solve_x0_ready.
Qed.
Definition x0_concrete_expr_283 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Bleq) (@Eref VarOrder.T (@Eid VarOrder.T 282)) (@Eref VarOrder.T (@Eid VarOrder.T 150))).
Lemma x0_concrete_ready_283 old :
 (exists g bits, VM.find 150 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 282 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_283.
Proof.
 intros [g150 [b150 H150]].
 intros [g282 [b282 H282]].
 unfold x0_concrete_expr_283. solve_x0_ready.
Qed.
Definition x0_concrete_expr_284 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 118)) (@Econst VarOrder.T (Fuint 3) [::false; false; true])).
Lemma x0_concrete_ready_284 old :
 (exists g bits, VM.find 118 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_284.
Proof.
 intros [g118 [b118 H118]].
 unfold x0_concrete_expr_284. solve_x0_ready.
Qed.
Definition x0_concrete_expr_285 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_285 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_285.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_285. solve_x0_ready.
Qed.
Definition x0_concrete_expr_286 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 285)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_286 old :
 (exists g bits, VM.find 285 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_286.
Proof.
 intros [g285 [b285 H285]].
 unfold x0_concrete_expr_286. solve_x0_ready.
Qed.
Definition x0_concrete_expr_287 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 286))).
Lemma x0_concrete_ready_287 old :
 (exists g bits, VM.find 284 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 286 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_287.
Proof.
 intros [g284 [b284 H284]].
 intros [g286 [b286 H286]].
 unfold x0_concrete_expr_287. solve_x0_ready.
Qed.
Definition x0_concrete_expr_288 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_288 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_288.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_288. solve_x0_ready.
Qed.
Definition x0_concrete_expr_289 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 288)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_289 old :
 (exists g bits, VM.find 288 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_289.
Proof.
 intros [g288 [b288 H288]].
 unfold x0_concrete_expr_289. solve_x0_ready.
Qed.
Definition x0_concrete_expr_290 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 287)) (@Eref VarOrder.T (@Eid VarOrder.T 289))).
Lemma x0_concrete_ready_290 old :
 (exists g bits, VM.find 287 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 289 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_290.
Proof.
 intros [g287 [b287 H287]].
 intros [g289 [b289 H289]].
 unfold x0_concrete_expr_290. solve_x0_ready.
Qed.
Definition x0_concrete_expr_291 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_291 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_291.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_291. solve_x0_ready.
Qed.
Definition x0_concrete_expr_292 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 291))).
Lemma x0_concrete_ready_292 old :
 (exists g bits, VM.find 284 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 291 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_292.
Proof.
 intros [g284 [b284 H284]].
 intros [g291 [b291 H291]].
 unfold x0_concrete_expr_292. solve_x0_ready.
Qed.
Definition x0_concrete_expr_293 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 8 8) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_293 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_293.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_293. solve_x0_ready.
Qed.
Definition x0_concrete_expr_294 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 293)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_294 old :
 (exists g bits, VM.find 293 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_294.
Proof.
 intros [g293 [b293 H293]].
 unfold x0_concrete_expr_294. solve_x0_ready.
Qed.
Definition x0_concrete_expr_295 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 292)) (@Eref VarOrder.T (@Eid VarOrder.T 294))).
Lemma x0_concrete_ready_295 old :
 (exists g bits, VM.find 292 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 294 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_295.
Proof.
 intros [g292 [b292 H292]].
 intros [g294 [b294 H294]].
 unfold x0_concrete_expr_295. solve_x0_ready.
Qed.
Definition x0_concrete_expr_301 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_301 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_301.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_301. solve_x0_ready.
Qed.
Definition x0_concrete_expr_302 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 301))).
Lemma x0_concrete_ready_302 old :
 (exists g bits, VM.find 301 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_302.
Proof.
 intros [g301 [b301 H301]].
 unfold x0_concrete_expr_302. solve_x0_ready.
Qed.
Definition x0_concrete_expr_303 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_303 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_303.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_303. solve_x0_ready.
Qed.
Definition x0_concrete_expr_304 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 303))).
Lemma x0_concrete_ready_304 old :
 (exists g bits, VM.find 303 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_304.
Proof.
 intros [g303 [b303 H303]].
 unfold x0_concrete_expr_304. solve_x0_ready.
Qed.
Definition x0_concrete_expr_305 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_305 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_305.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_305. solve_x0_ready.
Qed.
Definition x0_concrete_expr_306 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 305))).
Lemma x0_concrete_ready_306 old :
 (exists g bits, VM.find 305 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_306.
Proof.
 intros [g305 [b305 H305]].
 unfold x0_concrete_expr_306. solve_x0_ready.
Qed.
Definition x0_concrete_expr_307 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_307 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_307.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_307. solve_x0_ready.
Qed.
Definition x0_concrete_expr_308 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 307))).
Lemma x0_concrete_ready_308 old :
 (exists g bits, VM.find 307 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_308.
Proof.
 intros [g307 [b307 H307]].
 unfold x0_concrete_expr_308. solve_x0_ready.
Qed.
Definition x0_concrete_expr_309 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_309 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_309.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_309. solve_x0_ready.
Qed.
Definition x0_concrete_expr_310 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 309))).
Lemma x0_concrete_ready_310 old :
 (exists g bits, VM.find 309 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_310.
Proof.
 intros [g309 [b309 H309]].
 unfold x0_concrete_expr_310. solve_x0_ready.
Qed.
Definition x0_concrete_expr_311 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_311 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_311.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_311. solve_x0_ready.
Qed.
Definition x0_concrete_expr_312 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 311))).
Lemma x0_concrete_ready_312 old :
 (exists g bits, VM.find 311 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_312.
Proof.
 intros [g311 [b311 H311]].
 unfold x0_concrete_expr_312. solve_x0_ready.
Qed.
Definition x0_concrete_expr_313 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_313 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_313.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_313. solve_x0_ready.
Qed.
Definition x0_concrete_expr_314 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 313))).
Lemma x0_concrete_ready_314 old :
 (exists g bits, VM.find 313 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_314.
Proof.
 intros [g313 [b313 H313]].
 unfold x0_concrete_expr_314. solve_x0_ready.
Qed.
Definition x0_concrete_expr_315 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_315 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_315.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_315. solve_x0_ready.
Qed.
Definition x0_concrete_expr_316 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 315))).
Lemma x0_concrete_ready_316 old :
 (exists g bits, VM.find 315 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_316.
Proof.
 intros [g315 [b315 H315]].
 unfold x0_concrete_expr_316. solve_x0_ready.
Qed.
Definition x0_concrete_expr_317 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_317 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_317.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_317. solve_x0_ready.
Qed.
Definition x0_concrete_expr_318 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 317))).
Lemma x0_concrete_ready_318 old :
 (exists g bits, VM.find 317 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_318.
Proof.
 intros [g317 [b317 H317]].
 unfold x0_concrete_expr_318. solve_x0_ready.
Qed.
Definition x0_concrete_expr_319 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_319 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_319.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_319. solve_x0_ready.
Qed.
Definition x0_concrete_expr_320 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 319))).
Lemma x0_concrete_ready_320 old :
 (exists g bits, VM.find 319 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_320.
Proof.
 intros [g319 [b319 H319]].
 unfold x0_concrete_expr_320. solve_x0_ready.
Qed.
Definition x0_concrete_expr_321 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_321 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_321.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_321. solve_x0_ready.
Qed.
Definition x0_concrete_expr_322 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 321))).
Lemma x0_concrete_ready_322 old :
 (exists g bits, VM.find 321 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_322.
Proof.
 intros [g321 [b321 H321]].
 unfold x0_concrete_expr_322. solve_x0_ready.
Qed.
Definition x0_concrete_expr_323 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_323 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_323.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_323. solve_x0_ready.
Qed.
Definition x0_concrete_expr_324 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 323))).
Lemma x0_concrete_ready_324 old :
 (exists g bits, VM.find 323 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_324.
Proof.
 intros [g323 [b323 H323]].
 unfold x0_concrete_expr_324. solve_x0_ready.
Qed.
Definition x0_concrete_expr_325 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_325 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_325.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_325. solve_x0_ready.
Qed.
Definition x0_concrete_expr_326 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 325))).
Lemma x0_concrete_ready_326 old :
 (exists g bits, VM.find 325 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_326.
Proof.
 intros [g325 [b325 H325]].
 unfold x0_concrete_expr_326. solve_x0_ready.
Qed.
Definition x0_concrete_expr_327 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_327 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_327.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_327. solve_x0_ready.
Qed.
Definition x0_concrete_expr_328 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 327))).
Lemma x0_concrete_ready_328 old :
 (exists g bits, VM.find 327 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_328.
Proof.
 intros [g327 [b327 H327]].
 unfold x0_concrete_expr_328. solve_x0_ready.
Qed.
Definition x0_concrete_expr_329 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_329 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_329.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_329. solve_x0_ready.
Qed.
Definition x0_concrete_expr_330 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 12) [::false; false; false; false; true; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 329))).
Lemma x0_concrete_ready_330 old :
 (exists g bits, VM.find 329 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_330.
Proof.
 intros [g329 [b329 H329]].
 unfold x0_concrete_expr_330. solve_x0_ready.
Qed.
Definition x0_concrete_expr_331 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_331 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_331.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_331. solve_x0_ready.
Qed.
Definition x0_concrete_expr_332 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 331))).
Lemma x0_concrete_ready_332 old :
 (exists g bits, VM.find 331 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_332.
Proof.
 intros [g331 [b331 H331]].
 unfold x0_concrete_expr_332. solve_x0_ready.
Qed.
Definition x0_concrete_expr_333 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_333 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_333.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_333. solve_x0_ready.
Qed.
Definition x0_concrete_expr_334 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 333))).
Lemma x0_concrete_ready_334 old :
 (exists g bits, VM.find 333 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_334.
Proof.
 intros [g333 [b333 H333]].
 unfold x0_concrete_expr_334. solve_x0_ready.
Qed.
Definition x0_concrete_expr_335 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_335 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_335.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_335. solve_x0_ready.
Qed.
Definition x0_concrete_expr_336 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 335))).
Lemma x0_concrete_ready_336 old :
 (exists g bits, VM.find 335 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_336.
Proof.
 intros [g335 [b335 H335]].
 unfold x0_concrete_expr_336. solve_x0_ready.
Qed.
Definition x0_concrete_expr_337 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_337 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_337.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_337. solve_x0_ready.
Qed.
Definition x0_concrete_expr_338 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 337))).
Lemma x0_concrete_ready_338 old :
 (exists g bits, VM.find 337 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_338.
Proof.
 intros [g337 [b337 H337]].
 unfold x0_concrete_expr_338. solve_x0_ready.
Qed.
Definition x0_concrete_expr_339 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_339 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_339.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_339. solve_x0_ready.
Qed.
Definition x0_concrete_expr_340 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 339))).
Lemma x0_concrete_ready_340 old :
 (exists g bits, VM.find 339 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_340.
Proof.
 intros [g339 [b339 H339]].
 unfold x0_concrete_expr_340. solve_x0_ready.
Qed.
Definition x0_concrete_expr_341 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_341 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_341.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_341. solve_x0_ready.
Qed.
Definition x0_concrete_expr_342 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; true; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 341))).
Lemma x0_concrete_ready_342 old :
 (exists g bits, VM.find 341 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_342.
Proof.
 intros [g341 [b341 H341]].
 unfold x0_concrete_expr_342. solve_x0_ready.
Qed.
Definition x0_concrete_expr_343 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_343 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_343.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_343. solve_x0_ready.
Qed.
Definition x0_concrete_expr_344 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 343))).
Lemma x0_concrete_ready_344 old :
 (exists g bits, VM.find 343 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_344.
Proof.
 intros [g343 [b343 H343]].
 unfold x0_concrete_expr_344. solve_x0_ready.
Qed.
Definition x0_concrete_expr_345 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_345 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_345.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_345. solve_x0_ready.
Qed.
Definition x0_concrete_expr_346 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; false; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 345))).
Lemma x0_concrete_ready_346 old :
 (exists g bits, VM.find 345 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_346.
Proof.
 intros [g345 [b345 H345]].
 unfold x0_concrete_expr_346. solve_x0_ready.
Qed.
Definition x0_concrete_expr_347 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_347 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_347.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_347. solve_x0_ready.
Qed.
Definition x0_concrete_expr_348 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 347))).
Lemma x0_concrete_ready_348 old :
 (exists g bits, VM.find 347 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_348.
Proof.
 intros [g347 [b347 H347]].
 unfold x0_concrete_expr_348. solve_x0_ready.
Qed.
Definition x0_concrete_expr_349 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_349 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_349.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_349. solve_x0_ready.
Qed.
Definition x0_concrete_expr_350 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::true; true; false; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 349))).
Lemma x0_concrete_ready_350 old :
 (exists g bits, VM.find 349 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_350.
Proof.
 intros [g349 [b349 H349]].
 unfold x0_concrete_expr_350. solve_x0_ready.
Qed.
Definition x0_concrete_expr_351 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_351 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_351.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_351. solve_x0_ready.
Qed.
Definition x0_concrete_expr_352 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; true; false; false; false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 351))).
Lemma x0_concrete_ready_352 old :
 (exists g bits, VM.find 351 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_352.
Proof.
 intros [g351 [b351 H351]].
 unfold x0_concrete_expr_352. solve_x0_ready.
Qed.
Definition x0_concrete_expr_353 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_353 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_353.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_353. solve_x0_ready.
Qed.
Definition x0_concrete_expr_354 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::false; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 353))).
Lemma x0_concrete_ready_354 old :
 (exists g bits, VM.find 353 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_354.
Proof.
 intros [g353 [b353 H353]].
 unfold x0_concrete_expr_354. solve_x0_ready.
Qed.
Definition x0_concrete_expr_355 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_355 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_355.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_355. solve_x0_ready.
Qed.
Definition x0_concrete_expr_356 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 11) [::true; false; false; false; false; false; false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 355))).
Lemma x0_concrete_ready_356 old :
 (exists g bits, VM.find 355 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_356.
Proof.
 intros [g355 [b355 H355]].
 unfold x0_concrete_expr_356. solve_x0_ready.
Qed.
Definition x0_concrete_expr_357 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; true; true; true; true; true; true; true; true; true; true; true])).
Lemma x0_concrete_ready_357 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_357.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_357. solve_x0_ready.
Qed.
Definition x0_concrete_expr_358 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 10) [::false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 357))).
Lemma x0_concrete_ready_358 old :
 (exists g bits, VM.find 357 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_358.
Proof.
 intros [g357 [b357 H357]].
 unfold x0_concrete_expr_358. solve_x0_ready.
Qed.
Definition x0_concrete_expr_359 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 302)) (@Eref VarOrder.T (@Eid VarOrder.T 304))).
Lemma x0_concrete_ready_359 old :
 (exists g bits, VM.find 302 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 304 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_359.
Proof.
 intros [g302 [b302 H302]].
 intros [g304 [b304 H304]].
 unfold x0_concrete_expr_359. solve_x0_ready.
Qed.
Definition x0_concrete_expr_360 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 359)) (@Eref VarOrder.T (@Eid VarOrder.T 306))).
Lemma x0_concrete_ready_360 old :
 (exists g bits, VM.find 306 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 359 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_360.
Proof.
 intros [g306 [b306 H306]].
 intros [g359 [b359 H359]].
 unfold x0_concrete_expr_360. solve_x0_ready.
Qed.
Definition x0_concrete_expr_361 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 360)) (@Eref VarOrder.T (@Eid VarOrder.T 308))).
Lemma x0_concrete_ready_361 old :
 (exists g bits, VM.find 308 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 360 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_361.
Proof.
 intros [g308 [b308 H308]].
 intros [g360 [b360 H360]].
 unfold x0_concrete_expr_361. solve_x0_ready.
Qed.
Definition x0_concrete_expr_362 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 361)) (@Eref VarOrder.T (@Eid VarOrder.T 310))).
Lemma x0_concrete_ready_362 old :
 (exists g bits, VM.find 310 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 361 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_362.
Proof.
 intros [g310 [b310 H310]].
 intros [g361 [b361 H361]].
 unfold x0_concrete_expr_362. solve_x0_ready.
Qed.
Definition x0_concrete_expr_363 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 362)) (@Eref VarOrder.T (@Eid VarOrder.T 312))).
Lemma x0_concrete_ready_363 old :
 (exists g bits, VM.find 312 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 362 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_363.
Proof.
 intros [g312 [b312 H312]].
 intros [g362 [b362 H362]].
 unfold x0_concrete_expr_363. solve_x0_ready.
Qed.
Definition x0_concrete_expr_364 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 363)) (@Eref VarOrder.T (@Eid VarOrder.T 314))).
Lemma x0_concrete_ready_364 old :
 (exists g bits, VM.find 314 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 363 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_364.
Proof.
 intros [g314 [b314 H314]].
 intros [g363 [b363 H363]].
 unfold x0_concrete_expr_364. solve_x0_ready.
Qed.
Definition x0_concrete_expr_365 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 364)) (@Eref VarOrder.T (@Eid VarOrder.T 316))).
Lemma x0_concrete_ready_365 old :
 (exists g bits, VM.find 316 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 364 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_365.
Proof.
 intros [g316 [b316 H316]].
 intros [g364 [b364 H364]].
 unfold x0_concrete_expr_365. solve_x0_ready.
Qed.
Definition x0_concrete_expr_366 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 365)) (@Eref VarOrder.T (@Eid VarOrder.T 318))).
Lemma x0_concrete_ready_366 old :
 (exists g bits, VM.find 318 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 365 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_366.
Proof.
 intros [g318 [b318 H318]].
 intros [g365 [b365 H365]].
 unfold x0_concrete_expr_366. solve_x0_ready.
Qed.
Definition x0_concrete_expr_367 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 366)) (@Eref VarOrder.T (@Eid VarOrder.T 320))).
Lemma x0_concrete_ready_367 old :
 (exists g bits, VM.find 320 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 366 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_367.
Proof.
 intros [g320 [b320 H320]].
 intros [g366 [b366 H366]].
 unfold x0_concrete_expr_367. solve_x0_ready.
Qed.
Definition x0_concrete_expr_368 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 367)) (@Eref VarOrder.T (@Eid VarOrder.T 322))).
Lemma x0_concrete_ready_368 old :
 (exists g bits, VM.find 322 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 367 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_368.
Proof.
 intros [g322 [b322 H322]].
 intros [g367 [b367 H367]].
 unfold x0_concrete_expr_368. solve_x0_ready.
Qed.
Definition x0_concrete_expr_369 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 368)) (@Eref VarOrder.T (@Eid VarOrder.T 324))).
Lemma x0_concrete_ready_369 old :
 (exists g bits, VM.find 324 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 368 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_369.
Proof.
 intros [g324 [b324 H324]].
 intros [g368 [b368 H368]].
 unfold x0_concrete_expr_369. solve_x0_ready.
Qed.
Definition x0_concrete_expr_370 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 369)) (@Eref VarOrder.T (@Eid VarOrder.T 326))).
Lemma x0_concrete_ready_370 old :
 (exists g bits, VM.find 326 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 369 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_370.
Proof.
 intros [g326 [b326 H326]].
 intros [g369 [b369 H369]].
 unfold x0_concrete_expr_370. solve_x0_ready.
Qed.
Definition x0_concrete_expr_371 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 370)) (@Eref VarOrder.T (@Eid VarOrder.T 328))).
Lemma x0_concrete_ready_371 old :
 (exists g bits, VM.find 328 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 370 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_371.
Proof.
 intros [g328 [b328 H328]].
 intros [g370 [b370 H370]].
 unfold x0_concrete_expr_371. solve_x0_ready.
Qed.
Definition x0_concrete_expr_372 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 371)) (@Eref VarOrder.T (@Eid VarOrder.T 330))).
Lemma x0_concrete_ready_372 old :
 (exists g bits, VM.find 330 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 371 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_372.
Proof.
 intros [g330 [b330 H330]].
 intros [g371 [b371 H371]].
 unfold x0_concrete_expr_372. solve_x0_ready.
Qed.
Definition x0_concrete_expr_373 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 372)) (@Eref VarOrder.T (@Eid VarOrder.T 332))).
Lemma x0_concrete_ready_373 old :
 (exists g bits, VM.find 332 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 372 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_373.
Proof.
 intros [g332 [b332 H332]].
 intros [g372 [b372 H372]].
 unfold x0_concrete_expr_373. solve_x0_ready.
Qed.
Definition x0_concrete_expr_374 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 373)) (@Eref VarOrder.T (@Eid VarOrder.T 334))).
Lemma x0_concrete_ready_374 old :
 (exists g bits, VM.find 334 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 373 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_374.
Proof.
 intros [g334 [b334 H334]].
 intros [g373 [b373 H373]].
 unfold x0_concrete_expr_374. solve_x0_ready.
Qed.
Definition x0_concrete_expr_375 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 374)) (@Eref VarOrder.T (@Eid VarOrder.T 336))).
Lemma x0_concrete_ready_375 old :
 (exists g bits, VM.find 336 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 374 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_375.
Proof.
 intros [g336 [b336 H336]].
 intros [g374 [b374 H374]].
 unfold x0_concrete_expr_375. solve_x0_ready.
Qed.
Definition x0_concrete_expr_376 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 375)) (@Eref VarOrder.T (@Eid VarOrder.T 338))).
Lemma x0_concrete_ready_376 old :
 (exists g bits, VM.find 338 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 375 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_376.
Proof.
 intros [g338 [b338 H338]].
 intros [g375 [b375 H375]].
 unfold x0_concrete_expr_376. solve_x0_ready.
Qed.
Definition x0_concrete_expr_377 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 376)) (@Eref VarOrder.T (@Eid VarOrder.T 340))).
Lemma x0_concrete_ready_377 old :
 (exists g bits, VM.find 340 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 376 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_377.
Proof.
 intros [g340 [b340 H340]].
 intros [g376 [b376 H376]].
 unfold x0_concrete_expr_377. solve_x0_ready.
Qed.
Definition x0_concrete_expr_378 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 377)) (@Eref VarOrder.T (@Eid VarOrder.T 342))).
Lemma x0_concrete_ready_378 old :
 (exists g bits, VM.find 342 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 377 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_378.
Proof.
 intros [g342 [b342 H342]].
 intros [g377 [b377 H377]].
 unfold x0_concrete_expr_378. solve_x0_ready.
Qed.
Definition x0_concrete_expr_379 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 378)) (@Eref VarOrder.T (@Eid VarOrder.T 344))).
Lemma x0_concrete_ready_379 old :
 (exists g bits, VM.find 344 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 378 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_379.
Proof.
 intros [g344 [b344 H344]].
 intros [g378 [b378 H378]].
 unfold x0_concrete_expr_379. solve_x0_ready.
Qed.
Definition x0_concrete_expr_380 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 379)) (@Eref VarOrder.T (@Eid VarOrder.T 346))).
Lemma x0_concrete_ready_380 old :
 (exists g bits, VM.find 346 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 379 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_380.
Proof.
 intros [g346 [b346 H346]].
 intros [g379 [b379 H379]].
 unfold x0_concrete_expr_380. solve_x0_ready.
Qed.
Definition x0_concrete_expr_381 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 380)) (@Eref VarOrder.T (@Eid VarOrder.T 348))).
Lemma x0_concrete_ready_381 old :
 (exists g bits, VM.find 348 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 380 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_381.
Proof.
 intros [g348 [b348 H348]].
 intros [g380 [b380 H380]].
 unfold x0_concrete_expr_381. solve_x0_ready.
Qed.
Definition x0_concrete_expr_382 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 381)) (@Eref VarOrder.T (@Eid VarOrder.T 350))).
Lemma x0_concrete_ready_382 old :
 (exists g bits, VM.find 350 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 381 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_382.
Proof.
 intros [g350 [b350 H350]].
 intros [g381 [b381 H381]].
 unfold x0_concrete_expr_382. solve_x0_ready.
Qed.
Definition x0_concrete_expr_383 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 382)) (@Eref VarOrder.T (@Eid VarOrder.T 352))).
Lemma x0_concrete_ready_383 old :
 (exists g bits, VM.find 352 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 382 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_383.
Proof.
 intros [g352 [b352 H352]].
 intros [g382 [b382 H382]].
 unfold x0_concrete_expr_383. solve_x0_ready.
Qed.
Definition x0_concrete_expr_384 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 383)) (@Eref VarOrder.T (@Eid VarOrder.T 354))).
Lemma x0_concrete_ready_384 old :
 (exists g bits, VM.find 354 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 383 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_384.
Proof.
 intros [g354 [b354 H354]].
 intros [g383 [b383 H383]].
 unfold x0_concrete_expr_384. solve_x0_ready.
Qed.
Definition x0_concrete_expr_385 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 384)) (@Eref VarOrder.T (@Eid VarOrder.T 356))).
Lemma x0_concrete_ready_385 old :
 (exists g bits, VM.find 356 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 384 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_385.
Proof.
 intros [g356 [b356 H356]].
 intros [g384 [b384 H384]].
 unfold x0_concrete_expr_385. solve_x0_ready.
Qed.
Definition x0_concrete_expr_386 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 385)) (@Eref VarOrder.T (@Eid VarOrder.T 358))).
Lemma x0_concrete_ready_386 old :
 (exists g bits, VM.find 358 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 385 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_386.
Proof.
 intros [g358 [b358 H358]].
 intros [g385 [b385 H385]].
 unfold x0_concrete_expr_386. solve_x0_ready.
Qed.
Definition x0_concrete_expr_387 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 10) (@Eref VarOrder.T (@Eid VarOrder.T 140))).
Lemma x0_concrete_ready_387 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_387.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_387. solve_x0_ready.
Qed.
Definition x0_concrete_expr_388 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uandr (@Eref VarOrder.T (@Eid VarOrder.T 387))).
Lemma x0_concrete_ready_388 old :
 (exists g bits, VM.find 387 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_388.
Proof.
 intros [g387 [b387 H387]].
 unfold x0_concrete_expr_388. solve_x0_ready.
Qed.
Definition x0_concrete_expr_389 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::true; false; false; false; false; false; false; false; true; true; false; false])).
Lemma x0_concrete_ready_389 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_389.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_389. solve_x0_ready.
Qed.
Definition x0_concrete_expr_390 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 388)) (@Eref VarOrder.T (@Eid VarOrder.T 389))).
Lemma x0_concrete_ready_390 old :
 (exists g bits, VM.find 388 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 389 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_390.
Proof.
 intros [g388 [b388 H388]].
 intros [g389 [b389 H389]].
 unfold x0_concrete_expr_390. solve_x0_ready.
Qed.
Definition x0_concrete_expr_391 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 140)) (@Econst VarOrder.T (Fuint 12) [::false; true; false; false; false; false; false; false; true; true; false; false])).
Lemma x0_concrete_ready_391 old :
 (exists g bits, VM.find 140 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_391.
Proof.
 intros [g140 [b140 H140]].
 unfold x0_concrete_expr_391. solve_x0_ready.
Qed.
Definition x0_concrete_expr_392 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 390)) (@Eref VarOrder.T (@Eid VarOrder.T 391))).
Lemma x0_concrete_ready_392 old :
 (exists g bits, VM.find 390 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 391 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_392.
Proof.
 intros [g390 [b390 H390]].
 intros [g391 [b391 H391]].
 unfold x0_concrete_expr_392. solve_x0_ready.
Qed.
Definition x0_concrete_expr_393 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 118)) (@Econst VarOrder.T (Fuint 3) [::true; false; false])).
Lemma x0_concrete_ready_393 old :
 (exists g bits, VM.find 118 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_393.
Proof.
 intros [g118 [b118 H118]].
 unfold x0_concrete_expr_393. solve_x0_ready.
Qed.
Definition x0_concrete_expr_394 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma x0_concrete_ready_394 old :
 (exists g bits, VM.find 118 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_394.
Proof.
 intros [g118 [b118 H118]].
 unfold x0_concrete_expr_394. solve_x0_ready.
Qed.
Definition x0_concrete_expr_395 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 141))).
Lemma x0_concrete_ready_395 old :
 (exists g bits, VM.find 141 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_395.
Proof.
 intros [g141 [b141 H141]].
 unfold x0_concrete_expr_395. solve_x0_ready.
Qed.
Definition x0_concrete_expr_396 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 394)) (@Eref VarOrder.T (@Eid VarOrder.T 395))).
Lemma x0_concrete_ready_396 old :
 (exists g bits, VM.find 394 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 395 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_396.
Proof.
 intros [g394 [b394 H394]].
 intros [g395 [b395 H395]].
 unfold x0_concrete_expr_396. solve_x0_ready.
Qed.
Definition x0_concrete_expr_397 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 393)) (@Eref VarOrder.T (@Eid VarOrder.T 396))).
Lemma x0_concrete_ready_397 old :
 (exists g bits, VM.find 393 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 396 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_397.
Proof.
 intros [g393 [b393 H393]].
 intros [g396 [b396 H396]].
 unfold x0_concrete_expr_397. solve_x0_ready.
Qed.
Definition x0_concrete_expr_407 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 1) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_407 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_407.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_407. solve_x0_ready.
Qed.
Definition x0_concrete_expr_408 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 127)) (@Eref VarOrder.T (@Eid VarOrder.T 407))).
Lemma x0_concrete_ready_408 old :
 (exists g bits, VM.find 127 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 407 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_408.
Proof.
 intros [g127 [b127 H127]].
 intros [g407 [b407 H407]].
 unfold x0_concrete_expr_408. solve_x0_ready.
Qed.
Definition x0_concrete_expr_409 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_409 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_409.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_409. solve_x0_ready.
Qed.
Definition x0_concrete_expr_410 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 409))).
Lemma x0_concrete_ready_410 old :
 (exists g bits, VM.find 409 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_410.
Proof.
 intros [g409 [b409 H409]].
 unfold x0_concrete_expr_410. solve_x0_ready.
Qed.
Definition x0_concrete_expr_411 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_411 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_411.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_411. solve_x0_ready.
Qed.
Definition x0_concrete_expr_412 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_412 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_412.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_412. solve_x0_ready.
Qed.
Definition x0_concrete_expr_413 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; false]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma x0_concrete_ready_413 old :
 (exists g bits, VM.find 126 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_413.
Proof.
 intros [g126 [b126 H126]].
 unfold x0_concrete_expr_413. solve_x0_ready.
Qed.
Definition x0_concrete_expr_414 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 413)) (@Eref VarOrder.T (@Eid VarOrder.T 410)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_414 old :
 (exists g bits, VM.find 410 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 413 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_414.
Proof.
 intros [g410 [b410 H410]].
 intros [g413 [b413 H413]].
 unfold x0_concrete_expr_414. solve_x0_ready.
Qed.
Definition x0_concrete_expr_415 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma x0_concrete_ready_415 old :
 (exists g bits, VM.find 126 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_415.
Proof.
 intros [g126 [b126 H126]].
 unfold x0_concrete_expr_415. solve_x0_ready.
Qed.
Definition x0_concrete_expr_416 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 415)) (@Eref VarOrder.T (@Eid VarOrder.T 411)) (@Eref VarOrder.T (@Eid VarOrder.T 414))).
Lemma x0_concrete_ready_416 old :
 (exists g bits, VM.find 411 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 414 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 415 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_416.
Proof.
 intros [g411 [b411 H411]].
 intros [g414 [b414 H414]].
 intros [g415 [b415 H415]].
 unfold x0_concrete_expr_416. solve_x0_ready.
Qed.
Definition x0_concrete_expr_417 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 126))).
Lemma x0_concrete_ready_417 old :
 (exists g bits, VM.find 126 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_417.
Proof.
 intros [g126 [b126 H126]].
 unfold x0_concrete_expr_417. solve_x0_ready.
Qed.
Definition x0_concrete_expr_418 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 417)) (@Eref VarOrder.T (@Eid VarOrder.T 412)) (@Eref VarOrder.T (@Eid VarOrder.T 416))).
Lemma x0_concrete_ready_418 old :
 (exists g bits, VM.find 412 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 416 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 417 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_418.
Proof.
 intros [g412 [b412 H412]].
 intros [g416 [b416 H416]].
 intros [g417 [b417 H417]].
 unfold x0_concrete_expr_418. solve_x0_ready.
Qed.
Definition x0_concrete_expr_419 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_419 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_419.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_419. solve_x0_ready.
Qed.
Definition x0_concrete_expr_420 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 419))).
Lemma x0_concrete_ready_420 old :
 (exists g bits, VM.find 419 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_420.
Proof.
 intros [g419 [b419 H419]].
 unfold x0_concrete_expr_420. solve_x0_ready.
Qed.
Definition x0_concrete_expr_421 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 122))).
Lemma x0_concrete_ready_421 old :
 (exists g bits, VM.find 122 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_421.
Proof.
 intros [g122 [b122 H122]].
 unfold x0_concrete_expr_421. solve_x0_ready.
Qed.
Definition x0_concrete_expr_422 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; false]) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Lemma x0_concrete_ready_422 old :
 (exists g bits, VM.find 125 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_422.
Proof.
 intros [g125 [b125 H125]].
 unfold x0_concrete_expr_422. solve_x0_ready.
Qed.
Definition x0_concrete_expr_423 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 422)) (@Eref VarOrder.T (@Eid VarOrder.T 420)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_423 old :
 (exists g bits, VM.find 420 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 422 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_423.
Proof.
 intros [g420 [b420 H420]].
 intros [g422 [b422 H422]].
 unfold x0_concrete_expr_423. solve_x0_ready.
Qed.
Definition x0_concrete_expr_424 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 125))).
Lemma x0_concrete_ready_424 old :
 (exists g bits, VM.find 125 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_424.
Proof.
 intros [g125 [b125 H125]].
 unfold x0_concrete_expr_424. solve_x0_ready.
Qed.
Definition x0_concrete_expr_425 : hfexpr VarOrder.T := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 424)) (@Eref VarOrder.T (@Eid VarOrder.T 421)) (@Eref VarOrder.T (@Eid VarOrder.T 423))).
Lemma x0_concrete_ready_425 old :
 (exists g bits, VM.find 421 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 423 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 424 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_425.
Proof.
 intros [g421 [b421 H421]].
 intros [g423 [b423 H423]].
 intros [g424 [b424 H424]].
 unfold x0_concrete_expr_425. solve_x0_ready.
Qed.
Definition x0_concrete_expr_426 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 124)) (@Eref VarOrder.T (@Eid VarOrder.T 408))).
Lemma x0_concrete_ready_426 old :
 (exists g bits, VM.find 124 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 408 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_426.
Proof.
 intros [g124 [b124 H124]].
 intros [g408 [b408 H408]].
 unfold x0_concrete_expr_426. solve_x0_ready.
Qed.
Definition x0_concrete_expr_427 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 426)) (@Eref VarOrder.T (@Eid VarOrder.T 418))).
Lemma x0_concrete_ready_427 old :
 (exists g bits, VM.find 418 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 426 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_427.
Proof.
 intros [g418 [b418 H418]].
 intros [g426 [b426 H426]].
 unfold x0_concrete_expr_427. solve_x0_ready.
Qed.
Definition x0_concrete_expr_428 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 427)) (@Eref VarOrder.T (@Eid VarOrder.T 425))).
Lemma x0_concrete_ready_428 old :
 (exists g bits, VM.find 425 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 427 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_428.
Proof.
 intros [g425 [b425 H425]].
 intros [g427 [b427 H427]].
 unfold x0_concrete_expr_428. solve_x0_ready.
Qed.
Definition x0_concrete_expr_429 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 1 0) (@Eref VarOrder.T (@Eid VarOrder.T 118))).
Lemma x0_concrete_ready_429 old :
 (exists g bits, VM.find 118 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_429.
Proof.
 intros [g118 [b118 H118]].
 unfold x0_concrete_expr_429. solve_x0_ready.
Qed.
Definition x0_concrete_expr_430 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T (@Eid VarOrder.T 429))).
Lemma x0_concrete_ready_430 old :
 (exists g bits, VM.find 429 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_430.
Proof.
 intros [g429 [b429 H429]].
 unfold x0_concrete_expr_430. solve_x0_ready.
Qed.
Definition x0_concrete_expr_431 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 386)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_431 old :
 (exists g bits, VM.find 386 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_431.
Proof.
 intros [g386 [b386 H386]].
 unfold x0_concrete_expr_431. solve_x0_ready.
Qed.
Definition x0_concrete_expr_432 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 283)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_432 old :
 (exists g bits, VM.find 283 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_432.
Proof.
 intros [g283 [b283 H283]].
 unfold x0_concrete_expr_432. solve_x0_ready.
Qed.
Definition x0_concrete_expr_433 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 431)) (@Eref VarOrder.T (@Eid VarOrder.T 432))).
Lemma x0_concrete_ready_433 old :
 (exists g bits, VM.find 431 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 432 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_433.
Proof.
 intros [g431 [b431 H431]].
 intros [g432 [b432 H432]].
 unfold x0_concrete_expr_433. solve_x0_ready.
Qed.
Definition x0_concrete_expr_434 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 430)) (@Eref VarOrder.T (@Eid VarOrder.T 433))).
Lemma x0_concrete_ready_434 old :
 (exists g bits, VM.find 430 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 433 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_434.
Proof.
 intros [g430 [b430 H430]].
 intros [g433 [b433 H433]].
 unfold x0_concrete_expr_434. solve_x0_ready.
Qed.
Definition x0_concrete_expr_435 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 428)) (@Eref VarOrder.T (@Eid VarOrder.T 434))).
Lemma x0_concrete_ready_435 old :
 (exists g bits, VM.find 428 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 434 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_435.
Proof.
 intros [g428 [b428 H428]].
 intros [g434 [b434 H434]].
 unfold x0_concrete_expr_435. solve_x0_ready.
Qed.
Definition x0_concrete_expr_436 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 397)) (@Eref VarOrder.T (@Eid VarOrder.T 392))).
Lemma x0_concrete_ready_436 old :
 (exists g bits, VM.find 392 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 397 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_436.
Proof.
 intros [g392 [b392 H392]].
 intros [g397 [b397 H397]].
 unfold x0_concrete_expr_436. solve_x0_ready.
Qed.
Definition x0_concrete_expr_437 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 435)) (@Eref VarOrder.T (@Eid VarOrder.T 436))).
Lemma x0_concrete_ready_437 old :
 (exists g bits, VM.find 435 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 436 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_437.
Proof.
 intros [g435 [b435 H435]].
 intros [g436 [b436 H436]].
 unfold x0_concrete_expr_437. solve_x0_ready.
Qed.
Definition x0_concrete_expr_438 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 283)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_438 old :
 (exists g bits, VM.find 283 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_438.
Proof.
 intros [g283 [b283 H283]].
 unfold x0_concrete_expr_438. solve_x0_ready.
Qed.
Definition x0_concrete_expr_439 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 284)) (@Eref VarOrder.T (@Eid VarOrder.T 438))).
Lemma x0_concrete_ready_439 old :
 (exists g bits, VM.find 284 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 438 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_439.
Proof.
 intros [g284 [b284 H284]].
 intros [g438 [b438 H438]].
 unfold x0_concrete_expr_439. solve_x0_ready.
Qed.
Definition x0_concrete_expr_440 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 437)) (@Eref VarOrder.T (@Eid VarOrder.T 439))).
Lemma x0_concrete_ready_440 old :
 (exists g bits, VM.find 437 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 439 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_440.
Proof.
 intros [g437 [b437 H437]].
 intros [g439 [b439 H439]].
 unfold x0_concrete_expr_440. solve_x0_ready.
Qed.
Definition x0_concrete_expr_441 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 440)) (@Eref VarOrder.T (@Eid VarOrder.T 290))).
Lemma x0_concrete_ready_441 old :
 (exists g bits, VM.find 290 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 440 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_441.
Proof.
 intros [g290 [b290 H290]].
 intros [g440 [b440 H440]].
 unfold x0_concrete_expr_441. solve_x0_ready.
Qed.
Definition x0_concrete_expr_442 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 441)) (@Eref VarOrder.T (@Eid VarOrder.T 295))).
Lemma x0_concrete_ready_442 old :
 (exists g bits, VM.find 295 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 441 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_442.
Proof.
 intros [g295 [b295 H295]].
 intros [g441 [b441 H441]].
 unfold x0_concrete_expr_442. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7763 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 74)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_7763 old :
 (exists g bits, VM.find 74 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7763.
Proof.
 intros [g74 [b74 H74]].
 unfold x0_concrete_expr_7763. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7764 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 81)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_7764 old :
 (exists g bits, VM.find 81 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7764.
Proof.
 intros [g81 [b81 H81]].
 unfold x0_concrete_expr_7764. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7765 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 7763)) (@Eref VarOrder.T (@Eid VarOrder.T 7764))).
Lemma x0_concrete_ready_7765 old :
 (exists g bits, VM.find 7763 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 7764 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7765.
Proof.
 intros [g7763 [b7763 H7763]].
 intros [g7764 [b7764 H7764]].
 unfold x0_concrete_expr_7765. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7805 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 11 7) (@Eref VarOrder.T (@Eid VarOrder.T 7750))).
Lemma x0_concrete_ready_7805 old :
 (exists g bits, VM.find 7750 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7805.
Proof.
 intros [g7750 [b7750 H7750]].
 unfold x0_concrete_expr_7805. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7938 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 7765)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_7938 old :
 (exists g bits, VM.find 7765 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7938.
Proof.
 intros [g7765 [b7765 H7765]].
 unfold x0_concrete_expr_7938. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7939 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7757)) (@Eref VarOrder.T (@Eid VarOrder.T 7938))).
Lemma x0_concrete_ready_7939 old :
 (exists g bits, VM.find 7757 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 7938 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7939.
Proof.
 intros [g7757 [b7757 H7757]].
 intros [g7938 [b7938 H7938]].
 unfold x0_concrete_expr_7939. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7940 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 128)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_7940 old :
 (exists g bits, VM.find 128 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7940.
Proof.
 intros [g128 [b128 H128]].
 unfold x0_concrete_expr_7940. solve_x0_ready.
Qed.
Definition x0_concrete_expr_7941 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 7939)) (@Eref VarOrder.T (@Eid VarOrder.T 7940))).
Lemma x0_concrete_ready_7941 old :
 (exists g bits, VM.find 7939 old = Some (Gval g bits)) ->
 (exists g bits, VM.find 7940 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_7941.
Proof.
 intros [g7939 [b7939 H7939]].
 intros [g7940 [b7940 H7940]].
 unfold x0_concrete_expr_7941. solve_x0_ready.
Qed.
Definition x0_concrete_expr_9215 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Lemma x0_concrete_ready_9215 old :
 (exists g bits, VM.find 1 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_9215.
Proof.
 intros [g1 [b1 H1]].
 unfold x0_concrete_expr_9215. solve_x0_ready.
Qed.
Definition x0_concrete_expr_9216 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9215)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_9216 old :
 (exists g bits, VM.find 9215 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_9216.
Proof.
 intros [g9215 [b9215 H9215]].
 unfold x0_concrete_expr_9216. solve_x0_ready.
Qed.
Definition x0_concrete_expr_9217 : hfexpr VarOrder.T := (@Eprim_unop VarOrder.T (Uextr 0 0) (@Eref VarOrder.T (@Eid VarOrder.T 1))).
Lemma x0_concrete_ready_9217 old :
 (exists g bits, VM.find 1 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_9217.
Proof.
 intros [g1 [b1 H1]].
 unfold x0_concrete_expr_9217. solve_x0_ready.
Qed.
Definition x0_concrete_expr_9218 : hfexpr VarOrder.T := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 9217)) (@Econst VarOrder.T (Fuint 1) [::false])).
Lemma x0_concrete_ready_9218 old :
 (exists g bits, VM.find 9217 old = Some (Gval g bits)) ->
 concrete_expression_ready old x0_concrete_expr_9218.
Proof.
 intros [g9217 [b9217 H9217]].
 unfold x0_concrete_expr_9218. solve_x0_ready.
Qed.
Print Assumptions x0_concrete_ready_9218.
