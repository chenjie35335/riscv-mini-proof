Require Import X0ConcreteExpressionCertificates ConcreteUIntOperations ConcreteUIntScalarExpressions.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_uint_ready :=
 repeat first [eapply uint_ready_ref; eassumption | apply uint_ready_const
 | apply uint_ready_unary; [reflexivity|] | apply uint_ready_binary].
Lemma x0_uint_result_140 invalid site mm old result :
 (exists width bits, VM.find 123 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_140 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w123 [b123 H123]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_140. solve_uint_ready.
Qed.
Lemma x0_uint_result_141 invalid site mm old result :
 (exists width bits, VM.find 123 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_141 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w123 [b123 H123]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_141. solve_uint_ready.
Qed.
Lemma x0_uint_result_282 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_282 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_282. solve_uint_ready.
Qed.
Lemma x0_uint_result_283 invalid site mm old result :
 (exists width bits, VM.find 150 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 282 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_283 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w150 [b150 H150]].
 intros [w282 [b282 H282]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_283. solve_uint_ready.
Qed.
Lemma x0_uint_result_284 invalid site mm old result :
 (exists width bits, VM.find 118 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_284 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w118 [b118 H118]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_284. solve_uint_ready.
Qed.
Lemma x0_uint_result_285 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_285 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_285. solve_uint_ready.
Qed.
Lemma x0_uint_result_286 invalid site mm old result :
 (exists width bits, VM.find 285 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_286 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w285 [b285 H285]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_286. solve_uint_ready.
Qed.
Lemma x0_uint_result_287 invalid site mm old result :
 (exists width bits, VM.find 284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 286 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_287 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w284 [b284 H284]].
 intros [w286 [b286 H286]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_287. solve_uint_ready.
Qed.
Lemma x0_uint_result_288 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_288 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_288. solve_uint_ready.
Qed.
Lemma x0_uint_result_289 invalid site mm old result :
 (exists width bits, VM.find 288 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_289 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w288 [b288 H288]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_289. solve_uint_ready.
Qed.
Lemma x0_uint_result_290 invalid site mm old result :
 (exists width bits, VM.find 287 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 289 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_290 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w287 [b287 H287]].
 intros [w289 [b289 H289]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_290. solve_uint_ready.
Qed.
Lemma x0_uint_result_291 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_291 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_291. solve_uint_ready.
Qed.
Lemma x0_uint_result_292 invalid site mm old result :
 (exists width bits, VM.find 284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 291 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_292 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w284 [b284 H284]].
 intros [w291 [b291 H291]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_292. solve_uint_ready.
Qed.
Lemma x0_uint_result_293 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_293 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_293. solve_uint_ready.
Qed.
Lemma x0_uint_result_294 invalid site mm old result :
 (exists width bits, VM.find 293 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_294 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w293 [b293 H293]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_294. solve_uint_ready.
Qed.
Lemma x0_uint_result_295 invalid site mm old result :
 (exists width bits, VM.find 292 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 294 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_295 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w292 [b292 H292]].
 intros [w294 [b294 H294]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_295. solve_uint_ready.
Qed.
Lemma x0_uint_result_301 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_301 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_301. solve_uint_ready.
Qed.
Lemma x0_uint_result_302 invalid site mm old result :
 (exists width bits, VM.find 301 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_302 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w301 [b301 H301]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_302. solve_uint_ready.
Qed.
Lemma x0_uint_result_303 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_303 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_303. solve_uint_ready.
Qed.
Lemma x0_uint_result_304 invalid site mm old result :
 (exists width bits, VM.find 303 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_304 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w303 [b303 H303]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_304. solve_uint_ready.
Qed.
Lemma x0_uint_result_305 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_305 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_305. solve_uint_ready.
Qed.
Lemma x0_uint_result_306 invalid site mm old result :
 (exists width bits, VM.find 305 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_306 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w305 [b305 H305]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_306. solve_uint_ready.
Qed.
Lemma x0_uint_result_307 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_307 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_307. solve_uint_ready.
Qed.
Lemma x0_uint_result_308 invalid site mm old result :
 (exists width bits, VM.find 307 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_308 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w307 [b307 H307]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_308. solve_uint_ready.
Qed.
Lemma x0_uint_result_309 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_309 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_309. solve_uint_ready.
Qed.
Lemma x0_uint_result_310 invalid site mm old result :
 (exists width bits, VM.find 309 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_310 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w309 [b309 H309]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_310. solve_uint_ready.
Qed.
Lemma x0_uint_result_311 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_311 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_311. solve_uint_ready.
Qed.
Lemma x0_uint_result_312 invalid site mm old result :
 (exists width bits, VM.find 311 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_312 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w311 [b311 H311]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_312. solve_uint_ready.
Qed.
Lemma x0_uint_result_313 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_313 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_313. solve_uint_ready.
Qed.
Lemma x0_uint_result_314 invalid site mm old result :
 (exists width bits, VM.find 313 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_314 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w313 [b313 H313]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_314. solve_uint_ready.
Qed.
Lemma x0_uint_result_315 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_315 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_315. solve_uint_ready.
Qed.
Lemma x0_uint_result_316 invalid site mm old result :
 (exists width bits, VM.find 315 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_316 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w315 [b315 H315]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_316. solve_uint_ready.
Qed.
Lemma x0_uint_result_317 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_317 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_317. solve_uint_ready.
Qed.
Lemma x0_uint_result_318 invalid site mm old result :
 (exists width bits, VM.find 317 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_318 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w317 [b317 H317]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_318. solve_uint_ready.
Qed.
Lemma x0_uint_result_319 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_319 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_319. solve_uint_ready.
Qed.
Lemma x0_uint_result_320 invalid site mm old result :
 (exists width bits, VM.find 319 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_320 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w319 [b319 H319]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_320. solve_uint_ready.
Qed.
Lemma x0_uint_result_321 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_321 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_321. solve_uint_ready.
Qed.
Lemma x0_uint_result_322 invalid site mm old result :
 (exists width bits, VM.find 321 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_322 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w321 [b321 H321]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_322. solve_uint_ready.
Qed.
Lemma x0_uint_result_323 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_323 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_323. solve_uint_ready.
Qed.
Lemma x0_uint_result_324 invalid site mm old result :
 (exists width bits, VM.find 323 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_324 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w323 [b323 H323]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_324. solve_uint_ready.
Qed.
Lemma x0_uint_result_325 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_325 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_325. solve_uint_ready.
Qed.
Lemma x0_uint_result_326 invalid site mm old result :
 (exists width bits, VM.find 325 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_326 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w325 [b325 H325]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_326. solve_uint_ready.
Qed.
Lemma x0_uint_result_327 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_327 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_327. solve_uint_ready.
Qed.
Lemma x0_uint_result_328 invalid site mm old result :
 (exists width bits, VM.find 327 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_328 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w327 [b327 H327]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_328. solve_uint_ready.
Qed.
Lemma x0_uint_result_329 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_329 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_329. solve_uint_ready.
Qed.
Lemma x0_uint_result_330 invalid site mm old result :
 (exists width bits, VM.find 329 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_330 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w329 [b329 H329]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_330. solve_uint_ready.
Qed.
Lemma x0_uint_result_331 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_331 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_331. solve_uint_ready.
Qed.
Lemma x0_uint_result_332 invalid site mm old result :
 (exists width bits, VM.find 331 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_332 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w331 [b331 H331]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_332. solve_uint_ready.
Qed.
Lemma x0_uint_result_333 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_333 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_333. solve_uint_ready.
Qed.
Lemma x0_uint_result_334 invalid site mm old result :
 (exists width bits, VM.find 333 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_334 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w333 [b333 H333]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_334. solve_uint_ready.
Qed.
Lemma x0_uint_result_335 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_335 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_335. solve_uint_ready.
Qed.
Lemma x0_uint_result_336 invalid site mm old result :
 (exists width bits, VM.find 335 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_336 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w335 [b335 H335]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_336. solve_uint_ready.
Qed.
Lemma x0_uint_result_337 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_337 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_337. solve_uint_ready.
Qed.
Lemma x0_uint_result_338 invalid site mm old result :
 (exists width bits, VM.find 337 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_338 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w337 [b337 H337]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_338. solve_uint_ready.
Qed.
Lemma x0_uint_result_339 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_339 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_339. solve_uint_ready.
Qed.
Lemma x0_uint_result_340 invalid site mm old result :
 (exists width bits, VM.find 339 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_340 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w339 [b339 H339]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_340. solve_uint_ready.
Qed.
Lemma x0_uint_result_341 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_341 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_341. solve_uint_ready.
Qed.
Lemma x0_uint_result_342 invalid site mm old result :
 (exists width bits, VM.find 341 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_342 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w341 [b341 H341]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_342. solve_uint_ready.
Qed.
Lemma x0_uint_result_343 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_343 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_343. solve_uint_ready.
Qed.
Lemma x0_uint_result_344 invalid site mm old result :
 (exists width bits, VM.find 343 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_344 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w343 [b343 H343]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_344. solve_uint_ready.
Qed.
Lemma x0_uint_result_345 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_345 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_345. solve_uint_ready.
Qed.
Lemma x0_uint_result_346 invalid site mm old result :
 (exists width bits, VM.find 345 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_346 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w345 [b345 H345]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_346. solve_uint_ready.
Qed.
Lemma x0_uint_result_347 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_347 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_347. solve_uint_ready.
Qed.
Lemma x0_uint_result_348 invalid site mm old result :
 (exists width bits, VM.find 347 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_348 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w347 [b347 H347]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_348. solve_uint_ready.
Qed.
Lemma x0_uint_result_349 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_349 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_349. solve_uint_ready.
Qed.
Lemma x0_uint_result_350 invalid site mm old result :
 (exists width bits, VM.find 349 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_350 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w349 [b349 H349]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_350. solve_uint_ready.
Qed.
Lemma x0_uint_result_351 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_351 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_351. solve_uint_ready.
Qed.
Lemma x0_uint_result_352 invalid site mm old result :
 (exists width bits, VM.find 351 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_352 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w351 [b351 H351]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_352. solve_uint_ready.
Qed.
Lemma x0_uint_result_353 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_353 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_353. solve_uint_ready.
Qed.
Lemma x0_uint_result_354 invalid site mm old result :
 (exists width bits, VM.find 353 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_354 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w353 [b353 H353]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_354. solve_uint_ready.
Qed.
Lemma x0_uint_result_355 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_355 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_355. solve_uint_ready.
Qed.
Lemma x0_uint_result_356 invalid site mm old result :
 (exists width bits, VM.find 355 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_356 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w355 [b355 H355]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_356. solve_uint_ready.
Qed.
Lemma x0_uint_result_357 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_357 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_357. solve_uint_ready.
Qed.
Lemma x0_uint_result_358 invalid site mm old result :
 (exists width bits, VM.find 357 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_358 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w357 [b357 H357]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_358. solve_uint_ready.
Qed.
Lemma x0_uint_result_359 invalid site mm old result :
 (exists width bits, VM.find 302 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 304 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_359 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w302 [b302 H302]].
 intros [w304 [b304 H304]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_359. solve_uint_ready.
Qed.
Lemma x0_uint_result_360 invalid site mm old result :
 (exists width bits, VM.find 306 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 359 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_360 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w306 [b306 H306]].
 intros [w359 [b359 H359]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_360. solve_uint_ready.
Qed.
Lemma x0_uint_result_361 invalid site mm old result :
 (exists width bits, VM.find 308 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 360 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_361 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w308 [b308 H308]].
 intros [w360 [b360 H360]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_361. solve_uint_ready.
Qed.
Lemma x0_uint_result_362 invalid site mm old result :
 (exists width bits, VM.find 310 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 361 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_362 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w310 [b310 H310]].
 intros [w361 [b361 H361]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_362. solve_uint_ready.
Qed.
Lemma x0_uint_result_363 invalid site mm old result :
 (exists width bits, VM.find 312 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 362 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_363 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w312 [b312 H312]].
 intros [w362 [b362 H362]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_363. solve_uint_ready.
Qed.
Lemma x0_uint_result_364 invalid site mm old result :
 (exists width bits, VM.find 314 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 363 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_364 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w314 [b314 H314]].
 intros [w363 [b363 H363]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_364. solve_uint_ready.
Qed.
Lemma x0_uint_result_365 invalid site mm old result :
 (exists width bits, VM.find 316 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 364 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_365 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w316 [b316 H316]].
 intros [w364 [b364 H364]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_365. solve_uint_ready.
Qed.
Lemma x0_uint_result_366 invalid site mm old result :
 (exists width bits, VM.find 318 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 365 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_366 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w318 [b318 H318]].
 intros [w365 [b365 H365]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_366. solve_uint_ready.
Qed.
Lemma x0_uint_result_367 invalid site mm old result :
 (exists width bits, VM.find 320 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 366 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_367 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w320 [b320 H320]].
 intros [w366 [b366 H366]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_367. solve_uint_ready.
Qed.
Lemma x0_uint_result_368 invalid site mm old result :
 (exists width bits, VM.find 322 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 367 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_368 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w322 [b322 H322]].
 intros [w367 [b367 H367]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_368. solve_uint_ready.
Qed.
Lemma x0_uint_result_369 invalid site mm old result :
 (exists width bits, VM.find 324 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 368 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_369 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w324 [b324 H324]].
 intros [w368 [b368 H368]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_369. solve_uint_ready.
Qed.
Lemma x0_uint_result_370 invalid site mm old result :
 (exists width bits, VM.find 326 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 369 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_370 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w326 [b326 H326]].
 intros [w369 [b369 H369]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_370. solve_uint_ready.
Qed.
Lemma x0_uint_result_371 invalid site mm old result :
 (exists width bits, VM.find 328 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 370 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_371 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w328 [b328 H328]].
 intros [w370 [b370 H370]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_371. solve_uint_ready.
Qed.
Lemma x0_uint_result_372 invalid site mm old result :
 (exists width bits, VM.find 330 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 371 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_372 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w330 [b330 H330]].
 intros [w371 [b371 H371]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_372. solve_uint_ready.
Qed.
Lemma x0_uint_result_373 invalid site mm old result :
 (exists width bits, VM.find 332 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 372 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_373 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w332 [b332 H332]].
 intros [w372 [b372 H372]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_373. solve_uint_ready.
Qed.
Lemma x0_uint_result_374 invalid site mm old result :
 (exists width bits, VM.find 334 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 373 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_374 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w334 [b334 H334]].
 intros [w373 [b373 H373]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_374. solve_uint_ready.
Qed.
Lemma x0_uint_result_375 invalid site mm old result :
 (exists width bits, VM.find 336 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 374 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_375 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w336 [b336 H336]].
 intros [w374 [b374 H374]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_375. solve_uint_ready.
Qed.
Lemma x0_uint_result_376 invalid site mm old result :
 (exists width bits, VM.find 338 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 375 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_376 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w338 [b338 H338]].
 intros [w375 [b375 H375]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_376. solve_uint_ready.
Qed.
Lemma x0_uint_result_377 invalid site mm old result :
 (exists width bits, VM.find 340 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 376 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_377 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w340 [b340 H340]].
 intros [w376 [b376 H376]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_377. solve_uint_ready.
Qed.
Lemma x0_uint_result_378 invalid site mm old result :
 (exists width bits, VM.find 342 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 377 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_378 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w342 [b342 H342]].
 intros [w377 [b377 H377]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_378. solve_uint_ready.
Qed.
Lemma x0_uint_result_379 invalid site mm old result :
 (exists width bits, VM.find 344 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 378 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_379 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w344 [b344 H344]].
 intros [w378 [b378 H378]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_379. solve_uint_ready.
Qed.
Lemma x0_uint_result_380 invalid site mm old result :
 (exists width bits, VM.find 346 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 379 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_380 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w346 [b346 H346]].
 intros [w379 [b379 H379]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_380. solve_uint_ready.
Qed.
Lemma x0_uint_result_381 invalid site mm old result :
 (exists width bits, VM.find 348 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 380 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_381 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w348 [b348 H348]].
 intros [w380 [b380 H380]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_381. solve_uint_ready.
Qed.
Lemma x0_uint_result_382 invalid site mm old result :
 (exists width bits, VM.find 350 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 381 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_382 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w350 [b350 H350]].
 intros [w381 [b381 H381]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_382. solve_uint_ready.
Qed.
Lemma x0_uint_result_383 invalid site mm old result :
 (exists width bits, VM.find 352 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 382 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_383 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w352 [b352 H352]].
 intros [w382 [b382 H382]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_383. solve_uint_ready.
Qed.
Lemma x0_uint_result_384 invalid site mm old result :
 (exists width bits, VM.find 354 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 383 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_384 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w354 [b354 H354]].
 intros [w383 [b383 H383]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_384. solve_uint_ready.
Qed.
Lemma x0_uint_result_385 invalid site mm old result :
 (exists width bits, VM.find 356 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 384 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_385 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w356 [b356 H356]].
 intros [w384 [b384 H384]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_385. solve_uint_ready.
Qed.
Lemma x0_uint_result_386 invalid site mm old result :
 (exists width bits, VM.find 358 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 385 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_386 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w358 [b358 H358]].
 intros [w385 [b385 H385]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_386. solve_uint_ready.
Qed.
Lemma x0_uint_result_387 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_387 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_387. solve_uint_ready.
Qed.
Lemma x0_uint_result_388 invalid site mm old result :
 (exists width bits, VM.find 387 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_388 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w387 [b387 H387]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_388. solve_uint_ready.
Qed.
Lemma x0_uint_result_389 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_389 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_389. solve_uint_ready.
Qed.
Lemma x0_uint_result_390 invalid site mm old result :
 (exists width bits, VM.find 388 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 389 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_390 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w388 [b388 H388]].
 intros [w389 [b389 H389]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_390. solve_uint_ready.
Qed.
Lemma x0_uint_result_391 invalid site mm old result :
 (exists width bits, VM.find 140 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_391 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w140 [b140 H140]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_391. solve_uint_ready.
Qed.
Lemma x0_uint_result_392 invalid site mm old result :
 (exists width bits, VM.find 390 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 391 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_392 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w390 [b390 H390]].
 intros [w391 [b391 H391]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_392. solve_uint_ready.
Qed.
Lemma x0_uint_result_393 invalid site mm old result :
 (exists width bits, VM.find 118 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_393 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w118 [b118 H118]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_393. solve_uint_ready.
Qed.
Lemma x0_uint_result_394 invalid site mm old result :
 (exists width bits, VM.find 118 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_394 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w118 [b118 H118]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_394. solve_uint_ready.
Qed.
Lemma x0_uint_result_395 invalid site mm old result :
 (exists width bits, VM.find 141 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_395 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w141 [b141 H141]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_395. solve_uint_ready.
Qed.
Lemma x0_uint_result_396 invalid site mm old result :
 (exists width bits, VM.find 394 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 395 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_396 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w394 [b394 H394]].
 intros [w395 [b395 H395]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_396. solve_uint_ready.
Qed.
Lemma x0_uint_result_397 invalid site mm old result :
 (exists width bits, VM.find 393 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 396 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_397 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w393 [b393 H393]].
 intros [w396 [b396 H396]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_397. solve_uint_ready.
Qed.
Lemma x0_uint_result_407 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_407 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_407. solve_uint_ready.
Qed.
Lemma x0_uint_result_408 invalid site mm old result :
 (exists width bits, VM.find 127 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 407 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_408 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w127 [b127 H127]].
 intros [w407 [b407 H407]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_408. solve_uint_ready.
Qed.
Lemma x0_uint_result_409 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_409 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_409. solve_uint_ready.
Qed.
Lemma x0_uint_result_410 invalid site mm old result :
 (exists width bits, VM.find 409 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_410 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w409 [b409 H409]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_410. solve_uint_ready.
Qed.
Lemma x0_uint_result_411 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_411 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_411. solve_uint_ready.
Qed.
Lemma x0_uint_result_412 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_412 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_412. solve_uint_ready.
Qed.
Lemma x0_uint_result_413 invalid site mm old result :
 (exists width bits, VM.find 126 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_413 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w126 [b126 H126]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_413. solve_uint_ready.
Qed.
Lemma x0_uint_result_414 invalid site mm old result :
 (exists width bits, VM.find 410 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 413 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_414 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w410 [b410 H410]].
 intros [w413 [b413 H413]].
 intro Eval. unfold x0_concrete_expr_414 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H410 ?H413 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H410 ?H413 in Eval.
 repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma x0_uint_result_415 invalid site mm old result :
 (exists width bits, VM.find 126 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_415 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w126 [b126 H126]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_415. solve_uint_ready.
Qed.
Lemma x0_uint_result_416 invalid site mm old result :
 (exists width bits, VM.find 411 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 414 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 415 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_416 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w411 [b411 H411]].
 intros [w414 [b414 H414]].
 intros [w415 [b415 H415]].
 intro Eval. unfold x0_concrete_expr_416 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H411 ?H414 ?H415 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H411 ?H414 ?H415 in Eval.
 repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma x0_uint_result_417 invalid site mm old result :
 (exists width bits, VM.find 126 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_417 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w126 [b126 H126]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_417. solve_uint_ready.
Qed.
Lemma x0_uint_result_418 invalid site mm old result :
 (exists width bits, VM.find 412 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 416 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 417 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_418 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w412 [b412 H412]].
 intros [w416 [b416 H416]].
 intros [w417 [b417 H417]].
 intro Eval. unfold x0_concrete_expr_418 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H412 ?H416 ?H417 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H412 ?H416 ?H417 in Eval.
 repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma x0_uint_result_419 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_419 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_419. solve_uint_ready.
Qed.
Lemma x0_uint_result_420 invalid site mm old result :
 (exists width bits, VM.find 419 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_420 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w419 [b419 H419]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_420. solve_uint_ready.
Qed.
Lemma x0_uint_result_421 invalid site mm old result :
 (exists width bits, VM.find 122 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_421 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w122 [b122 H122]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_421. solve_uint_ready.
Qed.
Lemma x0_uint_result_422 invalid site mm old result :
 (exists width bits, VM.find 125 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_422 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w125 [b125 H125]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_422. solve_uint_ready.
Qed.
Lemma x0_uint_result_423 invalid site mm old result :
 (exists width bits, VM.find 420 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 422 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_423 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w420 [b420 H420]].
 intros [w422 [b422 H422]].
 intro Eval. unfold x0_concrete_expr_423 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H420 ?H422 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H420 ?H422 in Eval.
 repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma x0_uint_result_424 invalid site mm old result :
 (exists width bits, VM.find 125 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_424 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w125 [b125 H125]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_424. solve_uint_ready.
Qed.
Lemma x0_uint_result_425 invalid site mm old result :
 (exists width bits, VM.find 421 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 423 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 424 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_425 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w421 [b421 H421]].
 intros [w423 [b423 H423]].
 intros [w424 [b424 H424]].
 intro Eval. unfold x0_concrete_expr_425 in Eval.
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
 rewrite ?H421 ?H423 ?H424 in Eval.
 unfold eval_type_of_expr in Eval. cbn [type_of_expr' eval_type_of_ref] in Eval.
 rewrite ?H421 ?H423 ?H424 in Eval.
 repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;
 cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;
 inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Lemma x0_uint_result_426 invalid site mm old result :
 (exists width bits, VM.find 124 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 408 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_426 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w124 [b124 H124]].
 intros [w408 [b408 H408]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_426. solve_uint_ready.
Qed.
Lemma x0_uint_result_427 invalid site mm old result :
 (exists width bits, VM.find 418 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 426 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_427 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w418 [b418 H418]].
 intros [w426 [b426 H426]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_427. solve_uint_ready.
Qed.
Lemma x0_uint_result_428 invalid site mm old result :
 (exists width bits, VM.find 425 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 427 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_428 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w425 [b425 H425]].
 intros [w427 [b427 H427]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_428. solve_uint_ready.
Qed.
Lemma x0_uint_result_429 invalid site mm old result :
 (exists width bits, VM.find 118 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_429 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w118 [b118 H118]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_429. solve_uint_ready.
Qed.
Lemma x0_uint_result_430 invalid site mm old result :
 (exists width bits, VM.find 429 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_430 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w429 [b429 H429]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_430. solve_uint_ready.
Qed.
Lemma x0_uint_result_431 invalid site mm old result :
 (exists width bits, VM.find 386 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_431 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w386 [b386 H386]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_431. solve_uint_ready.
Qed.
Lemma x0_uint_result_432 invalid site mm old result :
 (exists width bits, VM.find 283 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_432 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w283 [b283 H283]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_432. solve_uint_ready.
Qed.
Lemma x0_uint_result_433 invalid site mm old result :
 (exists width bits, VM.find 431 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 432 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_433 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w431 [b431 H431]].
 intros [w432 [b432 H432]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_433. solve_uint_ready.
Qed.
Lemma x0_uint_result_434 invalid site mm old result :
 (exists width bits, VM.find 430 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 433 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_434 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w430 [b430 H430]].
 intros [w433 [b433 H433]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_434. solve_uint_ready.
Qed.
Lemma x0_uint_result_435 invalid site mm old result :
 (exists width bits, VM.find 428 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 434 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_435 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w428 [b428 H428]].
 intros [w434 [b434 H434]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_435. solve_uint_ready.
Qed.
Lemma x0_uint_result_436 invalid site mm old result :
 (exists width bits, VM.find 392 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 397 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_436 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w392 [b392 H392]].
 intros [w397 [b397 H397]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_436. solve_uint_ready.
Qed.
Lemma x0_uint_result_437 invalid site mm old result :
 (exists width bits, VM.find 435 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 436 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_437 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w435 [b435 H435]].
 intros [w436 [b436 H436]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_437. solve_uint_ready.
Qed.
Lemma x0_uint_result_438 invalid site mm old result :
 (exists width bits, VM.find 283 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_438 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w283 [b283 H283]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_438. solve_uint_ready.
Qed.
Lemma x0_uint_result_439 invalid site mm old result :
 (exists width bits, VM.find 284 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 438 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_439 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w284 [b284 H284]].
 intros [w438 [b438 H438]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_439. solve_uint_ready.
Qed.
Lemma x0_uint_result_440 invalid site mm old result :
 (exists width bits, VM.find 437 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 439 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_440 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w437 [b437 H437]].
 intros [w439 [b439 H439]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_440. solve_uint_ready.
Qed.
Lemma x0_uint_result_441 invalid site mm old result :
 (exists width bits, VM.find 290 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 440 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_441 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w290 [b290 H290]].
 intros [w440 [b440 H440]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_441. solve_uint_ready.
Qed.
Lemma x0_uint_result_442 invalid site mm old result :
 (exists width bits, VM.find 295 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 441 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_442 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w295 [b295 H295]].
 intros [w441 [b441 H441]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_442. solve_uint_ready.
Qed.
Lemma x0_uint_result_7763 invalid site mm old result :
 (exists width bits, VM.find 74 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7763 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w74 [b74 H74]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7763. solve_uint_ready.
Qed.
Lemma x0_uint_result_7764 invalid site mm old result :
 (exists width bits, VM.find 81 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7764 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w81 [b81 H81]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7764. solve_uint_ready.
Qed.
Lemma x0_uint_result_7765 invalid site mm old result :
 (exists width bits, VM.find 7763 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7764 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7765 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7763 [b7763 H7763]].
 intros [w7764 [b7764 H7764]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7765. solve_uint_ready.
Qed.
Lemma x0_uint_result_7805 invalid site mm old result :
 (exists width bits, VM.find 7750 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7805 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7750 [b7750 H7750]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7805. solve_uint_ready.
Qed.
Lemma x0_uint_result_7938 invalid site mm old result :
 (exists width bits, VM.find 7765 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7938 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7765 [b7765 H7765]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7938. solve_uint_ready.
Qed.
Lemma x0_uint_result_7939 invalid site mm old result :
 (exists width bits, VM.find 7757 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7938 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7939 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7757 [b7757 H7757]].
 intros [w7938 [b7938 H7938]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7939. solve_uint_ready.
Qed.
Lemma x0_uint_result_7940 invalid site mm old result :
 (exists width bits, VM.find 128 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7940 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w128 [b128 H128]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7940. solve_uint_ready.
Qed.
Lemma x0_uint_result_7941 invalid site mm old result :
 (exists width bits, VM.find 7939 old = Some (Gval (Fuint width) bits)) ->
 (exists width bits, VM.find 7940 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_7941 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w7939 [b7939 H7939]].
 intros [w7940 [b7940 H7940]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_7941. solve_uint_ready.
Qed.
Lemma x0_uint_result_9215 invalid site mm old result :
 (exists width bits, VM.find 1 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_9215 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1 [b1 H1]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_9215. solve_uint_ready.
Qed.
Lemma x0_uint_result_9216 invalid site mm old result :
 (exists width bits, VM.find 9215 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_9216 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9215 [b9215 H9215]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_9216. solve_uint_ready.
Qed.
Lemma x0_uint_result_9217 invalid site mm old result :
 (exists width bits, VM.find 1 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_9217 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w1 [b1 H1]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_9217. solve_uint_ready.
Qed.
Lemma x0_uint_result_9218 invalid site mm old result :
 (exists width bits, VM.find 9217 old = Some (Gval (Fuint width) bits)) ->
 eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_9218 old old = Some result ->
 concrete_uint_value result.
Proof.
 intros [w9217 [b9217 H9217]].
 apply formal_uint_scalar_concrete. unfold x0_concrete_expr_9218. solve_uint_ready.
Qed.
Print Assumptions x0_uint_result_7941.
