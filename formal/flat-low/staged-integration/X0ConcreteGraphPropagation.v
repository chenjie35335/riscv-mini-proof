Require Import CoreSocModel ComparisonNodes X0DependencyRanks CheckedDependencyHistory X0ConcreteOutputCertificates X0ConcreteConnectionOutputs.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition x0_concrete_at (env : VM.t hvalue) (node : nat) : Prop :=
 exists width bits, VM.find (N.of_nat node) env = Some (Gval (Fuint width) bits).
Theorem x0_dependency_step inputs path old current result node rank dependencies :
 List.In (node, (rank, dependencies)) x0_dependency_ranks ->
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> x0_concrete_at old source) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 x0_concrete_at result node.
Proof.
 intros Member Positive Sources Step. unfold x0_dependency_ranks in Member.
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   lia. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_118 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7758 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_122 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7752 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_123 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7750 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_124 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7759 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_125 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7754 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_126 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7755 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_127 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7760 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7805 inputs path old current result).
   - exact (Sources 7750 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_9215 inputs path old current result).
   - exact (Sources 1 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_9217 inputs path old current result).
   - exact (Sources 1 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_140 inputs path old current result).
   - exact (Sources 123 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_141 inputs path old current result).
   - exact (Sources 123 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_284 inputs path old current result).
   - exact (Sources 118 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_393 inputs path old current result).
   - exact (Sources 118 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_394 inputs path old current result).
   - exact (Sources 118 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_407 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_409 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_411 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_412 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_413 inputs path old current result).
   - exact (Sources 126 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_415 inputs path old current result).
   - exact (Sources 126 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_417 inputs path old current result).
   - exact (Sources 126 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_419 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_421 inputs path old current result).
   - exact (Sources 122 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_422 inputs path old current result).
   - exact (Sources 125 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_424 inputs path old current result).
   - exact (Sources 125 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_429 inputs path old current result).
   - exact (Sources 118 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_785 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7805 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_9216 inputs path old current result).
   - exact (Sources 9215 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_9218 inputs path old current result).
   - exact (Sources 9217 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_33 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 9216 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_40 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 9218 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_282 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_285 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_288 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_291 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_293 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_301 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_303 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_305 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_307 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_309 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_311 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_313 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_315 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_317 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_319 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_321 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_323 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_325 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_327 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_329 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_331 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_333 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_335 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_337 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_339 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_341 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_343 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_345 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_347 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_349 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_351 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_353 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_355 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_357 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_387 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_389 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_391 inputs path old current result).
   - exact (Sources 140 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_395 inputs path old current result).
   - exact (Sources 141 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_408 inputs path old current result).
   - exact (Sources 127 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 407 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_410 inputs path old current result).
   - exact (Sources 409 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_420 inputs path old current result).
   - exact (Sources 419 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_430 inputs path old current result).
   - exact (Sources 429 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_74 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 33 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_81 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 40 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_283 inputs path old current result).
   - exact (Sources 150 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 282 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_286 inputs path old current result).
   - exact (Sources 285 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_289 inputs path old current result).
   - exact (Sources 288 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_292 inputs path old current result).
   - exact (Sources 284 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 291 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_294 inputs path old current result).
   - exact (Sources 293 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_302 inputs path old current result).
   - exact (Sources 301 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_304 inputs path old current result).
   - exact (Sources 303 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_306 inputs path old current result).
   - exact (Sources 305 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_308 inputs path old current result).
   - exact (Sources 307 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_310 inputs path old current result).
   - exact (Sources 309 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_312 inputs path old current result).
   - exact (Sources 311 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_314 inputs path old current result).
   - exact (Sources 313 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_316 inputs path old current result).
   - exact (Sources 315 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_318 inputs path old current result).
   - exact (Sources 317 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_320 inputs path old current result).
   - exact (Sources 319 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_322 inputs path old current result).
   - exact (Sources 321 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_324 inputs path old current result).
   - exact (Sources 323 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_326 inputs path old current result).
   - exact (Sources 325 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_328 inputs path old current result).
   - exact (Sources 327 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_330 inputs path old current result).
   - exact (Sources 329 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_332 inputs path old current result).
   - exact (Sources 331 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_334 inputs path old current result).
   - exact (Sources 333 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_336 inputs path old current result).
   - exact (Sources 335 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_338 inputs path old current result).
   - exact (Sources 337 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_340 inputs path old current result).
   - exact (Sources 339 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_342 inputs path old current result).
   - exact (Sources 341 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_344 inputs path old current result).
   - exact (Sources 343 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_346 inputs path old current result).
   - exact (Sources 345 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_348 inputs path old current result).
   - exact (Sources 347 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_350 inputs path old current result).
   - exact (Sources 349 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_352 inputs path old current result).
   - exact (Sources 351 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_354 inputs path old current result).
   - exact (Sources 353 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_356 inputs path old current result).
   - exact (Sources 355 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_358 inputs path old current result).
   - exact (Sources 357 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_388 inputs path old current result).
   - exact (Sources 387 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_396 inputs path old current result).
   - exact (Sources 394 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 395 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_414 inputs path old current result).
   - exact (Sources 410 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 413 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_423 inputs path old current result).
   - exact (Sources 420 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 422 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_426 inputs path old current result).
   - exact (Sources 124 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 408 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_287 inputs path old current result).
   - exact (Sources 284 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 286 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_295 inputs path old current result).
   - exact (Sources 292 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 294 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_359 inputs path old current result).
   - exact (Sources 302 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 304 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_390 inputs path old current result).
   - exact (Sources 388 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 389 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_397 inputs path old current result).
   - exact (Sources 393 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 396 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_416 inputs path old current result).
   - exact (Sources 411 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 414 ltac:(do 1 right; left; reflexivity)).
   - exact (Sources 415 ltac:(do 2 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_425 inputs path old current result).
   - exact (Sources 421 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 423 ltac:(do 1 right; left; reflexivity)).
   - exact (Sources 424 ltac:(do 2 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_432 inputs path old current result).
   - exact (Sources 283 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_438 inputs path old current result).
   - exact (Sources 283 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7763 inputs path old current result).
   - exact (Sources 74 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7764 inputs path old current result).
   - exact (Sources 81 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_290 inputs path old current result).
   - exact (Sources 287 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 289 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_360 inputs path old current result).
   - exact (Sources 306 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 359 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_392 inputs path old current result).
   - exact (Sources 390 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 391 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_418 inputs path old current result).
   - exact (Sources 412 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 416 ltac:(do 1 right; left; reflexivity)).
   - exact (Sources 417 ltac:(do 2 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_439 inputs path old current result).
   - exact (Sources 284 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 438 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7765 inputs path old current result).
   - exact (Sources 7763 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 7764 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_361 inputs path old current result).
   - exact (Sources 308 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 360 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_427 inputs path old current result).
   - exact (Sources 418 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 426 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_436 inputs path old current result).
   - exact (Sources 392 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 397 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7938 inputs path old current result).
   - exact (Sources 7765 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_362 inputs path old current result).
   - exact (Sources 310 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 361 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_428 inputs path old current result).
   - exact (Sources 425 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 427 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7939 inputs path old current result).
   - exact (Sources 7757 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 7938 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_363 inputs path old current result).
   - exact (Sources 312 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 362 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_364 inputs path old current result).
   - exact (Sources 314 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 363 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_365 inputs path old current result).
   - exact (Sources 316 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 364 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_366 inputs path old current result).
   - exact (Sources 318 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 365 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_367 inputs path old current result).
   - exact (Sources 320 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 366 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_368 inputs path old current result).
   - exact (Sources 322 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 367 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_369 inputs path old current result).
   - exact (Sources 324 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 368 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_370 inputs path old current result).
   - exact (Sources 326 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 369 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_371 inputs path old current result).
   - exact (Sources 328 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 370 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_372 inputs path old current result).
   - exact (Sources 330 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 371 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_373 inputs path old current result).
   - exact (Sources 332 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 372 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_374 inputs path old current result).
   - exact (Sources 334 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 373 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_375 inputs path old current result).
   - exact (Sources 336 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 374 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_376 inputs path old current result).
   - exact (Sources 338 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 375 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_377 inputs path old current result).
   - exact (Sources 340 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 376 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_378 inputs path old current result).
   - exact (Sources 342 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 377 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_379 inputs path old current result).
   - exact (Sources 344 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 378 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_380 inputs path old current result).
   - exact (Sources 346 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 379 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_381 inputs path old current result).
   - exact (Sources 348 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 380 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_382 inputs path old current result).
   - exact (Sources 350 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 381 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_383 inputs path old current result).
   - exact (Sources 352 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 382 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_384 inputs path old current result).
   - exact (Sources 354 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 383 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_385 inputs path old current result).
   - exact (Sources 356 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 384 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_386 inputs path old current result).
   - exact (Sources 358 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 385 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_431 inputs path old current result).
   - exact (Sources 386 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_433 inputs path old current result).
   - exact (Sources 431 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 432 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_434 inputs path old current result).
   - exact (Sources 430 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 433 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_435 inputs path old current result).
   - exact (Sources 428 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 434 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_437 inputs path old current result).
   - exact (Sources 435 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 436 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_440 inputs path old current result).
   - exact (Sources 437 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 439 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_441 inputs path old current result).
   - exact (Sources 290 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 440 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_442 inputs path old current result).
   - exact (Sources 295 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 441 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_128 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 442 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7940 inputs path old current result).
   - exact (Sources 128 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_node_output_7941 inputs path old current result).
   - exact (Sources 7939 ltac:(do 0 right; left; reflexivity)).
   - exact (Sources 7940 ltac:(do 1 right; left; reflexivity)).
   - exact Step. }
 destruct Member as [Equal|Member].
 { inversion Equal; subst node rank dependencies.
   apply (x0_connection_output_784 (formal_invalid_policy inputs path) old current result).
   - exact (Sources 7941 ltac:(do 0 right; left; reflexivity)).
   - exact Step. }
 contradiction.
Qed.
Theorem x0_concrete_history_targets inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
   List.In (node, (0%nat, dependencies)) x0_dependency_ranks -> x0_concrete_at (history time) node) ->
 (forall time, (time < limit)%coq_nat ->
   formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> (44 <= time)%coq_nat ->
 x0_concrete_at (history time) 784 /\ x0_concrete_at (history time) 785.
Proof.
 intros Boundary Steps.
 apply (x0_checked_history_targets (fun time node => x0_concrete_at (history time) node) limit Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 exact (x0_dependency_step inputs path (history time) (history time) (history (S time)) node rank dependencies
 Member Positive Sources (Steps time Within)).
Qed.
Print Assumptions x0_concrete_history_targets.
