Require Import PCDecodeExpressionValues CoreSocModel ComparisonNodes FormalTypedNodeEquation FormalTypedNodeFrames ScalarNodeFrames FormalStatementSegments RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition decode_tail_8263 := match straight_drop 9024 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8263 : straight_drop 9023 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8263 decode_expr_8263) decode_tail_8263).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8263 : formal_typed_suffix_safe flat_memories 8263 decode_tail_8263.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8263 : has_register 8263 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8263 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8263 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8263 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8263|exact decode_suffix_8263|exact decode_nonregister_8263|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8265 := match straight_drop 9026 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8265 : straight_drop 9025 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8265 decode_expr_8265) decode_tail_8265).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8265 : formal_typed_suffix_safe flat_memories 8265 decode_tail_8265.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8265 : has_register 8265 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8265 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8265 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8265 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8265|exact decode_suffix_8265|exact decode_nonregister_8265|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8267 := match straight_drop 9028 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8267 : straight_drop 9027 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8267 decode_expr_8267) decode_tail_8267).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8267 : formal_typed_suffix_safe flat_memories 8267 decode_tail_8267.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8267 : has_register 8267 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8267 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8267 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8267 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8267|exact decode_suffix_8267|exact decode_nonregister_8267|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8269 := match straight_drop 9030 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8269 : straight_drop 9029 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8269 decode_expr_8269) decode_tail_8269).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8269 : formal_typed_suffix_safe flat_memories 8269 decode_tail_8269.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8269 : has_register 8269 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8269 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8269 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8269 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8269|exact decode_suffix_8269|exact decode_nonregister_8269|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8271 := match straight_drop 9032 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8271 : straight_drop 9031 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8271 decode_expr_8271) decode_tail_8271).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8271 : formal_typed_suffix_safe flat_memories 8271 decode_tail_8271.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8271 : has_register 8271 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8271 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8271 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8271 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8271|exact decode_suffix_8271|exact decode_nonregister_8271|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8273 := match straight_drop 9034 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8273 : straight_drop 9033 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8273 decode_expr_8273) decode_tail_8273).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8273 : formal_typed_suffix_safe flat_memories 8273 decode_tail_8273.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8273 : has_register 8273 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8273 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8273 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8273 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8273|exact decode_suffix_8273|exact decode_nonregister_8273|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8275 := match straight_drop 9036 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8275 : straight_drop 9035 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8275 decode_expr_8275) decode_tail_8275).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8275 : formal_typed_suffix_safe flat_memories 8275 decode_tail_8275.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8275 : has_register 8275 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8275 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8275 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8275 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8275|exact decode_suffix_8275|exact decode_nonregister_8275|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8277 := match straight_drop 9038 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8277 : straight_drop 9037 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8277 decode_expr_8277) decode_tail_8277).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8277 : formal_typed_suffix_safe flat_memories 8277 decode_tail_8277.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8277 : has_register 8277 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8277 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8277 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8277 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8277|exact decode_suffix_8277|exact decode_nonregister_8277|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8279 := match straight_drop 9040 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8279 : straight_drop 9039 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8279 decode_expr_8279) decode_tail_8279).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8279 : formal_typed_suffix_safe flat_memories 8279 decode_tail_8279.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8279 : has_register 8279 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8279 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8279 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8279 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8279|exact decode_suffix_8279|exact decode_nonregister_8279|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8281 := match straight_drop 9042 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8281 : straight_drop 9041 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8281 decode_expr_8281) decode_tail_8281).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8281 : formal_typed_suffix_safe flat_memories 8281 decode_tail_8281.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8281 : has_register 8281 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8281 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8281 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8281 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8281|exact decode_suffix_8281|exact decode_nonregister_8281|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8283 := match straight_drop 9044 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8283 : straight_drop 9043 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8283 decode_expr_8283) decode_tail_8283).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8283 : formal_typed_suffix_safe flat_memories 8283 decode_tail_8283.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8283 : has_register 8283 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8283 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8283 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8283 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8283|exact decode_suffix_8283|exact decode_nonregister_8283|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8285 := match straight_drop 9046 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8285 : straight_drop 9045 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8285 decode_expr_8285) decode_tail_8285).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8285 : formal_typed_suffix_safe flat_memories 8285 decode_tail_8285.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8285 : has_register 8285 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8285 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8285 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8285 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8285|exact decode_suffix_8285|exact decode_nonregister_8285|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8287 := match straight_drop 9048 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8287 : straight_drop 9047 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8287 decode_expr_8287) decode_tail_8287).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8287 : formal_typed_suffix_safe flat_memories 8287 decode_tail_8287.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8287 : has_register 8287 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8287 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8287 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8287 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8287|exact decode_suffix_8287|exact decode_nonregister_8287|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8289 := match straight_drop 9050 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8289 : straight_drop 9049 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8289 decode_expr_8289) decode_tail_8289).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8289 : formal_typed_suffix_safe flat_memories 8289 decode_tail_8289.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8289 : has_register 8289 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8289 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8289 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8289 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8289|exact decode_suffix_8289|exact decode_nonregister_8289|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8291 := match straight_drop 9052 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8291 : straight_drop 9051 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8291 decode_expr_8291) decode_tail_8291).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8291 : formal_typed_suffix_safe flat_memories 8291 decode_tail_8291.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8291 : has_register 8291 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8291 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8291 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8291 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8291|exact decode_suffix_8291|exact decode_nonregister_8291|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8293 := match straight_drop 9054 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8293 : straight_drop 9053 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8293 decode_expr_8293) decode_tail_8293).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8293 : formal_typed_suffix_safe flat_memories 8293 decode_tail_8293.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8293 : has_register 8293 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8293 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8293 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8293 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8293|exact decode_suffix_8293|exact decode_nonregister_8293|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8297 := match straight_drop 9058 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8297 : straight_drop 9057 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8297 decode_expr_8297) decode_tail_8297).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8297 : formal_typed_suffix_safe flat_memories 8297 decode_tail_8297.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8297 : has_register 8297 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8297 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8297 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8297 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8297|exact decode_suffix_8297|exact decode_nonregister_8297|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8299 := match straight_drop 9060 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8299 : straight_drop 9059 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8299 decode_expr_8299) decode_tail_8299).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8299 : formal_typed_suffix_safe flat_memories 8299 decode_tail_8299.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8299 : has_register 8299 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8299 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8299 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8299 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8299|exact decode_suffix_8299|exact decode_nonregister_8299|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8295 := match straight_drop 9056 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8295 : straight_drop 9055 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8295 decode_expr_8295) decode_tail_8295).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8295 : formal_typed_suffix_safe flat_memories 8295 decode_tail_8295.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8295 : has_register 8295 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8295 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8295 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8295 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8295|exact decode_suffix_8295|exact decode_nonregister_8295|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8301 := match straight_drop 9062 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8301 : straight_drop 9061 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8301 decode_expr_8301) decode_tail_8301).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8301 : formal_typed_suffix_safe flat_memories 8301 decode_tail_8301.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8301 : has_register 8301 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8301 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8301 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8301 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8301|exact decode_suffix_8301|exact decode_nonregister_8301|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8305 := match straight_drop 9066 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8305 : straight_drop 9065 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8305 decode_expr_8305) decode_tail_8305).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8305 : formal_typed_suffix_safe flat_memories 8305 decode_tail_8305.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8305 : has_register 8305 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8305 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8305 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8305 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8305|exact decode_suffix_8305|exact decode_nonregister_8305|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8303 := match straight_drop 9064 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8303 : straight_drop 9063 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8303 decode_expr_8303) decode_tail_8303).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8303 : formal_typed_suffix_safe flat_memories 8303 decode_tail_8303.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8303 : has_register 8303 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8303 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8303 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8303 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8303|exact decode_suffix_8303|exact decode_nonregister_8303|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8309 := match straight_drop 9070 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8309 : straight_drop 9069 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8309 decode_expr_8309) decode_tail_8309).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8309 : formal_typed_suffix_safe flat_memories 8309 decode_tail_8309.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8309 : has_register 8309 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8309 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8309 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8309 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8309|exact decode_suffix_8309|exact decode_nonregister_8309|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8307 := match straight_drop 9068 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8307 : straight_drop 9067 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8307 decode_expr_8307) decode_tail_8307).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8307 : formal_typed_suffix_safe flat_memories 8307 decode_tail_8307.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8307 : has_register 8307 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8307 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8307 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8307 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8307|exact decode_suffix_8307|exact decode_nonregister_8307|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8311 := match straight_drop 9072 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8311 : straight_drop 9071 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8311 decode_expr_8311) decode_tail_8311).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8311 : formal_typed_suffix_safe flat_memories 8311 decode_tail_8311.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8311 : has_register 8311 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8311 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8311 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8311 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8311|exact decode_suffix_8311|exact decode_nonregister_8311|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8313 := match straight_drop 9074 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8313 : straight_drop 9073 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8313 decode_expr_8313) decode_tail_8313).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8313 : formal_typed_suffix_safe flat_memories 8313 decode_tail_8313.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8313 : has_register 8313 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8313 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8313 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8313 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8313|exact decode_suffix_8313|exact decode_nonregister_8313|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8315 := match straight_drop 9076 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8315 : straight_drop 9075 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8315 decode_expr_8315) decode_tail_8315).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8315 : formal_typed_suffix_safe flat_memories 8315 decode_tail_8315.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8315 : has_register 8315 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8315 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8315 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8315 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8315|exact decode_suffix_8315|exact decode_nonregister_8315|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8317 := match straight_drop 9078 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8317 : straight_drop 9077 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8317 decode_expr_8317) decode_tail_8317).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8317 : formal_typed_suffix_safe flat_memories 8317 decode_tail_8317.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8317 : has_register 8317 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8317 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8317 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8317 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8317|exact decode_suffix_8317|exact decode_nonregister_8317|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8319 := match straight_drop 9080 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8319 : straight_drop 9079 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8319 decode_expr_8319) decode_tail_8319).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8319 : formal_typed_suffix_safe flat_memories 8319 decode_tail_8319.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8319 : has_register 8319 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8319 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8319 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8319 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8319|exact decode_suffix_8319|exact decode_nonregister_8319|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8321 := match straight_drop 9082 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8321 : straight_drop 9081 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8321 decode_expr_8321) decode_tail_8321).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8321 : formal_typed_suffix_safe flat_memories 8321 decode_tail_8321.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8321 : has_register 8321 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8321 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8321 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8321 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8321|exact decode_suffix_8321|exact decode_nonregister_8321|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8323 := match straight_drop 9084 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8323 : straight_drop 9083 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8323 decode_expr_8323) decode_tail_8323).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8323 : formal_typed_suffix_safe flat_memories 8323 decode_tail_8323.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8323 : has_register 8323 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8323 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8323 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8323 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8323|exact decode_suffix_8323|exact decode_nonregister_8323|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8325 := match straight_drop 9086 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8325 : straight_drop 9085 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8325 decode_expr_8325) decode_tail_8325).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8325 : formal_typed_suffix_safe flat_memories 8325 decode_tail_8325.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8325 : has_register 8325 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8325 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8325 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8325 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8325|exact decode_suffix_8325|exact decode_nonregister_8325|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8327 := match straight_drop 9088 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8327 : straight_drop 9087 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8327 decode_expr_8327) decode_tail_8327).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8327 : formal_typed_suffix_safe flat_memories 8327 decode_tail_8327.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8327 : has_register 8327 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8327 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8327 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8327 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8327|exact decode_suffix_8327|exact decode_nonregister_8327|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8329 := match straight_drop 9090 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8329 : straight_drop 9089 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8329 decode_expr_8329) decode_tail_8329).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8329 : formal_typed_suffix_safe flat_memories 8329 decode_tail_8329.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8329 : has_register 8329 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8329 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8329 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8329 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8329|exact decode_suffix_8329|exact decode_nonregister_8329|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8331 := match straight_drop 9092 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8331 : straight_drop 9091 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8331 decode_expr_8331) decode_tail_8331).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8331 : formal_typed_suffix_safe flat_memories 8331 decode_tail_8331.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8331 : has_register 8331 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8331 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8331 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8331 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8331|exact decode_suffix_8331|exact decode_nonregister_8331|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8333 := match straight_drop 9094 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8333 : straight_drop 9093 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8333 decode_expr_8333) decode_tail_8333).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8333 : formal_typed_suffix_safe flat_memories 8333 decode_tail_8333.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8333 : has_register 8333 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8333 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8333 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8333 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8333|exact decode_suffix_8333|exact decode_nonregister_8333|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8335 := match straight_drop 9096 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8335 : straight_drop 9095 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8335 decode_expr_8335) decode_tail_8335).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8335 : formal_typed_suffix_safe flat_memories 8335 decode_tail_8335.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8335 : has_register 8335 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8335 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8335 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8335 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8335|exact decode_suffix_8335|exact decode_nonregister_8335|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8337 := match straight_drop 9098 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8337 : straight_drop 9097 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8337 decode_expr_8337) decode_tail_8337).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8337 : formal_typed_suffix_safe flat_memories 8337 decode_tail_8337.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8337 : has_register 8337 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8337 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8337 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8337 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8337|exact decode_suffix_8337|exact decode_nonregister_8337|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8339 := match straight_drop 9100 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8339 : straight_drop 9099 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8339 decode_expr_8339) decode_tail_8339).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8339 : formal_typed_suffix_safe flat_memories 8339 decode_tail_8339.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8339 : has_register 8339 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8339 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8339 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8339 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8339|exact decode_suffix_8339|exact decode_nonregister_8339|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8341 := match straight_drop 9102 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8341 : straight_drop 9101 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8341 decode_expr_8341) decode_tail_8341).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8341 : formal_typed_suffix_safe flat_memories 8341 decode_tail_8341.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8341 : has_register 8341 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8341 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8341 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8341 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8341|exact decode_suffix_8341|exact decode_nonregister_8341|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8343 := match straight_drop 9104 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8343 : straight_drop 9103 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8343 decode_expr_8343) decode_tail_8343).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8343 : formal_typed_suffix_safe flat_memories 8343 decode_tail_8343.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8343 : has_register 8343 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8343 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8343 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8343 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8343|exact decode_suffix_8343|exact decode_nonregister_8343|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8345 := match straight_drop 9106 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8345 : straight_drop 9105 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8345 decode_expr_8345) decode_tail_8345).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8345 : formal_typed_suffix_safe flat_memories 8345 decode_tail_8345.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8345 : has_register 8345 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8345 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8345 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8345 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8345|exact decode_suffix_8345|exact decode_nonregister_8345|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8347 := match straight_drop 9108 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8347 : straight_drop 9107 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8347 decode_expr_8347) decode_tail_8347).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8347 : formal_typed_suffix_safe flat_memories 8347 decode_tail_8347.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8347 : has_register 8347 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8347 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8347 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8347 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8347|exact decode_suffix_8347|exact decode_nonregister_8347|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8349 := match straight_drop 9110 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8349 : straight_drop 9109 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8349 decode_expr_8349) decode_tail_8349).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8349 : formal_typed_suffix_safe flat_memories 8349 decode_tail_8349.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8349 : has_register 8349 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8349 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8349 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8349 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8349|exact decode_suffix_8349|exact decode_nonregister_8349|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8351 := match straight_drop 9112 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8351 : straight_drop 9111 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8351 decode_expr_8351) decode_tail_8351).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8351 : formal_typed_suffix_safe flat_memories 8351 decode_tail_8351.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8351 : has_register 8351 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8351 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8351 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8351 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8351|exact decode_suffix_8351|exact decode_nonregister_8351|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8353 := match straight_drop 9114 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8353 : straight_drop 9113 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8353 decode_expr_8353) decode_tail_8353).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8353 : formal_typed_suffix_safe flat_memories 8353 decode_tail_8353.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8353 : has_register 8353 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8353 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8353 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8353 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8353|exact decode_suffix_8353|exact decode_nonregister_8353|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8355 := match straight_drop 9116 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8355 : straight_drop 9115 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8355 decode_expr_8355) decode_tail_8355).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8355 : formal_typed_suffix_safe flat_memories 8355 decode_tail_8355.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8355 : has_register 8355 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8355 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8355 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8355 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8355|exact decode_suffix_8355|exact decode_nonregister_8355|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8357 := match straight_drop 9118 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8357 : straight_drop 9117 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8357 decode_expr_8357) decode_tail_8357).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8357 : formal_typed_suffix_safe flat_memories 8357 decode_tail_8357.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8357 : has_register 8357 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8357 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8357 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8357 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8357|exact decode_suffix_8357|exact decode_nonregister_8357|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8359 := match straight_drop 9120 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8359 : straight_drop 9119 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8359 decode_expr_8359) decode_tail_8359).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8359 : formal_typed_suffix_safe flat_memories 8359 decode_tail_8359.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8359 : has_register 8359 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8359 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8359 old old = Some value ->
 type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8359 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8359|exact decode_suffix_8359|exact decode_nonregister_8359|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8264 := match straight_drop 9025 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8264 : straight_drop 9024 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8264 decode_expr_8264) decode_tail_8264).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8264 : formal_typed_suffix_safe flat_memories 8264 decode_tail_8264.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8264 : has_register 8264 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8264 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8264 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8264 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8264|exact decode_suffix_8264|exact decode_nonregister_8264|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8266 := match straight_drop 9027 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8266 : straight_drop 9026 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8266 decode_expr_8266) decode_tail_8266).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8266 : formal_typed_suffix_safe flat_memories 8266 decode_tail_8266.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8266 : has_register 8266 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8266 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8266 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8266 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8266|exact decode_suffix_8266|exact decode_nonregister_8266|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8268 := match straight_drop 9029 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8268 : straight_drop 9028 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8268 decode_expr_8268) decode_tail_8268).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8268 : formal_typed_suffix_safe flat_memories 8268 decode_tail_8268.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8268 : has_register 8268 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8268 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8268 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8268 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8268|exact decode_suffix_8268|exact decode_nonregister_8268|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8270 := match straight_drop 9031 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8270 : straight_drop 9030 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8270 decode_expr_8270) decode_tail_8270).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8270 : formal_typed_suffix_safe flat_memories 8270 decode_tail_8270.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8270 : has_register 8270 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8270 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8270 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8270 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8270|exact decode_suffix_8270|exact decode_nonregister_8270|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8272 := match straight_drop 9033 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8272 : straight_drop 9032 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8272 decode_expr_8272) decode_tail_8272).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8272 : formal_typed_suffix_safe flat_memories 8272 decode_tail_8272.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8272 : has_register 8272 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8272 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8272 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8272 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8272|exact decode_suffix_8272|exact decode_nonregister_8272|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8274 := match straight_drop 9035 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8274 : straight_drop 9034 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8274 decode_expr_8274) decode_tail_8274).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8274 : formal_typed_suffix_safe flat_memories 8274 decode_tail_8274.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8274 : has_register 8274 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8274 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8274 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8274 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8274|exact decode_suffix_8274|exact decode_nonregister_8274|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8276 := match straight_drop 9037 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8276 : straight_drop 9036 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8276 decode_expr_8276) decode_tail_8276).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8276 : formal_typed_suffix_safe flat_memories 8276 decode_tail_8276.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8276 : has_register 8276 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8276 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8276 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8276 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8276|exact decode_suffix_8276|exact decode_nonregister_8276|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8278 := match straight_drop 9039 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8278 : straight_drop 9038 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8278 decode_expr_8278) decode_tail_8278).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8278 : formal_typed_suffix_safe flat_memories 8278 decode_tail_8278.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8278 : has_register 8278 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8278 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8278 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8278 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8278|exact decode_suffix_8278|exact decode_nonregister_8278|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8280 := match straight_drop 9041 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8280 : straight_drop 9040 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8280 decode_expr_8280) decode_tail_8280).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8280 : formal_typed_suffix_safe flat_memories 8280 decode_tail_8280.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8280 : has_register 8280 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8280 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8280 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8280 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8280|exact decode_suffix_8280|exact decode_nonregister_8280|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8282 := match straight_drop 9043 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8282 : straight_drop 9042 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8282 decode_expr_8282) decode_tail_8282).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8282 : formal_typed_suffix_safe flat_memories 8282 decode_tail_8282.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8282 : has_register 8282 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8282 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8282 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8282 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8282|exact decode_suffix_8282|exact decode_nonregister_8282|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8284 := match straight_drop 9045 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8284 : straight_drop 9044 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8284 decode_expr_8284) decode_tail_8284).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8284 : formal_typed_suffix_safe flat_memories 8284 decode_tail_8284.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8284 : has_register 8284 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8284 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8284 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8284 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8284|exact decode_suffix_8284|exact decode_nonregister_8284|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8286 := match straight_drop 9047 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8286 : straight_drop 9046 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8286 decode_expr_8286) decode_tail_8286).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8286 : formal_typed_suffix_safe flat_memories 8286 decode_tail_8286.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8286 : has_register 8286 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8286 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8286 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8286 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8286|exact decode_suffix_8286|exact decode_nonregister_8286|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8288 := match straight_drop 9049 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8288 : straight_drop 9048 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8288 decode_expr_8288) decode_tail_8288).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8288 : formal_typed_suffix_safe flat_memories 8288 decode_tail_8288.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8288 : has_register 8288 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8288 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8288 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8288 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8288|exact decode_suffix_8288|exact decode_nonregister_8288|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8290 := match straight_drop 9051 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8290 : straight_drop 9050 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8290 decode_expr_8290) decode_tail_8290).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8290 : formal_typed_suffix_safe flat_memories 8290 decode_tail_8290.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8290 : has_register 8290 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8290 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8290 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8290 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8290|exact decode_suffix_8290|exact decode_nonregister_8290|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8292 := match straight_drop 9053 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8292 : straight_drop 9052 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8292 decode_expr_8292) decode_tail_8292).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8292 : formal_typed_suffix_safe flat_memories 8292 decode_tail_8292.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8292 : has_register 8292 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8292 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8292 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8292 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8292|exact decode_suffix_8292|exact decode_nonregister_8292|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8294 := match straight_drop 9055 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8294 : straight_drop 9054 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8294 decode_expr_8294) decode_tail_8294).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8294 : formal_typed_suffix_safe flat_memories 8294 decode_tail_8294.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8294 : has_register 8294 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8294 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8294 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8294 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8294|exact decode_suffix_8294|exact decode_nonregister_8294|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8296 := match straight_drop 9057 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8296 : straight_drop 9056 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8296 decode_expr_8296) decode_tail_8296).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8296 : formal_typed_suffix_safe flat_memories 8296 decode_tail_8296.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8296 : has_register 8296 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8296 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8296 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8296 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8296|exact decode_suffix_8296|exact decode_nonregister_8296|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8298 := match straight_drop 9059 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8298 : straight_drop 9058 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8298 decode_expr_8298) decode_tail_8298).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8298 : formal_typed_suffix_safe flat_memories 8298 decode_tail_8298.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8298 : has_register 8298 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8298 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8298 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8298 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8298|exact decode_suffix_8298|exact decode_nonregister_8298|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8300 := match straight_drop 9061 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8300 : straight_drop 9060 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8300 decode_expr_8300) decode_tail_8300).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8300 : formal_typed_suffix_safe flat_memories 8300 decode_tail_8300.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8300 : has_register 8300 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8300 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8300 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8300 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8300|exact decode_suffix_8300|exact decode_nonregister_8300|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8302 := match straight_drop 9063 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8302 : straight_drop 9062 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8302 decode_expr_8302) decode_tail_8302).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8302 : formal_typed_suffix_safe flat_memories 8302 decode_tail_8302.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8302 : has_register 8302 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8302 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8302 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8302 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8302|exact decode_suffix_8302|exact decode_nonregister_8302|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8304 := match straight_drop 9065 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8304 : straight_drop 9064 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8304 decode_expr_8304) decode_tail_8304).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8304 : formal_typed_suffix_safe flat_memories 8304 decode_tail_8304.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8304 : has_register 8304 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8304 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8304 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8304 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8304|exact decode_suffix_8304|exact decode_nonregister_8304|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8306 := match straight_drop 9067 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8306 : straight_drop 9066 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8306 decode_expr_8306) decode_tail_8306).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8306 : formal_typed_suffix_safe flat_memories 8306 decode_tail_8306.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8306 : has_register 8306 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8306 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8306 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8306 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8306|exact decode_suffix_8306|exact decode_nonregister_8306|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8308 := match straight_drop 9069 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8308 : straight_drop 9068 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8308 decode_expr_8308) decode_tail_8308).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8308 : formal_typed_suffix_safe flat_memories 8308 decode_tail_8308.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8308 : has_register 8308 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8308 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8308 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8308 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8308|exact decode_suffix_8308|exact decode_nonregister_8308|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8310 := match straight_drop 9071 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8310 : straight_drop 9070 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8310 decode_expr_8310) decode_tail_8310).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8310 : formal_typed_suffix_safe flat_memories 8310 decode_tail_8310.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8310 : has_register 8310 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8310 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8310 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8310 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8310|exact decode_suffix_8310|exact decode_nonregister_8310|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8312 := match straight_drop 9073 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8312 : straight_drop 9072 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8312 decode_expr_8312) decode_tail_8312).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8312 : formal_typed_suffix_safe flat_memories 8312 decode_tail_8312.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8312 : has_register 8312 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8312 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8312 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8312 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8312|exact decode_suffix_8312|exact decode_nonregister_8312|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8314 := match straight_drop 9075 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8314 : straight_drop 9074 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8314 decode_expr_8314) decode_tail_8314).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8314 : formal_typed_suffix_safe flat_memories 8314 decode_tail_8314.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8314 : has_register 8314 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8314 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8314 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8314 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8314|exact decode_suffix_8314|exact decode_nonregister_8314|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8316 := match straight_drop 9077 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8316 : straight_drop 9076 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8316 decode_expr_8316) decode_tail_8316).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8316 : formal_typed_suffix_safe flat_memories 8316 decode_tail_8316.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8316 : has_register 8316 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8316 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8316 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8316 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8316|exact decode_suffix_8316|exact decode_nonregister_8316|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8318 := match straight_drop 9079 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8318 : straight_drop 9078 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8318 decode_expr_8318) decode_tail_8318).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8318 : formal_typed_suffix_safe flat_memories 8318 decode_tail_8318.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8318 : has_register 8318 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8318 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8318 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8318 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8318|exact decode_suffix_8318|exact decode_nonregister_8318|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8320 := match straight_drop 9081 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8320 : straight_drop 9080 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8320 decode_expr_8320) decode_tail_8320).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8320 : formal_typed_suffix_safe flat_memories 8320 decode_tail_8320.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8320 : has_register 8320 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8320 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8320 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8320 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8320|exact decode_suffix_8320|exact decode_nonregister_8320|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8322 := match straight_drop 9083 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8322 : straight_drop 9082 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8322 decode_expr_8322) decode_tail_8322).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8322 : formal_typed_suffix_safe flat_memories 8322 decode_tail_8322.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8322 : has_register 8322 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8322 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8322 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8322 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8322|exact decode_suffix_8322|exact decode_nonregister_8322|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8324 := match straight_drop 9085 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8324 : straight_drop 9084 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8324 decode_expr_8324) decode_tail_8324).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8324 : formal_typed_suffix_safe flat_memories 8324 decode_tail_8324.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8324 : has_register 8324 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8324 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8324 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8324 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8324|exact decode_suffix_8324|exact decode_nonregister_8324|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8326 := match straight_drop 9087 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8326 : straight_drop 9086 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8326 decode_expr_8326) decode_tail_8326).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8326 : formal_typed_suffix_safe flat_memories 8326 decode_tail_8326.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8326 : has_register 8326 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8326 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8326 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8326 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8326|exact decode_suffix_8326|exact decode_nonregister_8326|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8328 := match straight_drop 9089 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8328 : straight_drop 9088 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8328 decode_expr_8328) decode_tail_8328).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8328 : formal_typed_suffix_safe flat_memories 8328 decode_tail_8328.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8328 : has_register 8328 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8328 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8328 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8328 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8328|exact decode_suffix_8328|exact decode_nonregister_8328|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8330 := match straight_drop 9091 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8330 : straight_drop 9090 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8330 decode_expr_8330) decode_tail_8330).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8330 : formal_typed_suffix_safe flat_memories 8330 decode_tail_8330.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8330 : has_register 8330 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8330 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8330 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8330 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8330|exact decode_suffix_8330|exact decode_nonregister_8330|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8332 := match straight_drop 9093 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8332 : straight_drop 9092 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8332 decode_expr_8332) decode_tail_8332).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8332 : formal_typed_suffix_safe flat_memories 8332 decode_tail_8332.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8332 : has_register 8332 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8332 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8332 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8332 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8332|exact decode_suffix_8332|exact decode_nonregister_8332|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8334 := match straight_drop 9095 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8334 : straight_drop 9094 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8334 decode_expr_8334) decode_tail_8334).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8334 : formal_typed_suffix_safe flat_memories 8334 decode_tail_8334.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8334 : has_register 8334 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8334 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8334 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8334 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8334|exact decode_suffix_8334|exact decode_nonregister_8334|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8336 := match straight_drop 9097 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8336 : straight_drop 9096 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8336 decode_expr_8336) decode_tail_8336).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8336 : formal_typed_suffix_safe flat_memories 8336 decode_tail_8336.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8336 : has_register 8336 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8336 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8336 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8336 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8336|exact decode_suffix_8336|exact decode_nonregister_8336|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8338 := match straight_drop 9099 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8338 : straight_drop 9098 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8338 decode_expr_8338) decode_tail_8338).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8338 : formal_typed_suffix_safe flat_memories 8338 decode_tail_8338.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8338 : has_register 8338 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8338 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8338 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8338 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8338|exact decode_suffix_8338|exact decode_nonregister_8338|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8340 := match straight_drop 9101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8340 : straight_drop 9100 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8340 decode_expr_8340) decode_tail_8340).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8340 : formal_typed_suffix_safe flat_memories 8340 decode_tail_8340.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8340 : has_register 8340 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8340 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8340 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8340 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8340|exact decode_suffix_8340|exact decode_nonregister_8340|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8342 := match straight_drop 9103 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8342 : straight_drop 9102 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8342 decode_expr_8342) decode_tail_8342).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8342 : formal_typed_suffix_safe flat_memories 8342 decode_tail_8342.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8342 : has_register 8342 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8342 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8342 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8342 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8342|exact decode_suffix_8342|exact decode_nonregister_8342|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8344 := match straight_drop 9105 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8344 : straight_drop 9104 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8344 decode_expr_8344) decode_tail_8344).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8344 : formal_typed_suffix_safe flat_memories 8344 decode_tail_8344.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8344 : has_register 8344 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8344 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8344 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8344 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8344|exact decode_suffix_8344|exact decode_nonregister_8344|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8346 := match straight_drop 9107 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8346 : straight_drop 9106 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8346 decode_expr_8346) decode_tail_8346).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8346 : formal_typed_suffix_safe flat_memories 8346 decode_tail_8346.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8346 : has_register 8346 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8346 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8346 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8346 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8346|exact decode_suffix_8346|exact decode_nonregister_8346|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8348 := match straight_drop 9109 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8348 : straight_drop 9108 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8348 decode_expr_8348) decode_tail_8348).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8348 : formal_typed_suffix_safe flat_memories 8348 decode_tail_8348.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8348 : has_register 8348 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8348 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8348 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8348 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8348|exact decode_suffix_8348|exact decode_nonregister_8348|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8350 := match straight_drop 9111 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8350 : straight_drop 9110 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8350 decode_expr_8350) decode_tail_8350).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8350 : formal_typed_suffix_safe flat_memories 8350 decode_tail_8350.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8350 : has_register 8350 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8350 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8350 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8350 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8350|exact decode_suffix_8350|exact decode_nonregister_8350|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8352 := match straight_drop 9113 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8352 : straight_drop 9112 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8352 decode_expr_8352) decode_tail_8352).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8352 : formal_typed_suffix_safe flat_memories 8352 decode_tail_8352.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8352 : has_register 8352 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8352 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8352 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8352 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8352|exact decode_suffix_8352|exact decode_nonregister_8352|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8354 := match straight_drop 9115 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8354 : straight_drop 9114 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8354 decode_expr_8354) decode_tail_8354).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8354 : formal_typed_suffix_safe flat_memories 8354 decode_tail_8354.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8354 : has_register 8354 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8354 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8354 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8354 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8354|exact decode_suffix_8354|exact decode_nonregister_8354|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8356 := match straight_drop 9117 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8356 : straight_drop 9116 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8356 decode_expr_8356) decode_tail_8356).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8356 : formal_typed_suffix_safe flat_memories 8356 decode_tail_8356.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8356 : has_register 8356 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8356 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8356 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8356 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8356|exact decode_suffix_8356|exact decode_nonregister_8356|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8358 := match straight_drop 9119 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8358 : straight_drop 9118 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8358 decode_expr_8358) decode_tail_8358).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8358 : formal_typed_suffix_safe flat_memories 8358 decode_tail_8358.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8358 : has_register 8358 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8358 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8358 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8358 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8358|exact decode_suffix_8358|exact decode_nonregister_8358|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8360 := match straight_drop 9121 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8360 : straight_drop 9120 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8360 decode_expr_8360) decode_tail_8360).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8360 : formal_typed_suffix_safe flat_memories 8360 decode_tail_8360.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8360 : has_register 8360 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8360 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8360 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8360 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8360|exact decode_suffix_8360|exact decode_nonregister_8360|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8361 := match straight_drop 9122 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8361 : straight_drop 9121 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8361 decode_expr_8361) decode_tail_8361).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8361 : formal_typed_suffix_safe flat_memories 8361 decode_tail_8361.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8361 : has_register 8361 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8361 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8361 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8361 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8361|exact decode_suffix_8361|exact decode_nonregister_8361|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8362 := match straight_drop 9123 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8362 : straight_drop 9122 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8362 decode_expr_8362) decode_tail_8362).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8362 : formal_typed_suffix_safe flat_memories 8362 decode_tail_8362.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8362 : has_register 8362 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8362 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8362 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8362 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8362|exact decode_suffix_8362|exact decode_nonregister_8362|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8363 := match straight_drop 9124 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8363 : straight_drop 9123 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8363 decode_expr_8363) decode_tail_8363).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8363 : formal_typed_suffix_safe flat_memories 8363 decode_tail_8363.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8363 : has_register 8363 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8363 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8363 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8363 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8363|exact decode_suffix_8363|exact decode_nonregister_8363|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8364 := match straight_drop 9125 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8364 : straight_drop 9124 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8364 decode_expr_8364) decode_tail_8364).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8364 : formal_typed_suffix_safe flat_memories 8364 decode_tail_8364.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8364 : has_register 8364 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8364 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8364 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8364 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8364|exact decode_suffix_8364|exact decode_nonregister_8364|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8365 := match straight_drop 9126 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8365 : straight_drop 9125 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8365 decode_expr_8365) decode_tail_8365).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8365 : formal_typed_suffix_safe flat_memories 8365 decode_tail_8365.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8365 : has_register 8365 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8365 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8365 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8365 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8365|exact decode_suffix_8365|exact decode_nonregister_8365|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8366 := match straight_drop 9127 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8366 : straight_drop 9126 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8366 decode_expr_8366) decode_tail_8366).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8366 : formal_typed_suffix_safe flat_memories 8366 decode_tail_8366.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8366 : has_register 8366 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8366 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8366 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8366 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8366|exact decode_suffix_8366|exact decode_nonregister_8366|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8367 := match straight_drop 9128 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8367 : straight_drop 9127 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8367 decode_expr_8367) decode_tail_8367).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8367 : formal_typed_suffix_safe flat_memories 8367 decode_tail_8367.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8367 : has_register 8367 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8367 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8367 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8367 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8367|exact decode_suffix_8367|exact decode_nonregister_8367|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8368 := match straight_drop 9129 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8368 : straight_drop 9128 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8368 decode_expr_8368) decode_tail_8368).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8368 : formal_typed_suffix_safe flat_memories 8368 decode_tail_8368.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8368 : has_register 8368 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8368 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8368 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8368 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8368|exact decode_suffix_8368|exact decode_nonregister_8368|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8369 := match straight_drop 9130 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8369 : straight_drop 9129 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8369 decode_expr_8369) decode_tail_8369).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8369 : formal_typed_suffix_safe flat_memories 8369 decode_tail_8369.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8369 : has_register 8369 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8369 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8369 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8369 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8369|exact decode_suffix_8369|exact decode_nonregister_8369|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8370 := match straight_drop 9131 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8370 : straight_drop 9130 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8370 decode_expr_8370) decode_tail_8370).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8370 : formal_typed_suffix_safe flat_memories 8370 decode_tail_8370.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8370 : has_register 8370 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8370 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8370 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8370 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8370|exact decode_suffix_8370|exact decode_nonregister_8370|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8371 := match straight_drop 9132 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8371 : straight_drop 9131 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8371 decode_expr_8371) decode_tail_8371).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8371 : formal_typed_suffix_safe flat_memories 8371 decode_tail_8371.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8371 : has_register 8371 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8371 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8371 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8371 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8371|exact decode_suffix_8371|exact decode_nonregister_8371|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8372 := match straight_drop 9133 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8372 : straight_drop 9132 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8372 decode_expr_8372) decode_tail_8372).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8372 : formal_typed_suffix_safe flat_memories 8372 decode_tail_8372.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8372 : has_register 8372 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8372 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8372 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8372 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8372|exact decode_suffix_8372|exact decode_nonregister_8372|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8373 := match straight_drop 9134 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8373 : straight_drop 9133 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8373 decode_expr_8373) decode_tail_8373).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8373 : formal_typed_suffix_safe flat_memories 8373 decode_tail_8373.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8373 : has_register 8373 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8373 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8373 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8373 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8373|exact decode_suffix_8373|exact decode_nonregister_8373|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8374 := match straight_drop 9135 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8374 : straight_drop 9134 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8374 decode_expr_8374) decode_tail_8374).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8374 : formal_typed_suffix_safe flat_memories 8374 decode_tail_8374.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8374 : has_register 8374 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8374 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8374 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8374 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8374|exact decode_suffix_8374|exact decode_nonregister_8374|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8375 := match straight_drop 9136 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8375 : straight_drop 9135 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8375 decode_expr_8375) decode_tail_8375).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8375 : formal_typed_suffix_safe flat_memories 8375 decode_tail_8375.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8375 : has_register 8375 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8375 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8375 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8375 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8375|exact decode_suffix_8375|exact decode_nonregister_8375|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8376 := match straight_drop 9137 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8376 : straight_drop 9136 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8376 decode_expr_8376) decode_tail_8376).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8376 : formal_typed_suffix_safe flat_memories 8376 decode_tail_8376.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8376 : has_register 8376 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8376 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8376 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8376 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8376|exact decode_suffix_8376|exact decode_nonregister_8376|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8377 := match straight_drop 9138 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8377 : straight_drop 9137 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8377 decode_expr_8377) decode_tail_8377).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8377 : formal_typed_suffix_safe flat_memories 8377 decode_tail_8377.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8377 : has_register 8377 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8377 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8377 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8377 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8377|exact decode_suffix_8377|exact decode_nonregister_8377|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8378 := match straight_drop 9139 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8378 : straight_drop 9138 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8378 decode_expr_8378) decode_tail_8378).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8378 : formal_typed_suffix_safe flat_memories 8378 decode_tail_8378.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8378 : has_register 8378 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8378 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8378 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8378 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8378|exact decode_suffix_8378|exact decode_nonregister_8378|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8379 := match straight_drop 9140 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8379 : straight_drop 9139 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8379 decode_expr_8379) decode_tail_8379).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8379 : formal_typed_suffix_safe flat_memories 8379 decode_tail_8379.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8379 : has_register 8379 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8379 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8379 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8379 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8379|exact decode_suffix_8379|exact decode_nonregister_8379|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8380 := match straight_drop 9141 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8380 : straight_drop 9140 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8380 decode_expr_8380) decode_tail_8380).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8380 : formal_typed_suffix_safe flat_memories 8380 decode_tail_8380.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8380 : has_register 8380 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8380 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8380 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8380 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8380|exact decode_suffix_8380|exact decode_nonregister_8380|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8381 := match straight_drop 9142 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8381 : straight_drop 9141 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8381 decode_expr_8381) decode_tail_8381).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8381 : formal_typed_suffix_safe flat_memories 8381 decode_tail_8381.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8381 : has_register 8381 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8381 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8381 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8381 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8381|exact decode_suffix_8381|exact decode_nonregister_8381|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8382 := match straight_drop 9143 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8382 : straight_drop 9142 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8382 decode_expr_8382) decode_tail_8382).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8382 : formal_typed_suffix_safe flat_memories 8382 decode_tail_8382.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8382 : has_register 8382 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8382 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8382 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8382 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8382|exact decode_suffix_8382|exact decode_nonregister_8382|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8383 := match straight_drop 9144 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8383 : straight_drop 9143 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8383 decode_expr_8383) decode_tail_8383).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8383 : formal_typed_suffix_safe flat_memories 8383 decode_tail_8383.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8383 : has_register 8383 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8383 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8383 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8383 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8383|exact decode_suffix_8383|exact decode_nonregister_8383|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8384 := match straight_drop 9145 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8384 : straight_drop 9144 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8384 decode_expr_8384) decode_tail_8384).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8384 : formal_typed_suffix_safe flat_memories 8384 decode_tail_8384.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8384 : has_register 8384 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8384 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8384 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8384 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8384|exact decode_suffix_8384|exact decode_nonregister_8384|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8385 := match straight_drop 9146 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8385 : straight_drop 9145 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8385 decode_expr_8385) decode_tail_8385).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8385 : formal_typed_suffix_safe flat_memories 8385 decode_tail_8385.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8385 : has_register 8385 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8385 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8385 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8385 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8385|exact decode_suffix_8385|exact decode_nonregister_8385|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8386 := match straight_drop 9147 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8386 : straight_drop 9146 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8386 decode_expr_8386) decode_tail_8386).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8386 : formal_typed_suffix_safe flat_memories 8386 decode_tail_8386.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8386 : has_register 8386 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8386 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8386 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8386 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8386|exact decode_suffix_8386|exact decode_nonregister_8386|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8387 := match straight_drop 9148 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8387 : straight_drop 9147 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8387 decode_expr_8387) decode_tail_8387).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8387 : formal_typed_suffix_safe flat_memories 8387 decode_tail_8387.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8387 : has_register 8387 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8387 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8387 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8387 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8387|exact decode_suffix_8387|exact decode_nonregister_8387|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8388 := match straight_drop 9149 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8388 : straight_drop 9148 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8388 decode_expr_8388) decode_tail_8388).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8388 : formal_typed_suffix_safe flat_memories 8388 decode_tail_8388.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8388 : has_register 8388 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8388 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8388 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8388 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8388|exact decode_suffix_8388|exact decode_nonregister_8388|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8389 := match straight_drop 9150 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8389 : straight_drop 9149 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8389 decode_expr_8389) decode_tail_8389).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8389 : formal_typed_suffix_safe flat_memories 8389 decode_tail_8389.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8389 : has_register 8389 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8389 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8389 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8389 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8389|exact decode_suffix_8389|exact decode_nonregister_8389|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8390 := match straight_drop 9151 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8390 : straight_drop 9150 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8390 decode_expr_8390) decode_tail_8390).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8390 : formal_typed_suffix_safe flat_memories 8390 decode_tail_8390.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8390 : has_register 8390 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8390 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8390 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8390 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8390|exact decode_suffix_8390|exact decode_nonregister_8390|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8391 := match straight_drop 9152 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8391 : straight_drop 9151 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8391 decode_expr_8391) decode_tail_8391).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8391 : formal_typed_suffix_safe flat_memories 8391 decode_tail_8391.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8391 : has_register 8391 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8391 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8391 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8391 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8391|exact decode_suffix_8391|exact decode_nonregister_8391|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8392 := match straight_drop 9153 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8392 : straight_drop 9152 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8392 decode_expr_8392) decode_tail_8392).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8392 : formal_typed_suffix_safe flat_memories 8392 decode_tail_8392.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8392 : has_register 8392 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8392 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8392 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8392 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8392|exact decode_suffix_8392|exact decode_nonregister_8392|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8393 := match straight_drop 9154 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8393 : straight_drop 9153 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8393 decode_expr_8393) decode_tail_8393).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8393 : formal_typed_suffix_safe flat_memories 8393 decode_tail_8393.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8393 : has_register 8393 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8393 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8393 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8393 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8393|exact decode_suffix_8393|exact decode_nonregister_8393|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8394 := match straight_drop 9155 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8394 : straight_drop 9154 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8394 decode_expr_8394) decode_tail_8394).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8394 : formal_typed_suffix_safe flat_memories 8394 decode_tail_8394.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8394 : has_register 8394 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8394 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8394 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8394 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8394|exact decode_suffix_8394|exact decode_nonregister_8394|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8395 := match straight_drop 9156 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8395 : straight_drop 9155 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8395 decode_expr_8395) decode_tail_8395).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8395 : formal_typed_suffix_safe flat_memories 8395 decode_tail_8395.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8395 : has_register 8395 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8395 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8395 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8395 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8395|exact decode_suffix_8395|exact decode_nonregister_8395|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8396 := match straight_drop 9157 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8396 : straight_drop 9156 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8396 decode_expr_8396) decode_tail_8396).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8396 : formal_typed_suffix_safe flat_memories 8396 decode_tail_8396.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8396 : has_register 8396 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8396 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8396 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8396 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8396|exact decode_suffix_8396|exact decode_nonregister_8396|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8397 := match straight_drop 9158 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8397 : straight_drop 9157 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8397 decode_expr_8397) decode_tail_8397).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8397 : formal_typed_suffix_safe flat_memories 8397 decode_tail_8397.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8397 : has_register 8397 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8397 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8397 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8397 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8397|exact decode_suffix_8397|exact decode_nonregister_8397|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8398 := match straight_drop 9159 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8398 : straight_drop 9158 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8398 decode_expr_8398) decode_tail_8398).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8398 : formal_typed_suffix_safe flat_memories 8398 decode_tail_8398.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8398 : has_register 8398 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8398 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8398 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8398 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8398|exact decode_suffix_8398|exact decode_nonregister_8398|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8399 := match straight_drop 9160 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8399 : straight_drop 9159 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8399 decode_expr_8399) decode_tail_8399).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8399 : formal_typed_suffix_safe flat_memories 8399 decode_tail_8399.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8399 : has_register 8399 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8399 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8399 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8399 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8399|exact decode_suffix_8399|exact decode_nonregister_8399|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8400 := match straight_drop 9161 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8400 : straight_drop 9160 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8400 decode_expr_8400) decode_tail_8400).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8400 : formal_typed_suffix_safe flat_memories 8400 decode_tail_8400.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8400 : has_register 8400 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8400 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8400 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8400 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8400|exact decode_suffix_8400|exact decode_nonregister_8400|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8401 := match straight_drop 9162 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8401 : straight_drop 9161 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8401 decode_expr_8401) decode_tail_8401).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8401 : formal_typed_suffix_safe flat_memories 8401 decode_tail_8401.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8401 : has_register 8401 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8401 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8401 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8401 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8401|exact decode_suffix_8401|exact decode_nonregister_8401|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8402 := match straight_drop 9163 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8402 : straight_drop 9162 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8402 decode_expr_8402) decode_tail_8402).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8402 : formal_typed_suffix_safe flat_memories 8402 decode_tail_8402.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8402 : has_register 8402 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8402 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8402 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8402 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8402|exact decode_suffix_8402|exact decode_nonregister_8402|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8403 := match straight_drop 9164 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8403 : straight_drop 9163 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8403 decode_expr_8403) decode_tail_8403).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8403 : formal_typed_suffix_safe flat_memories 8403 decode_tail_8403.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8403 : has_register 8403 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8403 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8403 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8403 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8403|exact decode_suffix_8403|exact decode_nonregister_8403|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8404 := match straight_drop 9165 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8404 : straight_drop 9164 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8404 decode_expr_8404) decode_tail_8404).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8404 : formal_typed_suffix_safe flat_memories 8404 decode_tail_8404.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8404 : has_register 8404 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8404 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8404 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8404 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8404|exact decode_suffix_8404|exact decode_nonregister_8404|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8405 := match straight_drop 9166 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8405 : straight_drop 9165 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8405 decode_expr_8405) decode_tail_8405).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8405 : formal_typed_suffix_safe flat_memories 8405 decode_tail_8405.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8405 : has_register 8405 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8405 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8405 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8405 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8405|exact decode_suffix_8405|exact decode_nonregister_8405|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8406 := match straight_drop 9167 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8406 : straight_drop 9166 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8406 decode_expr_8406) decode_tail_8406).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8406 : formal_typed_suffix_safe flat_memories 8406 decode_tail_8406.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8406 : has_register 8406 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8406 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8406 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8406 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8406|exact decode_suffix_8406|exact decode_nonregister_8406|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8407 := match straight_drop 9168 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8407 : straight_drop 9167 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8407 decode_expr_8407) decode_tail_8407).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8407 : formal_typed_suffix_safe flat_memories 8407 decode_tail_8407.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8407 : has_register 8407 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8407 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8407 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8407 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8407|exact decode_suffix_8407|exact decode_nonregister_8407|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8408 := match straight_drop 9169 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8408 : straight_drop 9168 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8408 decode_expr_8408) decode_tail_8408).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8408 : formal_typed_suffix_safe flat_memories 8408 decode_tail_8408.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8408 : has_register 8408 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8408 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8408 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8408 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8408|exact decode_suffix_8408|exact decode_nonregister_8408|exact Eval|exact Typed|exact Step].
Qed.
Definition decode_tail_8409 := match straight_drop 9170 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_8409 : straight_drop 9169 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8409 decode_expr_8409) decode_tail_8409).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_8409 : formal_typed_suffix_safe flat_memories 8409 decode_tail_8409.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_8409 : has_register 8409 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_8409 invalid old current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_8409 old old = Some value ->
 type_of_val value = Gtyp (Fuint 2) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 8409 result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact decode_position_8409|exact decode_suffix_8409|exact decode_nonregister_8409|exact Eval|exact Typed|exact Step].
Qed.
Print Assumptions decode_node_8409.
