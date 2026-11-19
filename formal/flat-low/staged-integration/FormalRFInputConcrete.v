Require Import FormalRFInputConnections FormalRFDataConnection FormalRFResetPropagation.
From nbits Require Import NBits.
Require Import FormalDeclaredUnaryConnection.
Require Import FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation CoreSocModel ComparisonNodes RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Theorem rf_input_enable_concrete invalid old current result bit :
 VM.find 7941 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 784 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Source Step. apply (rf_input_connection_784 invalid old current result (Gval (Fuint 1) [::bit]) (Gval (Fuint 1) [::bit]));
 [exact Source|destruct bit; reflexivity|exact Step].
Qed.
Theorem rf_input_address_concrete invalid old current result bits :
 size bits = 5%nat -> VM.find 7805 old = Some (Gval (Fuint 5) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 785 result = Some (Gval (Fuint 5) bits).
Proof.
 intros Size Source Step. apply (rf_input_connection_785 invalid old current result (Gval (Fuint 5) bits) (Gval (Fuint 5) bits));
 [exact Source|apply sized_uint_adapt_identity; exact Size|exact Step].
Qed.
Theorem rf_input_data_concrete invalid old current result width bits :
 (31 < width)%nat -> VM.find 7937 old = Some (Gval (Fuint width) bits) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists word, VM.find 786 result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Source Step.
 exists (zext_to 32 (take 32 (take 32 bits))).
 apply (rf_input_connection_786 invalid old current result (Gval (Fuint 32) (take 32 bits)) _);
 [|reflexivity|exact Step].
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
 cbn [eval_unop]. rewrite Bound leq0n. cbn [andb]. rewrite subn0 drop0. reflexivity.
Qed.
Print Assumptions rf_input_data_concrete.
