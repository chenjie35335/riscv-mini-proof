Require Import CoreSocModel ComparisonNodes FormalRFInputConnections FormalExceptionInput FormalStallConnections X0RegisterInputConnections FormalDeclaredConnection.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem x0_connection_output_33 invalid old current result :
 (exists width bits, VM.find 9216 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 33 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply (declared_connection_value 10 flat_statements stall_declared_33 stall_middle_33 stall_after_33
 33 9216 1 (Gval (Fuint width) bits) _ invalid flat_memories old current result);
 [exact stall_declaration_33|exact stall_split_33|exact stall_straight_33|
 exact stall_middle_safe_33|exact stall_after_safe_33|exact stall_connection_nonregister_33|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_40 invalid old current result :
 (exists width bits, VM.find 9218 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 40 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply (declared_connection_value 17 flat_statements stall_declared_40 stall_middle_40 stall_after_40
 40 9218 1 (Gval (Fuint width) bits) _ invalid flat_memories old current result);
 [exact stall_declaration_40|exact stall_split_40|exact stall_straight_40|
 exact stall_middle_safe_40|exact stall_after_safe_40|exact stall_connection_nonregister_40|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_74 invalid old current result :
 (exists width bits, VM.find 33 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 74 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply (declared_connection_value 51 flat_statements stall_declared_74 stall_middle_74 stall_after_74
 74 33 1 (Gval (Fuint width) bits) _ invalid flat_memories old current result);
 [exact stall_declaration_74|exact stall_split_74|exact stall_straight_74|
 exact stall_middle_safe_74|exact stall_after_safe_74|exact stall_connection_nonregister_74|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_81 invalid old current result :
 (exists width bits, VM.find 40 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 81 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply (declared_connection_value 58 flat_statements stall_declared_81 stall_middle_81 stall_after_81
 81 40 1 (Gval (Fuint width) bits) _ invalid flat_memories old current result);
 [exact stall_declaration_81|exact stall_split_81|exact stall_straight_81|
 exact stall_middle_safe_81|exact stall_after_safe_81|exact stall_connection_nonregister_81|reflexivity|exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_118 invalid old current result :
 (exists width bits, VM.find 7758 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 118 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 3.
 exact (x0_register_input_concrete_118 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_122 invalid old current result :
 (exists width bits, VM.find 7752 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 122 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 32.
 exact (x0_register_input_concrete_122 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_123 invalid old current result :
 (exists width bits, VM.find 7750 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 123 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 32.
 exact (x0_register_input_concrete_123 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_124 invalid old current result :
 (exists width bits, VM.find 7759 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 124 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 exact (x0_register_input_concrete_124 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_125 invalid old current result :
 (exists width bits, VM.find 7754 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 125 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 2.
 exact (x0_register_input_concrete_125 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_126 invalid old current result :
 (exists width bits, VM.find 7755 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 126 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 3.
 exact (x0_register_input_concrete_126 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_127 invalid old current result :
 (exists width bits, VM.find 7760 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 127 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 exact (x0_register_input_concrete_127 invalid old current result width bits Source Step).
Qed.
Theorem x0_connection_output_128 invalid old current result :
 (exists width bits, VM.find 442 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 128 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply exception_input_connection_128; [exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_784 invalid old current result :
 (exists width bits, VM.find 7941 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 784 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 1.
 eexists. eapply rf_input_connection_784; [exact Source|reflexivity|exact Step].
Qed.
Theorem x0_connection_output_785 invalid old current result :
 (exists width bits, VM.find 7805 old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find 785 result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists 5.
 eexists. eapply rf_input_connection_785; [exact Source|reflexivity|exact Step].
Qed.
Print Assumptions x0_connection_output_785.
