Require Import CoreSocModel ComparisonNodes FormalRFEnableShape NormalizedBit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem concrete_x0_enable_is_bit invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 (exists width bits, VM.find 784 result = Some (Gval (Fuint width) bits)) ->
 exists bit, VM.find 784 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Step [width [bits Concrete]].
 destruct (rf_input_enable_normalized invalid old current result Step) as [value [Lookup Normal]].
 rewrite Concrete in Lookup. inversion Lookup; subst value.
 inversion Normal; subst. eexists; exact Concrete.
Qed.
Print Assumptions concrete_x0_enable_is_bit.
