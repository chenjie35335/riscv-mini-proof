Require Import FormalDeclaredWireCheck FormalDeclaredConnectionObservation FormalDeclaredConnection FormalTypedNodeEquation ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Theorem declared_wire_checked_observation mm stmts count distance node source width invalid old current result :
 declared_wire_check mm stmts count distance node source width = true ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 exists source_value value, VM.find source old=Some source_value /\ adapt_hvalue_as_type source_value (Gtyp(Fuint width))=Some value /\ VM.find node result=Some value.
Proof.
 unfold declared_wire_check.
 destruct (straight_drop count stmts) as [[|st decl]|] eqn:Position; try discriminate.
 destruct st as [|declared typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try discriminate.
 destruct typ as [ground|element length|fields]; try discriminate.
 destruct ground; try discriminate.
 destruct (straight_drop distance decl) as [[|st tail]|] eqn:Connection; try discriminate.
 destruct st as [|name typ|name reg|name mem|name mi|name expr|lhs rhs|reference|cond yes no]; try discriminate.
 destruct lhs as [target|ref field|ref index|ref index]; try discriminate.
 destruct rhs as [ty bits|cast arg|op arg|op left right|cond yes no|cond arg|reference]; try discriminate.
 destruct reference as [actual_source|ref field|ref index|ref index]; try discriminate.
 move/andP => [/eqP Declared /andP [/eqP Width /andP [/eqP Target /andP [/eqP Source /andP [Different /andP [/eqP Nonreg /andP [Mid Tail]]]]]]].
 subst declared n target actual_source.
 intro Step.
 destruct (declared_wire_drop_split distance decl _ Connection) as [Split Straight].
 eapply declared_connection_observation;
 [exact Position|exact Split|exact Straight|apply formal_typed_suffix_safe_b_sound;exact Mid|apply formal_typed_suffix_safe_b_sound;exact Tail|exact Nonreg|exact Different|exact Step].
Qed.
