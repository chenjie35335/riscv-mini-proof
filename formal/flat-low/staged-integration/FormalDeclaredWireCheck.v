Require Import FormalDeclaredConnection FormalTypedNodeEquation ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma declared_wire_drop_split count stmts suffix :
 straight_drop count stmts = Some suffix ->
 stmts = statement_append (take_statements count stmts) suffix /\ straight_statements (take_statements count stmts).
Proof.
 revert stmts. induction count as [|count IH]; intros stmts Drop.
 - inversion Drop; subst. split; [reflexivity|exact I].
 - destruct stmts as [|st tail]; [discriminate|].
   destruct st; try discriminate.
   all: cbn [straight_drop] in Drop.
   all: destruct (IH tail Drop) as [Split Straight].
   all: cbn [take_statements statement_append straight_statements].
   all: split; [rewrite <- Split;reflexivity|exact Straight].
Qed.
Definition declared_wire_check mm stmts count distance (node source : VarOrder.T) width : bool :=
 match straight_drop count stmts with
 | Some (Qcons (Swire declared (Gtyp (Fuint actual_width))) decl) =>
   match straight_drop distance decl with
   | Some (Qcons (Sfcnct (Eid target) (Eref (Eid actual_source))) tail) =>
    (declared == node) && ((actual_width == width) && ((target == node) &&
    ((actual_source == source) && ((node != source) && ((has_register node stmts == false) &&
    (formal_typed_suffix_safe_b mm node (take_statements distance decl) && formal_typed_suffix_safe_b mm node tail))))))
   | _ => false end
 | _ => false end.
Theorem declared_wire_checked_value mm stmts count distance node source width source_value value invalid old current result :
 declared_wire_check mm stmts count distance node source width = true ->
 VM.find source old = Some source_value ->
 adapt_hvalue_as_type source_value (Gtyp (Fuint width)) = Some value ->
 formal_value_iter invalid mm old false current stmts = Some result ->
 VM.find node result = Some value.
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
 intros Input Adapt Step.
 destruct (declared_wire_drop_split distance decl _ Connection) as [Split Straight].
 eapply declared_connection_value;
 [exact Position|exact Split|exact Straight|apply formal_typed_suffix_safe_b_sound;exact Mid|apply formal_typed_suffix_safe_b_sound;exact Tail|exact Nonreg|exact Different|exact Input|exact Adapt|exact Step].
Qed.
