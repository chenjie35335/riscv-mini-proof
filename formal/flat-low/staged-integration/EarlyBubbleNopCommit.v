Require Import CoreSocModel ComparisonNodes FrontInstructionNopCommit FormalInstructionResetConstants PipelineBubbleNormalCommit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem early_bubble_nop_same_commit invalid s0 s1 s2 result bit fetched held old_bubble :
 VM.find 7796 s0 = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 7944 s2 = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 75 s0 = Some fetched -> type_of_val fetched = Gtyp (Fuint 32) ->
 VM.find 7748 s0 = Some held -> type_of_val held = Gtyp (Fuint 32) ->
 VM.find 7945 s2 = Some old_bubble -> type_of_val old_bubble = Gtyp (Fuint 1) ->
 VM.find 7799 s1 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 65 s2 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7945 result = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7748 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Kill BubbleSource Fetched FetchedType Held HeldType OldBubble BubbleType Advance Reset S1 S2 Commit Bubble.
 pose proof (pipeline_bubble_7945_normal_commit invalid s2 s2 result old_bubble bit
 OldBubble BubbleType Reset BubbleSource Commit) as NewBubble.
 rewrite Bubble in NewBubble. inversion NewBubble; subst bit.
 exact (front_instruction_nop_commit_after_two invalid s0 s1 s2 result fetched held
 Kill Fetched FetchedType Held HeldType Advance Reset S1 S2 Commit).
Qed.
Print Assumptions early_bubble_nop_same_commit.
