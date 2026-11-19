Require Import CommitPCSelectionNodes ExactWordMux StagedRegisterHold ExceptionPCSourceRegisters.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition commit_pc_next stall advance ex ew := mux_word stall ew (mux_word advance ex ew).
Lemma commit_pc_next_size stall advance ex ew : size (commit_pc_next stall advance ex ew) = 32%nat.
Proof. apply mux_word_size. Qed.
Theorem commit_pc_after_two invalid old middle result advance stall ex ew :
 VM.find 7749 old = Some (Gval (Fuint 32) ex) ->
 VM.find 7751 old = Some (Gval (Fuint 32) ew) ->
 VM.find 7855 old = Some (Gval (Fuint 1) [::advance]) ->
 VM.find 7852 middle = Some (Gval (Fuint 1) [::stall]) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some middle ->
 formal_value_iter invalid flat_memories middle false middle flat_statements = Some result ->
 VM.find 7877 result = Some (Gval (Fuint 32) (commit_pc_next stall advance ex ew)).
Proof.
 intros Ex Ew Advance Stall First Second.
 assert (Selected : VM.find 7860 middle = Some (Gval (Fuint 32) (mux_word advance ex ew))).
 { apply (commit_pc_source_node_7860 invalid old old middle (Gval (Fuint 32) (mux_word advance ex ew)));
   [exact (exact_word_mux flat_memories old 7855 7749 7751 advance ex ew Advance Ex Ew)|reflexivity|exact First]. }
 assert (Held : VM.find 7751 middle = Some (Gval (Fuint 32) ew)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories old old middle flat_statements 7751
   exception_pc_implementation_register First). exact Ew. }
 apply (commit_pc_source_node_7877 invalid middle middle result (Gval (Fuint 32) (commit_pc_next stall advance ex ew)));
 [|reflexivity|exact Second].
 exact (exact_word_mux flat_memories middle 7852 7751 7860 stall ew (mux_word advance ex ew) Stall Held Selected).
Qed.
Print Assumptions commit_pc_after_two.
