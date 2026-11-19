Require Import FormalNonwriterStorageFrames NonwriterStorageCertificate ScalarNodeFrames CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ReadonlyStorageFrames ReadonlyStorageCertificate.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_commit_prefix := take_statements 10121 flat_statements.
Definition data_commit_tail := match straight_drop 10122 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_commit_source := @Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 9234)).
Definition data_commit_sink := @Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 4.
Lemma data_commit_split : flat_statements = statement_append data_commit_prefix
 (@Qcons VarOrder.T (@Sfcnct VarOrder.T data_commit_sink data_commit_source) data_commit_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_commit_prefix_straight : straight_statements data_commit_prefix.
Proof. vm_compute. exact I. Qed.
Print Assumptions data_commit_split.
Lemma data_commit_prefix_safe : nonwriter_suffix_safe flat_memories 9179 data_commit_prefix.
Proof. apply nonwriter_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_commit_tail_safe : nonwriter_suffix_safe flat_memories 9179 data_commit_tail.
Proof. apply nonwriter_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Print Assumptions data_commit_prefix_safe.
Print Assumptions data_commit_tail_safe.
