Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_update_7924 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 80))).
Definition joint_register_7924_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 4)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7924)))).
Definition joint_register_7924_decl := match straight_drop 8431 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7924_tail := match straight_drop 8869 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_7924_mid := take_statements 437 joint_register_7924_decl.
Lemma joint_register_7924_position : straight_drop 8430 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7924 joint_register_7924_reg) joint_register_7924_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7924_split : joint_register_7924_decl = statement_append joint_register_7924_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7924) joint_register_update_7924) joint_register_7924_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_7924_straight : straight_statements joint_register_7924_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_7924_mid_safe : formal_typed_suffix_safe flat_memories 7924 joint_register_7924_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7924_tail_safe : formal_typed_suffix_safe flat_memories 7924 joint_register_7924_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_7924_identity : register_identity_b 7924 flat_statements.
Proof. vm_compute. reflexivity. Qed.
