Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_update_8004 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8003))).
Definition joint_register_8004_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8004)))).
Definition joint_register_8004_decl := match straight_drop 8511 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_8004_tail := match straight_drop 9003 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_8004_mid := take_statements 491 joint_register_8004_decl.
Lemma joint_register_8004_position : straight_drop 8510 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 8004 joint_register_8004_reg) joint_register_8004_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_8004_split : joint_register_8004_decl = statement_append joint_register_8004_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8004) joint_register_update_8004) joint_register_8004_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_8004_straight : straight_statements joint_register_8004_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_8004_mid_safe : formal_typed_suffix_safe flat_memories 8004 joint_register_8004_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_8004_tail_safe : formal_typed_suffix_safe flat_memories 8004 joint_register_8004_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_8004_identity : register_identity_b 8004 flat_statements.
Proof. vm_compute. reflexivity. Qed.
