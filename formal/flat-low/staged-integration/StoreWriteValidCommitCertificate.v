Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalStatementSegments ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation RegisterCommitCertificate JointRegisterExpressionCertificates FormalConcreteRegisterMuxCommit FormalConcreteRegisterUnaryCommit FormalConcreteRegisterDirectCommit ConcreteExpressionClosure.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition joint_register_update_8028 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8027))).
Definition joint_register_8028_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 1)) (@Eref VarOrder.T (@Eid VarOrder.T 64)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 8028)))).
Definition joint_register_8028_decl := match straight_drop 8535 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_8028_tail := match straight_drop 9006 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition joint_register_8028_mid := take_statements 470 joint_register_8028_decl.
Lemma joint_register_8028_position : straight_drop 8534 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 8028 joint_register_8028_reg) joint_register_8028_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_8028_split : joint_register_8028_decl = statement_append joint_register_8028_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 8028) joint_register_update_8028) joint_register_8028_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma joint_register_8028_straight : straight_statements joint_register_8028_mid.
Proof. vm_compute. exact I. Qed.
Lemma joint_register_8028_mid_safe : formal_typed_suffix_safe flat_memories 8028 joint_register_8028_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_8028_tail_safe : formal_typed_suffix_safe flat_memories 8028 joint_register_8028_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma joint_register_8028_identity : register_identity_b 8028 flat_statements.
Proof. vm_compute. reflexivity. Qed.
