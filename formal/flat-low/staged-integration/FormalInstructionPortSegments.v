Require Import FormalDeclaredConnection ScalarNodeFrames CoreSocModel ComparisonNodes RegisterInvariants FormalStatementSegments MemoryWriteFrames MemorySuffixCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition instruction_port_decl_stmt := (@Smem VarOrder.T 9176 (@mk_fmem VarOrder.T 9177 (Gtyp (Fuint 32)) 16 [:: (@mk_mem_port VarOrder.T 0 0 1 2 3)] [::] 0 1 undefined)).
Definition instruction_port_decl_tail := match straight_drop 10008 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_port_decl_position : straight_drop 10007 flat_statements = Some (Qcons instruction_port_decl_stmt instruction_port_decl_tail).
Proof. vm_compute. reflexivity. Qed.
Definition instruction_port_address_stmt := (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 0) (@Eref VarOrder.T (@Eid VarOrder.T 9219))).
Definition instruction_port_address_tail := match straight_drop 10101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_port_address_position : straight_drop 10100 flat_statements = Some (Qcons instruction_port_address_stmt instruction_port_address_tail).
Proof. vm_compute. reflexivity. Qed.
Definition instruction_port_enable_stmt := (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 1) (@Econst VarOrder.T (Fuint 1) [::true])).
Definition instruction_port_enable_tail := match straight_drop 10102 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_port_enable_position : straight_drop 10101 flat_statements = Some (Qcons instruction_port_enable_stmt instruction_port_enable_tail).
Proof. vm_compute. reflexivity. Qed.
Definition instruction_port_clock_stmt := (@Sfcnct VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 2) (@Eref VarOrder.T (@Eid VarOrder.T 0))).
Definition instruction_port_clock_tail := match straight_drop 10103 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_port_clock_position : straight_drop 10102 flat_statements = Some (Qcons instruction_port_clock_stmt instruction_port_clock_tail).
Proof. vm_compute. reflexivity. Qed.
Definition instruction_port_read_stmt := (@Sfcnct VarOrder.T (@Eid VarOrder.T 9220) (@Eref VarOrder.T (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4))).
Definition instruction_port_read_tail := match straight_drop 10125 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma instruction_port_read_position : straight_drop 10124 flat_statements = Some (Qcons instruction_port_read_stmt instruction_port_read_tail).
Proof. vm_compute. reflexivity. Qed.
Definition instruction_port_before_address := take_statements 92 instruction_port_decl_tail.
Lemma instruction_port_before_address_split : instruction_port_decl_tail = statement_append instruction_port_before_address (Qcons instruction_port_address_stmt instruction_port_address_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_port_before_address_straight : straight_statements instruction_port_before_address.
Proof. vm_compute. exact I. Qed.
Lemma instruction_port_before_address_safe : memory_suffix_safe flat_memories 9176 instruction_port_before_address.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Definition instruction_port_before_read := take_statements 21 instruction_port_clock_tail.
Lemma instruction_port_before_read_split : instruction_port_clock_tail = statement_append instruction_port_before_read (Qcons instruction_port_read_stmt instruction_port_read_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_port_before_read_straight : straight_statements instruction_port_before_read.
Proof. vm_compute. exact I. Qed.
Lemma instruction_port_before_read_safe : memory_suffix_safe flat_memories 9176 instruction_port_before_read.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_port_address_next : instruction_port_address_tail = Qcons instruction_port_enable_stmt instruction_port_enable_tail.
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_port_enable_next : instruction_port_enable_tail = Qcons instruction_port_clock_stmt instruction_port_clock_tail.
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_port_read_suffix_safe : memory_suffix_safe flat_memories 9176 instruction_port_read_tail.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma instruction_port_nonregister : has_register 9176 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions instruction_port_read_suffix_safe.
