Require Import CoreSocModel ComparisonNodes ScalarNodeFrames RegisterInvariants FormalTypedNodeEquation X0ConcretePositionCertificate.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Semantics_with_memory.

Fixpoint selected_node_safety mm full (offsets : seq nat) (stmts : @hfstmt_seq VarOrder.T) : bool :=
 match offsets with
 | [::] => true
 | offset :: rest =>
   match straight_drop offset stmts with
   | Some (Qcons (Snode id expression) tail) =>
       formal_typed_suffix_safe_b mm id tail &&
       ~~ has_register id full && selected_node_safety mm full rest tail
   | _ => false
   end
 end.
Theorem x0_actual_nodes_safe :
 selected_node_safety flat_memories flat_statements x0_node_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Print Assumptions x0_actual_nodes_safe.
