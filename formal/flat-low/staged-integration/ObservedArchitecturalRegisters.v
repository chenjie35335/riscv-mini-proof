Require Import CoreSocModel RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition architectural_register_ids : seq VarOrder.T :=
 [:: 851;852;853;854;855;856;857;858;859;860;861;862;863;864;865;866;
     867;868;869;870;871;872;873;874;875;876;877;878;879;880;881;882;
     7748;7750;7768].
Lemma architectural_register_structure :
 all (fun id => (id != 0) && (id != 1) &&
   initial_register_safe id flat_statements && has_register id flat_statements)
   architectural_register_ids.
Proof. vm_compute. reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements.
Theorem observed_architectural_register_copies memory inputs k committed old observed id :
 id \in architectural_register_ids ->
 generated_run memory inputs k = Some committed -> SVM.find nil committed = Some old ->
 generated_observe memory inputs k = Some observed ->
 staged_register_lookup id observed = VM.find id old.
Proof.
 intros Member Run Old Observe.
 move/allP: architectural_register_structure => Structure.
 move/andP: (Structure id Member) => [/andP [/andP [NotClock NotReset] Safe] Present].
 eapply staged_observed_register_copies; eassumption.
Qed.
Print Assumptions observed_architectural_register_copies.
