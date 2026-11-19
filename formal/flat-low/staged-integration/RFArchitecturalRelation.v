Require Import ConcreteRegisterInitialization UIntRegisterCertificate FormalSingletonSymbolic StagedFlatCircuitIteration StagedObservedRegister StagedCircuitRegisterHold StagedRegisterHold FormalLocalHistory RegisterPreparationFrames CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition rf_architectural_register_pairs : list (nat * nat) := [::(851%nat,7299%nat);(852%nat,7300%nat);(853%nat,7301%nat);(854%nat,7302%nat);(855%nat,7303%nat);(856%nat,7304%nat);(857%nat,7305%nat);(858%nat,7306%nat);(859%nat,7307%nat);(860%nat,7308%nat);(861%nat,7309%nat);(862%nat,7310%nat);(863%nat,7311%nat);(864%nat,7312%nat);(865%nat,7313%nat);(866%nat,7314%nat);(867%nat,7315%nat);(868%nat,7316%nat);(869%nat,7317%nat);(870%nat,7318%nat);(871%nat,7319%nat);(872%nat,7320%nat);(873%nat,7321%nat);(874%nat,7322%nat);(875%nat,7323%nat);(876%nat,7324%nat);(877%nat,7325%nat);(878%nat,7326%nat);(879%nat,7327%nat);(880%nat,7328%nat);(881%nat,7329%nat);(882%nat,7330%nat)].
Definition rf_architectural_register_ids : list nat := [::851%nat;7299%nat;852%nat;7300%nat;853%nat;7301%nat;854%nat;7302%nat;855%nat;7303%nat;856%nat;7304%nat;857%nat;7305%nat;858%nat;7306%nat;859%nat;7307%nat;860%nat;7308%nat;861%nat;7309%nat;862%nat;7310%nat;863%nat;7311%nat;864%nat;7312%nat;865%nat;7313%nat;866%nat;7314%nat;867%nat;7315%nat;868%nat;7316%nat;869%nat;7317%nat;870%nat;7318%nat;871%nat;7319%nat;872%nat;7320%nat;873%nat;7321%nat;874%nat;7322%nat;875%nat;7323%nat;876%nat;7324%nat;877%nat;7325%nat;878%nat;7326%nat;879%nat;7327%nat;880%nat;7328%nat;881%nat;7329%nat;882%nat;7330%nat].
Definition rf_architectural_relation env : Prop :=
 List.Forall (fun pair => exists word, size word = 32%nat /\
 VM.find (N.of_nat (fst pair)) env = Some (Gval (Fuint 32) word) /\
 VM.find (N.of_nat (snd pair)) env = Some (Gval (Fuint 32) word)) rf_architectural_register_pairs.
Definition rf_architectural_registers_concrete env : Prop :=
 forall node, List.In node rf_architectural_register_ids -> map_uint_concrete (N.of_nat node) 32 env.
Lemma rf_architectural_register_check :
 List.forallb (fun node => has_register (N.of_nat node) flat_statements &&
 uint_register_declarations_b (N.of_nat node) 32 flat_statements && initial_register_safe (N.of_nat node) flat_statements) rf_architectural_register_ids = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_architectural_register_properties node :
 List.In node rf_architectural_register_ids ->
 has_register (N.of_nat node) flat_statements = true /\
 uint_register_declarations (N.of_nat node) 32 flat_statements /\
 initial_register_safe (N.of_nat node) flat_statements.
Proof.
 intro Member. pose proof rf_architectural_register_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check node Member).
 move/andP: Check => [/andP [Present Typed] Initial].
 split; [exact Present|]. split; [apply uint_register_declarations_b_sound;exact Typed|exact Initial].
Qed.
Lemma rf_architectural_symbolic_registers inputs path state :
 rf_architectural_registers_concrete (initialize_symbolic_registers inputs path flat_statements state).
Proof.
 intros node Member. destruct (rf_architectural_register_properties node Member) as [Present [Typed Initial]].
 apply initialize_establishes_uint_concrete; assumption.
Qed.
Theorem rf_architectural_symbolic_initial_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ rf_architectural_registers_concrete env.
Proof.
 intro Init.
 exact (singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements memory inputs states
 rf_architectural_registers_concrete flat_instance_map_exact flat_module_exact (rf_architectural_symbolic_registers inputs nil) Init).
Qed.
Lemma rf_architectural_nonexternal node :
 List.In node rf_architectural_register_ids ->
 (N.of_nat node != 0) /\ (N.of_nat node != 1).
Proof.
 intro Member.
 assert (Check : List.forallb (fun n => (N.of_nat n != 0) && (N.of_nat n != 1)) rf_architectural_register_ids = true).
 { vm_compute. reflexivity. }
 rewrite List.forallb_forall in Check. specialize (Check node Member).
 move/andP: Check => [Clock Reset]. split; assumption.
Qed.
Theorem rf_architectural_prepared_concrete previous old external initial :
 SVM.find nil previous = Some old -> rf_architectural_registers_concrete old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial ->
 rf_architectural_registers_concrete (top_environment initial).
Proof.
 intros Previous Concrete Prepare node Member.
 destruct (rf_architectural_nonexternal node Member) as [Nonclock Nonreset].
 destruct (rf_architectural_register_properties node Member) as [Present [Typed Initial]].
 destruct (Concrete node Member) as [word [Size Value]]. exists word; split; [exact Size|].
 pose proof (staged_prepared_register_copies previous old external initial (N.of_nat node) Nonclock Nonreset Initial Present Previous Prepare) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy. unfold top_environment.
 destruct (SVM.find nil initial); [exact Copy|discriminate Copy].
Qed.
Print Assumptions rf_architectural_symbolic_initial_concrete.
