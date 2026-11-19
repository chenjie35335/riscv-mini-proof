Require Import CoreSocModel ComparisonNodes RegisterInvariants StagedRegisterHold.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_control_registers : list VarOrder.T := [::7299;7300;7301;7302;7303;7304;7305;7306;7307;7308;7309;7310;7311;7312;7313;7314;7315;7316;7317;7318;7319;7320;7321;7322;7323;7324;7325;7326;7327;7328;7329;7330;7331;7332;7368;7750;7947].
Lemma reference_control_registers_check : List.forallb (fun node => has_register node flat_statements) reference_control_registers = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_control_register_present node :
 List.In node reference_control_registers -> has_register node flat_statements = true.
Proof.
 intro Member. pose proof reference_control_registers_check as Check. rewrite List.forallb_forall in Check.
 exact (Check node Member).
Qed.
Lemma reference_control_register_history_same invalid history limit node :
 has_register node flat_statements = true ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (time <= limit)%coq_nat -> VM.find node (history time) = VM.find node (history 0%nat).
Proof.
 intros Present Steps time. induction time as [|time IH]; intro Bound; [reflexivity|].
 rewrite (staged_combinational_holds_registers invalid flat_memories (history time) (history time) (history (S time)) flat_statements node Present (Steps time ltac:(lia))).
 apply IH. lia.
Qed.
