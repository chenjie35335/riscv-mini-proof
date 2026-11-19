Require Import CoreSocModel.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition top_ports := match generated_module_0 with FInmod _ ports _ | FExmod _ ports _ => ports end.
Lemma defined_external_reset inputs :
 formal_external_inputs_defined generated_modules generated_top inputs = true ->
 exists bit, VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit]).
Proof.
 change (all (external_port_defined (formal_external_inputs inputs)) top_ports = true -> exists bit, VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit])).
 let ports := eval vm_compute in top_ports in
 change (all (external_port_defined (formal_external_inputs inputs)) ports = true -> exists bit, VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::bit])).
 move/andP => [_ /andP [Reset _]].
 cbn [external_port_defined type_has_input] in Reset.
 destruct (VM.find 1 (formal_external_inputs inputs)) as [value|] eqn:Lookup; [|discriminate Reset].
 destruct value as [ground bits|element array|bundle|t|t|t]; try discriminate Reset.
 cbn [known_input_value type_has_input] in Reset.
 move/andP: Reset => [/eqP Ground /eqP Width]. subst ground.
 destruct bits as [|bit tail]; [discriminate Width|].
 destruct tail; [exists bit; reflexivity|discriminate Width].
Qed.
Lemma legal_observation_reset memory inputs k :
 generated_legal_trace memory inputs k ->
 exists bit, VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros [_ Trace]. destruct (Trace k (PeanoNat.Nat.le_refl k)) as [Defined _].
 apply defined_external_reset. exact Defined.
Qed.
Print Assumptions legal_observation_reset.
