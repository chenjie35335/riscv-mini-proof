Require Import CoreSocModel ComparisonNodes FormalLocalHistory RFWriteEffect RFArchitecturalNormalRelation RFReferenceNopHistory PipelinePCRelation.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
(* A snapshot only: correctness relations belong in separately proved invariants. *)
Record cycle_view := {
 cv_dut_bank : rf_bank;
 cv_reference_bank : rf_bank;
 cv_front_instruction : bits;
 cv_commit_instruction : bits;
 cv_fetch_pc : bits;
 cv_front_pc : bits;
 cv_commit_pc : bits;
 cv_reference_pc : bits;
 cv_left : bits;
 cv_right : bits;
 cv_pending_alu : bits;
 cv_write_data : bits;
 cv_destination : bits;
 cv_write_enabled : bool;
 cv_write_select_low : bool;
 cv_write_select_high : bool;
 cv_early_bubble : bool;
 cv_late_bubble : bool;
 cv_delayed_redirect : bool;
 cv_started : bool
}.
Record cycle_view_at (env : VM.t hvalue) (v : cycle_view) : Prop := {
 cva_dut_bank : rf_dut_bank_at env (cv_dut_bank v);
 cva_reference_bank : rf_reference_bank_at env (cv_reference_bank v);
 cva_front_instruction : VM.find 7748 env=Some(Gval(Fuint 32)(cv_front_instruction v));
 cva_commit_instruction : VM.find 7750 env=Some(Gval(Fuint 32)(cv_commit_instruction v));
 cva_fetch_pc : VM.find 7768 env=Some(Gval(Fuint 33)(cv_fetch_pc v));
 cva_front_pc : VM.find 7749 env=Some(Gval(Fuint 32)(cv_front_pc v));
 cva_commit_pc : VM.find 7751 env=Some(Gval(Fuint 32)(cv_commit_pc v));
 cva_reference_pc : VM.find 7331 env=Some(Gval(Fuint 32)(cv_reference_pc v));
 cva_left : VM.find 7816 env=Some(Gval(Fuint 32)(cv_left v));
 cva_right : VM.find 7819 env=Some(Gval(Fuint 32)(cv_right v));
 cva_pending_alu : VM.find 7752 env=Some(Gval(Fuint 32)(cv_pending_alu v));
 cva_write_data : VM.find 786 env=Some(Gval(Fuint 32)(cv_write_data v));
 cva_destination : VM.find 7805 env=Some(Gval(Fuint 5)(cv_destination v));
 cva_write_enabled : VM.find 7757 env=Some(Gval(Fuint 1)[::cv_write_enabled v]);
 cva_write_select : VM.find 7756 env=Some(Gval(Fuint 2)[::cv_write_select_low v;cv_write_select_high v]);
 cva_early_bubble : VM.find 7945 env=Some(Gval(Fuint 1)[::cv_early_bubble v]);
 cva_late_bubble : VM.find 7947 env=Some(Gval(Fuint 1)[::cv_late_bubble v]);
 cva_delayed_redirect : VM.find 7760 env=Some(Gval(Fuint 1)[::cv_delayed_redirect v]);
 cva_started : VM.find 7762 env=Some(Gval(Fuint 1)[::cv_started v]);
 cva_fetch_width : size(cv_fetch_pc v)=33%nat;
 cva_reference_pc_width : size(cv_reference_pc v)=32%nat;
 cva_left_width : size(cv_left v)=32%nat;
 cva_right_width : size(cv_right v)=32%nat;
 cva_pending_width : size(cv_pending_alu v)=32%nat;
 cva_write_width : size(cv_write_data v)=32%nat
}.
(* Observation-to-observation context, with the intervening registered state
   hidden existentially. No internal settling history or node callback. *)
Definition cycle_transition memory inputs k current next : Prop :=
 generated_observe memory inputs k=Some current /\
 generated_legal_trace memory inputs k /\
 generated_observe memory inputs(S k)=Some next /\
 generated_legal_trace memory inputs(S k) /\
 exists committed, generated_run memory inputs(S k)=Some committed.
Definition cycle_reset inputs k (bit:bool) : Prop :=
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::bit]).
Definition cycle_banks_agree (v:cycle_view) : Prop :=
 forall index,(index<32)%coq_nat ->cv_dut_bank v index=cv_reference_bank v index.
Definition cycle_pc_phase (v:cycle_view) : Prop :=
 (cv_late_bubble v=false /\ cv_commit_pc v=cv_reference_pc v) \/
 (cv_late_bubble v=true /\ cv_early_bubble v=false /\ cv_front_pc v=cv_reference_pc v) \/
 (cv_late_bubble v=true /\ cv_early_bubble v=true /\
  ((cv_started v=false /\ cv_reference_pc v=take 32(cv_fetch_pc v)) \/
   (cv_started v=true /\ N.of_nat(to_nat(cv_reference_pc v))=
    N.modulo(N.add(N.of_nat(to_nat(cv_fetch_pc v)))4)(N.pow 2 32)))).
Definition cycle_pc_aligned (v:cycle_view) : Prop :=
 take 2(cv_reference_pc v)=[::false;false] /\ cycle_pc_phase v.
Theorem cycle_pc_relation_sound env v :
 cycle_view_at env v ->cycle_pc_aligned v ->pipeline_pc_relation env.
Proof.
 intros View [Aligned Phase]. exists(cv_reference_pc v).
 split;[exact(cva_reference_pc_width _ _ View)|]. split;[exact Aligned|].
 split;[exact(cva_reference_pc _ _ View)|]. unfold pipeline_pc_phase.
 destruct Phase as [[Late PC]|[[Late[Early PC]]|[Late[Early Started]]]].
 - left. split;[rewrite(cva_late_bubble _ _ View) Late;reflexivity|rewrite(cva_commit_pc _ _ View) PC;reflexivity].
 - right;left. split;[rewrite(cva_late_bubble _ _ View) Late;reflexivity|].
   split;[rewrite(cva_early_bubble _ _ View) Early;reflexivity|rewrite(cva_front_pc _ _ View) PC;reflexivity].
 - right;right. split;[rewrite(cva_late_bubble _ _ View) Late;reflexivity|].
   split;[rewrite(cva_early_bubble _ _ View) Early;reflexivity|].
   exists(cv_fetch_pc v). split;[exact(cva_fetch_width _ _ View)|].
   split;[exact(cva_fetch_pc _ _ View)|].
   destruct Started as [[Started PC]|[Started PC]];[left|right];split;try exact PC;
   rewrite(cva_started _ _ View) Started;reflexivity.
Qed.
