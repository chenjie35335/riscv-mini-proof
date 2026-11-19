Require Import ReferenceBankCycleInputs RFReferenceWriteEffect.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Local Open Scope N_scope.
(* Representation obligation for the actually decoded data; not an axiom. *)
Definition ref_write_selected_data_concrete env :Prop :=
 forall stage,(stage<36)%coq_nat ->ref_write_guard env stage=true ->
 exists value,VM.find(rf_reference_write_data stage)env=Some value /\
 rf_reference_low_word(ref_write_word env stage)value.
Lemma ref_write_selected_data_word env stage width raw :
 VM.find(rf_reference_write_data stage)env=Some(Gval(Fuint width)raw) ->
 size raw=width ->(32<=width)%nat ->
 rf_reference_low_word(ref_write_word env stage)(Gval(Fuint width)raw).
Proof.
 intros Value Size Width. exists width,raw. split;[reflexivity|].
 split;[exact Size|]. split;[exact Width|].
 symmetry;exact(ref_write_word_actual env stage width raw Value).
Qed.
Lemma ref_write_selected_data_transport env history start limit :
 ref_write_selected_data_concrete env ->
 (forall stage time,(stage<36)%coq_nat ->(start<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find(rf_reference_write_data stage)(history time)=VM.find(rf_reference_write_data stage)env) ->
 forall stage time,(stage<36)%coq_nat ->ref_write_guard env stage=true ->
 (start<=time)%coq_nat ->(time<=limit)%coq_nat ->
 exists value,VM.find(rf_reference_write_data stage)(history time)=Some value /\rf_reference_low_word(ref_write_word env stage)value.
Proof.
 intros Concrete Stable stage time Stage Selected Lower Upper.
 destruct(Concrete stage Stage Selected)as[value[Value Low]].
 exists value;split;[rewrite(Stable stage time Stage Lower Upper);exact Value|exact Low].
Qed.
