Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation FormalDeclaredWireCheck X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalTypedNodeEquation FormalDeclaredConnection ScalarNodeFrames FormalStatementSegments FormalTypedNodeFrames RegisterInvariants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceControlExpressions ReferenceControlNodeCertificates0 ReferenceRedirectSpine.
Definition rf_ingress_port (index:nat) := N.of_nat (Nat.add 1717 index).
Definition rf_ingress_source (index:nat) := N.of_nat (Nat.add 7299 index).
Definition rf_ingress_decl_position (index:nat) : nat := nth 0%nat [::1796%nat;1797%nat;1798%nat;1799%nat;1800%nat;1801%nat;1802%nat;1803%nat;1804%nat;1805%nat;1806%nat;1807%nat;1808%nat;1809%nat;1810%nat;1811%nat;1812%nat;1813%nat;1814%nat;1815%nat;1816%nat;1817%nat;1818%nat;1819%nat;1820%nat;1821%nat;1822%nat;1823%nat;1824%nat;1825%nat;1826%nat;1827%nat] index.
Definition rf_ingress_connect_position (index:nat) : nat := nth 0%nat [::7964%nat;7965%nat;7966%nat;7967%nat;7968%nat;7969%nat;7970%nat;7971%nat;7972%nat;7973%nat;7974%nat;7975%nat;7976%nat;7977%nat;7978%nat;7979%nat;7980%nat;7981%nat;7982%nat;7983%nat;7984%nat;7985%nat;7986%nat;7987%nat;7988%nat;7989%nat;7990%nat;7991%nat;7992%nat;7993%nat;7994%nat;7995%nat] index.
Lemma rf_ingress_wire_certificates (index:nat) : (index < 32)%coq_nat ->
 declared_wire_check flat_memories flat_statements (rf_ingress_decl_position index)
 (Nat.sub (rf_ingress_connect_position index) (S (rf_ingress_decl_position index)))
 (rf_ingress_port index) (rf_ingress_source index) 32 = true.
Proof. intros Upper.
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_reference_old_wire index invalid old current result word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (rf_ingress_source index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (rf_ingress_port index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Input Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (rf_ingress_decl_position index)
 (Nat.sub (rf_ingress_connect_position index) (S (rf_ingress_decl_position index))) (rf_ingress_port index) (rf_ingress_source index) 32);
 [apply rf_ingress_wire_certificates;exact Bound|exact Input| |exact Step].
 change (Some (Gval (Fuint 32%nat) (zext_to 32%nat (take 32%nat word))) = Some (Gval (Fuint 32%nat) word)).
 rewrite -Size take_size.
 unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_reference_old_word_ingress (index:nat) invalid s0 s1 s2 word :
 (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find (N.of_nat (Nat.add 7299 index)) s0 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find (N.of_nat (Nat.sub 2177 index)) s2 = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Input S1 S2.
 pose proof (rf_reference_old_wire index invalid s0 s0 s1 word Bound Size Input S1) as Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2177 reference_control_expr_2177);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 294%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2177 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2176 reference_control_expr_2176);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 293%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2176 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2175 reference_control_expr_2175);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 292%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2175 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2174 reference_control_expr_2174);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 291%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2174 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2173 reference_control_expr_2173);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 290%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2173 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2172 reference_control_expr_2172);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 289%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2172 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2171 reference_control_expr_2171);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 288%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2171 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2170 reference_control_expr_2170);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 287%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2170 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2169 reference_control_expr_2169);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 286%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2169 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2168 reference_control_expr_2168);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 285%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2168 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2167 reference_control_expr_2167);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 284%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2167 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2166 reference_control_expr_2166);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 283%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2166 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2165 reference_control_expr_2165);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 282%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2165 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2164 reference_control_expr_2164);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 281%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2164 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2163 reference_control_expr_2163);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 280%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2163 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2162 reference_control_expr_2162);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 279%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2162 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2161 reference_control_expr_2161);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 278%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2161 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2160 reference_control_expr_2160);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 277%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2160 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2159 reference_control_expr_2159);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 276%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2159 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2158 reference_control_expr_2158);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 275%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2158 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2157 reference_control_expr_2157);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 274%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2157 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2156 reference_control_expr_2156);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 273%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2156 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2155 reference_control_expr_2155);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 272%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2155 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2154 reference_control_expr_2154);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 271%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2154 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2153 reference_control_expr_2153);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 270%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2153 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2152 reference_control_expr_2152);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 269%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2152 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2151 reference_control_expr_2151);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 268%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2151 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2150 reference_control_expr_2150);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 267%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2150 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2149 reference_control_expr_2149);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 266%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2149 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2148 reference_control_expr_2148);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 265%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2148 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2147 reference_control_expr_2147);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 264%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2147 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 destruct index as [|index].
 - eapply (reference_redirect_ground_step reference_control_0_offsets reference_control_0_nodes 2146 reference_control_expr_2146);
 [exact reference_control_0_positions|exact reference_control_0_safety| | |exact S2].
 + apply (List.nth_error_In reference_control_0_nodes 263%nat). vm_compute. reflexivity.
 + intros site. cbn [reference_control_expr_2146 eval_hfexpr_validif_policy eval_href_validif_policy]. exact Wire.
 lia.
Qed.
