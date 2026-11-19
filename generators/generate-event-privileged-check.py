from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration/EventAssertionSemantics.v'
mark='(* Actual privileged-instruction check. *)'
s=p.read_text().split(mark,1)[0]
t='''
Require Import ReferenceRedirectSpine.
Theorem event_privileged_bit8_history inputs path history limit time address bit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (65 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find 128 (history time) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 118 (history time) = Some (Gval (Fuint 3) [::false;false;true]) ->
 VM.find 140 (history time) = Some (Gval (Fuint 12) address) ->
 take 1 address = [::bit] -> drop 8 (take 9 address) = [::false] -> False.
Proof.
 intros Boundary Steps Lower Upper NoTrap Command Address Low High.
 pose proof (Steps time Upper) as Step.
'''
rows=[(284,'[::true]',['Command']),(285,'[::bit]',['Address','drop0','Low']),(286,'[::negb bit]',['V285']),(287,'[::negb bit]',['V284','V286']),(288,'[::false]',['Address','High']),(289,'[::true]',['V288']),(290,'[::negb bit]',['V287','V289']),(291,'[::bit]',['Address','drop0','Low']),(292,'[::bit]',['V284','V291']),(293,'[::false]',['Address','High']),(294,'[::true]',['V293']),(295,'[::bit]',['V292','V294'])]
for n,val,lk in rows:
 t+=f''' assert (V{n} : VM.find {n} (history time) = Some (Gval (Fuint 1) {val})).
 {{ rewrite (exception_stable_{n}_history inputs path history limit Boundary Steps time (S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply (reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes {n} joint_update_expr_{n});
 [exact joint_update_node_positions|exact joint_update_node_safety|apply (List.nth_error_In joint_update_expected_nodes {n-161}%nat);vm_compute;reflexivity| |exact Step].
 intros site. cbn [joint_update_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite {' '.join(lk)}. destruct bit; reflexivity. }}
'''
t=t.replace('rewrite Address High. destruct bit; reflexivity.', 'rewrite Address. cbn [eval_unop]. rewrite High. reflexivity.')
t=t.replace('rewrite Address drop0 Low. destruct bit; reflexivity.', 'rewrite Address. destruct address as [|b rest]; cbn in Low; inversion Low; subst; reflexivity.')
t+=''' destruct (event_no_ecall_ebreak_history inputs path history limit time Boundary Steps Lower Upper NoTrap) as [Ecall Ebreak].
 specialize (Ecall _ _ V290). specialize (Ebreak _ _ V295).
 destruct bit; discriminate.
Qed.
'''
tailmark='(* Observed privileged check. *)'
tail=p.read_text().split(tailmark,1)[1] if tailmark in p.read_text() else ''
p.write_text(s+mark+'\n'+t+(tailmark+tail if tail else ''))
