#!/usr/bin/env python3
"""Instantiate the common RF theorem at the unchanged original declarations."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
original=dict(re.findall(r'(?:Lemma|Theorem)\s+generated_assert_(\d+)\s*:\s*(.*?)\.\s*(?:Proof\.|Admitted\.)',(base/'CoreSoc.v').read_text(),re.S))
for number in range(9,40):
    text=f'''Require Import CycleRFAssertionsInvariant CoreSocModel.
From Coq Require Import Lia.
Local Opaque generated_modules generated_top.
Theorem generated_assert_{number} : {original[str(number)]}.
Proof.
 intros memory inputs k observed Observe Legal.
 exact(cycle_rf_original_assertion_reachable memory inputs k observed {number-8}%nat Observe Legal ltac:(lia)).
Qed.
'''
    path=base/'staged-integration'/f'GeneratedAssertion{number}.v'
    if not path.exists() or path.read_text()!=text:
        path.write_text(text)
