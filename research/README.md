# Verified research rounds

This workflow adapts Cai et al., *Cogentic: Multi-Agent Orchestration for
Automated Proof Discovery*, arXiv:2609.40324v2 (2026-10-01),
https://arxiv.org/html/2609.40324v2, sections 2.1–2.5.

Use bounded rounds with separate directions: candidate proof, competing
route, counterexample, foundations, and literature. Record failed
attempts even when a useful fragment survives. Promote intermediate
lemmas only after a clean Lean check. Axiom auditing is not sufficient
for independence or novelty; review structure hypotheses, compare
directions, and distinguish a sharp theorem from a merely useful bound.

- rounds.md is the persistent attempt and critique record.
- publication/claims.json records scoped publishable claims.
- The publication builder exports proof-ledger.json from the current
  audit, including every audited declaration and immutable revision.
- Before a new round, read the latest verified ledger and prior objections.
- At the end, rerun Lean, record results and residual questions, update
  the publication, and commit. No fabricated verifier consensus.

This is a sequential, kernel-gated adaptation, not a deployment of
Cogentic itself or a claim that independent agents were run.
