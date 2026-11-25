# Proof-carrying publication workflow

Inspired by [PaperOrchestra](https://github.com/google-research/paper-orchestra)
([Song et al., 2026](https://arxiv.org/abs/2604.05018)).
We adopt separation of outline, literature, exposition, figures, and review.
Unlike unrestricted manuscript generation, claims originate in Lean
and must survive the kernel and publication audit.

- claims.json: explicit claim registry with scope and source theorem.
- build.py: deterministic HTML publication and evidence export; checks
  every registered theorem against the current successful axiom audit.
- whitepaper.html: reviewed narrative, exact equations, interactive figures.
- literature.md: primary references and priority questions.
- CI builds Lean, rejects admitted axioms, generates the whitepaper,
  then deploys the exact checked commit to GitHub Pages.

For optional PaperOrchestra use, clone upstream at a reviewed immutable
commit in a separate environment. Supply the generated raw_materials
directory to its CLI with a mathematics LaTeX template, and save output
as a draft outside the verified Pages pipeline. Never treat generated
bibliography entries as verified. No external LLM API key is required for
this repository's deterministic pipeline. Do not send private credentials
or unpublished material to an external service without authorization.

## Editorial gates

1. Literature: verify DOI/arXiv metadata and inspect the relevant passages;
   no first-proof or priority claim before comparison.
2. Mathematics: match each claim's exact hypotheses to Lean; the standard
   axiom audit does not justify an interface's geometry independently.
3. Figures: generated from explicit coordinate formulas; distinguish
   illustration from proof.
4. Reproducibility: pin dependencies, record source commit and successful
   audit, and archive a release before submission.
5. Authorship and AI disclosure: follow the chosen venue's current rules;
   author reviews and approves the final submission. No automatic submission.

The working paper is public, not peer reviewed or a journal submission.
