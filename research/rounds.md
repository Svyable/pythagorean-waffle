# Research record

## R01 — Sharp slope regularity and dense tests (2026-11-25)

Baseline: 24a673d. Prior finite mesh bound used the triangle inequality
to bound the two squared differences separately, obtaining constant 6.

- Direction A: preserve cancellation. Reflection and convex combinations
  imply L(1,y) <= L(1,x) for 0 <= y <= x. The first proof of the sharper
  estimate failed Lean on multiplication order/inference; an explicit
  ordered multiplication calculation repaired it.
- Direction B: adversarial sharpness. Construct a full BasicLength model
  for taxicab length and prove its triangle inequality. Its error at 0
  and 1 forces every universal absolute-error Lipschitz constant >= 2.
  This rules out smaller constants for that particular theorem; it does
  not rule out a better global relative mesh bound.
- Direction C: dense rational samples. Use rational density and the
  improved Lipschitz bound to extend zero error to real slopes in (0,1],
  then reciprocal symmetry and homogeneity to the whole plane.

Accepted by Lean 4.19.0 (see verification/refinement-lean-4.19.0.txt):
slope_monotone, error_lipschitz_two, finite_sample_bound_two,
finite_sample_global_two, taxicab_triangle, lipschitz_two_sharp,
rational_slopes. Standard axiom dependencies only.

Objections still open: triangle inequality is an explicit new hypothesis,
not a result of BasicLength. No originality claim. Sharpness of the
absolute-error Lipschitz constant does not imply sharpness of every
sampling bound. Synthetic AA justification remains open.

Next directions: optimize relative-error regularity, verify an explicit
rational uniform mesh (rather than assuming coverage), compare with
classical norm-characterization literature, and investigate synthetic
geometry adapters. The archived global similarity axiom is not an
independent foundation.
