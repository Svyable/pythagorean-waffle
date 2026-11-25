# Research program and acceptance criteria

## R1 — Finite and infinite constructions

The affine intersection determines u and v without limits. For a nonzero b,
it also gives u = 2a/b + r u and v = 2r + r v, with r = (a/b)^2.
The two series are unique fixed points if r != 1. The nth truncated
solution has an exact polynomial defect, not merely a numerical estimate.

Acceptance: build and axiom audit all active algebra theorems, including
rational countermodels for omission of either sine relation. Prove that
the actual Euclidean cone exists with the asserted right angle and that
the triangle sequence realizes these algebraic partial sums.

## R2 — Independent synthetic geometry

Investigate the Rutgers Pythagoras4 synthetic similarity library and
Tarski-based GeoCoq. Use incidence, perpendicularity, congruence,
parallelism, and similarity with explicit dependencies.

For a right triangle, define geometric sine as the opposite/hypotenuse
ratio; prove independence of the representative via local similarity.
For the reflected triangle, let h be the altitude to a side of length c.
Show the double-angle sine is h/c (handling the foot on the extended
side when necessary); equate the two area expressions c*h/2 = a*b.
This yields s*c^2 = 2*a*b without using the unit-circle identity.
For the cone show s(1+v)c = u*c by angle congruence and local scaling.

Acceptance: no appeal to the Euclidean norm formula, the sine-square
identity, a Pythagorean theorem lemma, or the global complex-similarity
length postulate in the archive. Explain the actual dependency graph,
not merely a kernel axiom audit. Explicit hypothesis use must be justified
by prior geometric lemmas. Treat equal legs separately.

## R3 — Proof comparison and novelty

Compare the original 2023 cone, the five published Jackson–Johnson proofs
(2024), Shene's reconstruction, Zimba (2009), and Kise–Uehara–Shinzato
(2025). Finite trigonometric proofs predate this repository, so avoiding
infinite series alone is not a novelty claim. Investigate whether the
particular fixed-point and finite-truncation certificates and comparative
synthetic dependency analysis have prior art.

Acceptance: cite sources, distinguish mathematical novelty from
formalization novelty, publish reproducible builds and dependencies,
and do not claim a first until checked.
