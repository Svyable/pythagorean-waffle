# Pythagorean Waffle

Research into machine-checked trigonometric proofs of the Pythagorean theorem, inspired by Ne'Kiya Jackson and Calcea Johnson.

## Status

- `Waffle.lean`: finite affine intersection certificate, conditional Pythagorean derivation, fixed-point uniqueness and exact finite truncation error over arbitrary fields. Geometry assumptions are explicit.
- `archive/JacksonJohnson.lean`: original 460-line prototype, preserved as an **unverified archive**, not part of the default build. Its global similarity axiom itself implies Pythagoras; do not use it to certify foundational independence.
- Synthetic derivation of the sine transfer, reflected-triangle sine law, and angle/length semantics remains open.

## Mathematical core

Let the reflected triangle have vertices (0,b), (a,0), (-a,0). For 0 < a < b, the cone apex lies at the intersection
(a,0)-u(b,a) = (-a,0)-v(a,b).
Thus ub-va=2a and ua=vb. Multiply the first equation by b and the second by a and add to obtain
(a²+b²)u = 2ab(1+v).

For a genuine Euclidean configuration, the same angle sine s satisfies s(1+v)=u and sc²=2ab. These are currently explicit hypotheses, not hidden axioms. Combining the three equations gives Pythagoras whenever s(1+v) is nonzero. No infinite sum is necessary in the algebraic core.

For r=(a/b)² and u_n=u(1-rⁿ), v_n=v(1-rⁿ), the exact cross-multiplied truncation defect is
(a²+b²)u_n - 2ab(1+v_n) = -2ab rⁿ.
The normalized ratio defect has numerator u rⁿ. These certificates apply for every finite n and need no analytic limit or ordered field.

## Build

```sh
lake update
lake exe cache get
lake build
lake env lean Waffle.lean
```

The CI workflow builds the active target and prints the exported theorems' axioms. A clean kernel audit checks formal validity, not the independent geometric justification of explicit hypotheses.

## Research goals

1. Establish geometry using synthetic axioms, without relying on Euclidean norm or a multiplicativity axiom that immediately entails Pythagoras.
2. Derive both sine relations from local angle similarity and altitude geometry.
3. Verify the infinite construction and compare it against the finite intersection certificate; handle equal legs and reverse ordering.
4. Formalize the published proofs and related finite methods; audit theorem dependencies and test assumption minimality.
5. Establish priority through literature review. The finite approach is an engineering/research direction, not a claimed new theorem or first proof.

## References

- Jackson and Johnson, [Five or Ten New Proofs of the Pythagorean Theorem](https://doi.org/10.1080/00029890.2024.2370240), 2024.
- C-K Shene, [A New Approach to Proving the Pythagorean Theorem](https://pages.mtu.edu/~shene/VIDEOS/GEOMETRY/004-Pythagorean-Thm/Pythagorean.pdf).
- Kise, Uehara, Shinzato, [Trigonometric Ratios Can Prove the Pythagorean Theorem](https://arxiv.org/abs/2506.06304), 2025. Finite trigonometric proofs already exist.
- [Rutgers Pythagoras4](https://github.com/ianjauslin-rutgers/pythagoras4) and [GeoCoq](https://github.com/GeoCoq/GeoCoq) for synthetic foundations.
