# Jackson–Johnson waffle-cone proof in Lean 4

**Status:** complete candidate source at the level of an explicit similarity-plane interface; not yet kernel-checked. Lean, Lake and Mathlib were unavailable in the authoring environment, and outbound access to GitHub failed. No successful build or axiom-audit result is claimed. The supplied check script and GitHub Actions workflow are intended to perform that verification. No tactic holes or admitted declarations are intentionally included.

## Target

`JacksonJohnson.pythagorean_theorem_jackson_johnson` proves `a^2+b^2 = c^2` for positive legs, where `c = G.len a b`. It covers both orders of the legs and the isosceles case.

## Foundations and scope

`SimilarityPlane` is an explicit geometry parameter. It postulates axis normalization, positive length of nonzero vectors, reflection invariance, quarter-turn invariance, and length scaling under the affine direct-similarity map `(x,y) -> (p*x-q*y,q*x+p*y)`. It does **not** define length by a square root of a sum of squares. The sine is defined as the opposite/hypotenuse ratio in coordinates proportional to a rotated frame. The Law of Sines is derived, not postulated. No Mathlib Euclidean distance or analytic trigonometric identity is invoked.

The similarity postulate is substantive: it can itself imply Pythagoras by a much shorter algebraic argument (compose the similarity with its conjugate). It is justified mathematically by elementary Euclidean similarity, but its derivation from Tarski's or Hilbert's axioms is not formalized here. This project is not a claim of foundational independence from a specific existing geometry library. Rather, it formalizes the argument relative to stated geometric primitives. `#print axioms` checks Lean-level axioms only; it cannot establish the independent geometric justification of the structure's fields. In particular, do not instantiate the interface using an existing Pythagorean lemma and call that a noncircular derivation.

## Geometry and proof outline

Let `T=(0,b)`, `Y₀=(a,0)`, `Z₀=(-a,0)` and `c = G.len a b`. For `0<a<b` put `r=(a/b)^2`, `s=(2a/b)/(1-r)`, `t=2r/(1-r)` and `X=(a-sb,-sa)`.

* `scale_relations`, `Y_zero`, `Z_zero`, `w_eq` and `cone_leg_eq` establish the common cone apex, reflected triangle, extended ray and perpendicular side.
* `Y`, `Z`, `horizontal`, `base_step`, `vertical_step`, `Y_homothety`, `Z_homothety` construct the infinite family of nested similar triangles as explicit affine points. In particular `Yₙ=X+s rⁿ(b,a)`, `Zₙ=X+t rⁿ(a,b)`. Since `0<r<1`, these approach X; the length convergence is formalized in `cone_side_sums`.
* `Y_step` and `Z_step` compute the exact successive displacements. Their lengths are `(2ac/b) rⁿ` and `(2a²c/b²) rⁿ`. `cone_side_sums` proves that the series sum to `sc` and `tc`. `cone_lengths` identifies those sums with the actual boundary lengths, including the original side `c`.
* `rotated_length`, `sine_eq`, `sine_right` and `law_of_sines` derive geometric sine facts. `reflected_sine` computes `sin(2α)=2ab/c²`; `waffle_cone_sine` computes `sin(2α)=sc/(c+tc)=2ab/(a²+b²)`.
* `pythagoras_strict` equates them and cancels the nonzero numerator. `pythagoras_equal` uses the reflected right apex angle instead of the divergent cone. `pythagoras` handles the swapped-leg case by symmetry.

The main proof deliberately follows the infinite cone from the 2023 presentation, not one of the finite variants published in 2024. The use of affine coordinates is a design choice in place of formal point/line/angle objects in Mathlib's inner-product geometry.

## Build (Lean and Mathlib v4.19.0)

With [elan](https://github.com/leanprover/elan) installed and internet access, in the project directory run:

```sh
lake update
lake exe cache get
./check.sh
```

The build must succeed, the final axiom audit must be printed and `sorryAx` must be absent. Inspect the full output of `#print axioms`, not just the exit status. The version is pinned in `lean-toolchain` and `lakefile.lean`; Lake resolves the dependency manifest on first run. No build output or generated manifest is included because the build has not been run.

## Sources

- Ne’Kiya Jackson and Calcea Johnson, [Five or Ten New Proofs of the Pythagorean Theorem](https://doi.org/10.1080/00029890.2024.2370240), *The American Mathematical Monthly* 131(9), 739–752, 2024.
- C-K Shene, [A New Approach to Proving the Pythagorean Theorem](https://fermatslibrary.com/s/a-new-approach-to-proving-the-pythagorean-theorem), February 28, 2024, especially §§3–4, equations (10), (14), (15).
- Mathlib, [SpecificLimits.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecificLimits/Basic.html), `hasSum_geometric_of_lt_one`.