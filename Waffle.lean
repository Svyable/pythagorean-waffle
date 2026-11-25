import Mathlib.Tactic

/-!
Finite algebraic certificates for the Jackson–Johnson cone.
The two intersection equations are affine, not metric. The sine
transfer and reflected-triangle equations are explicit hypotheses;
their synthetic geometric justification is a separate research task.
No claim of priority or of a new synthetic proof is made.
-/

namespace Waffle

section Field

variable {K : Type*} [Field K]

/-- The intersection of the boundary rays gives a finite cone certificate. -/
theorem finite_cone (a b u v : K)
    (hx : u*b - v*a = 2*a)
    (hy : u*a = v*b) :
    (a^2+b^2)*u = 2*a*b*(1+v) := by
  linear_combination b * hx + a * hy

/-- The finite algebraic core is independent of limits and order.
    hsine is the reflected-triangle sine relation; hcone is the
    transfer of that same sine to the right cone. -/
theorem finite_pythagoras (a b c u v s : K)
    (hx : u*b - v*a = 2*a)
    (hy : u*a = v*b)
    (hcone : s*(1+v) = u)
    (hsine : s*c^2 = 2*a*b)
    (hnz : s*(1+v) ≠ 0) :
    a^2+b^2 = c^2 := by
  have hf := finite_cone a b u v hx hy
  have h : (s*(1+v)) * (a^2+b^2-c^2) = 0 := by
    linear_combination -hf - (a^2+b^2)*hcone + (1+v)*hsine
  have hz := (mul_eq_zero.mp h).resolve_left hnz
  exact sub_eq_zero.mp hz

/-- The affine fixed point of one shrinking step, with no completeness axiom. -/
theorem fixed_point_unique (d r x y : K) (hr : 1-r ≠ 0)
    (hx : x = d+r*x) (hy : y = d+r*y) : x = y := by
  have h : (1-r)*(x-y) = 0 := by
    linear_combination hx - hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hr)

/-- The n-step truncation of a stationary recurrence. -/
def partial (x r : K) (n : ℕ) : K := x*(1-r^n)

theorem partial_zero (x r : K) : partial x r 0 = 0 := by
  simp [partial]

theorem partial_succ (d x r : K) (n : ℕ) (hx : x = d+r*x) :
    partial x r (n+1) = d+r*partial x r n := by
  unfold partial
  rw [pow_succ]
  linear_combination hx

/-- Exact cross-multiplied truncation error, for any finite n. -/
theorem truncation_defect (a b u v r : K) (n : ℕ)
    (hx : u*b - v*a = 2*a)
    (hy : u*a = v*b) :
    (a^2+b^2)*partial u r n - 2*a*b*(1+partial v r n) =
      -(2*a*b)*r^n := by
  have hf := finite_cone a b u v hx hy
  unfold partial
  linear_combination (1-r^n)*hf

/-- Exact numerator of the error in the cone sine ratio. -/
theorem ratio_defect (u v r : K) (n : ℕ) :
    u*(1+partial v r n) - partial u r n*(1+v) = u*r^n := by
  unfold partial
  ring

/-- A separate equal-leg case, with sine of the right angle equal to one. -/
theorem equal_legs (a c s : K)
    (hs : s = 1) (h : s*c^2 = 2*a*a) :
    a^2+a^2 = c^2 := by
  rw [hs, one_mul] at h
  linear_combination -h

end Field

#print axioms finite_cone
#print axioms finite_pythagoras
#print axioms fixed_point_unique
#print axioms truncation_defect
#print axioms ratio_defect
#print axioms equal_legs

end Waffle
