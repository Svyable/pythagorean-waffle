import Waffle.Characterization

/-! Quantitative stability of the normalized projection condition.
The defect is an observable product difference, not a distance formula.
The exact identity and relative bound do not assume LocalAA. -/

noncomputable section
namespace Waffle.Stability
open Waffle.Geometry Waffle.Characterization

def defect (G : BasicLength) (x : ℝ) : ℝ :=
  G.len (0,x)*G.len (1,0) -
    G.len (sub (1,0) (scale (1/(1+x^2)) (1,x)))*G.len (1,x)

/-- The raw projection defect is exactly the squared-length error,
weighted by x/(1+x²). -/
theorem defect_identity (G : BasicLength) (x : ℝ) (hx : 0 < x) :
    defect G x = x/(1+x^2)*(1+x^2-(G.len (1,x))^2) := by
  have hd : 0 < 1+x^2 := by positivity
  have hv : sub (1,0) (scale (1/(1+x^2)) (1,x)) =
      scale (x/(1+x^2)) (x,-1) := by
    apply Prod.ext <;> simp [sub,scale] <;> field_simp [hd.ne'] <;> ring
  unfold defect
  rw [G.swap x 0,G.axis,G.axis,abs_of_pos hx,abs_one,hv,G.homogeneous,
    G.reflect,G.swap 1 x,abs_of_pos (div_pos hx hd)]
  field_simp [hd.ne'] <;> ring

/-- A relative defect tolerance is equivalent to a relative squared
length tolerance; no loss in the constant. -/
theorem relative_bound_iff (G : BasicLength) (x ε : ℝ) (hx : 0 < x) :
    |defect G x| ≤ ε*x ↔
    |(G.len (1,x))^2-(1+x^2)| ≤ ε*(1+x^2) := by
  have hd : 0 < 1+x^2 := by positivity
  rw [defect_identity G x hx,abs_mul,abs_of_pos (div_pos hx hd)]
  rw [show |1+x^2-(G.len (1,x))^2| =
      |(G.len (1,x))^2-(1+x^2)| by rw [abs_sub_comm]]
  constructor <;> intro h
  · have hh : |(G.len (1,x))^2-(1+x^2)| ≤ ε*x/(x/(1+x^2)) :=
      (le_div_iff₀ (div_pos hx hd)).2 (by
        rw [mul_comm |(G.len (1,x))^2-(1+x^2)|]
        exact h)
    have he : ε*x/(x/(1+x^2)) = ε*(1+x^2) := by
      field_simp [hx.ne',hd.ne'] <;> ring
    rwa [he] at hh
  · calc
      x/(1+x^2)*|(G.len (1,x))^2-(1+x^2)| ≤
          x/(1+x^2)*(ε*(1+x^2)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = ε*x := by field_simp [hd.ne'] <;> ring

/-- Extend a uniform positive-slope defect bound to the entire plane.
Axis cases are exact. -/
theorem global_relative_bound (G : BasicLength) (ε : ℝ) (he : 0 ≤ ε)
    (h : ∀ x : ℝ, 0 < x → |defect G x| ≤ ε*x) :
    ∀ p : Vec, |(G.len p)^2-Q p| ≤ ε*Q p := by
  rintro ⟨a,b⟩
  change |(G.len (a,b))^2-(a^2+b^2)| ≤ ε*(a^2+b^2)
  rw [len_abs]
  have ha : |a|^2 = a^2 := sq_abs a
  have hb : |b|^2 = b^2 := sq_abs b
  by_cases haz : a = 0
  · subst a
    rw [abs_zero,G.swap |b| 0,G.axis,abs_abs,hb]
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,sub_self,abs_zero]
    positivity
  by_cases hbz : b = 0
  · subst b
    rw [abs_zero,G.axis,abs_abs,ha]
    simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),add_zero,sub_self,abs_zero]
    positivity
  have hap := abs_pos.mpr haz
  have hbp := abs_pos.mpr hbz
  let x := |b|/|a|
  have hx : 0 < x := div_pos hbp hap
  have hv : (|a|,|b|) = scale |a| (1,x) := by
    apply Prod.ext
    · simp [scale]
    · simp [scale,x]
      field_simp [hap.ne']
  have hq : |a|^2*(1+x^2) = a^2+b^2 := by
    dsimp [x]
    rw [← ha,← hb]
    field_simp [hap.ne'] <;> ring
  have hh := (relative_bound_iff G x ε hx).1 (h x hx)
  rw [hv,G.homogeneous,abs_abs,mul_pow,← hq,← mul_sub,abs_mul,
    abs_of_nonneg (sq_nonneg _)]
  calc
    |a|^2*|(G.len (1,x))^2-(1+x^2)| ≤ |a|^2*(ε*(1+x^2)) :=
      mul_le_mul_of_nonneg_left hh (sq_nonneg _)
    _ = ε*(|a|^2*(1+x^2)) := by ring

#print axioms defect_identity
#print axioms relative_bound_iff
#print axioms global_relative_bound
end Waffle.Stability
