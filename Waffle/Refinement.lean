import Waffle.Sampling

/-! Sharp sampling regularity. The triangle inequality and reflection
imply monotonicity on positive slopes. Exploiting the sign of the
length change improves the earlier constant six to two. -/
noncomputable section
namespace Waffle.Refinement
open Waffle.Geometry Waffle.Characterization Waffle.Sampling Waffle.Stability

theorem slope_monotone (G : BasicLength) (hT : Triangle G) (x y : ℝ)
    (hy : 0 ≤ y) (hyx : y ≤ x) :
    G.len (1,y) ≤ G.len (1,x) := by
  by_cases hx : x = 0
  · have : y = 0 := by linarith
    simp [hx,this]
  have hxpos : 0 < x := lt_of_le_of_ne (le_trans hy hyx) (Ne.symm hx)
  let t := (x+y)/(2*x)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < 2*x)).2
    linarith
  have hv : add (scale t (1,x)) (scale (1-t) (1,-x)) = (1,y) := by
    apply Prod.ext
    · simp [add,scale]
    · dsimp [add,scale,t]
      field_simp [hx]
      ring
  have h := hT (scale t (1,x)) (scale (1-t) (1,-x))
  rw [hv,G.homogeneous,G.homogeneous,G.reflect,abs_of_nonneg ht,
    abs_of_nonneg (sub_nonneg.mpr ht1)] at h
  linarith

/-- Ordered slopes: preserve cancellation between the two squared
terms instead of estimating them separately. -/
theorem error_lipschitz_ordered (G : BasicLength) (hT : Triangle G)
    (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : y ≤ x) :
    |error G x-error G y| ≤ 2*|x-y| := by
  have hL := slope_monotone G hT x y hy.1 hxy
  have hN := len_nonneg G (1,y)
  have hN' := len_nonneg G (1,x)
  have hU := slope_upper G hT x hx.1
  have hU' := slope_upper G hT y hy.1
  have hD := slope_lipschitz G hT x y
  rw [abs_of_nonneg (sub_nonneg.mpr hL),abs_of_nonneg (sub_nonneg.mpr hxy)] at hD
  have hprod : (G.len (1,x)-G.len (1,y))*(G.len (1,x)+G.len (1,y)) ≤
      (x-y)*(2+x+y) :=
    mul_le_mul hD (by linarith) (by linarith) (by linarith [hx.1,hy.1])
  have hprod0 : 0 ≤ (G.len (1,x)-G.len (1,y))*(G.len (1,x)+G.len (1,y)) :=
    mul_nonneg (sub_nonneg.mpr hL) (by linarith)
  have hgeom : (x-y)*(x+y) ≤ 2*(x-y) := by
    calc
      _ ≤ (x-y)*2 := mul_le_mul_of_nonneg_left (show x+y ≤ 2 by linarith [hx.2,hy.2]) (sub_nonneg.mpr hxy)
      _ = _ := by ring
  rw [abs_of_nonneg (sub_nonneg.mpr hxy),abs_le]
  unfold error
  constructor <;> nlinarith

theorem error_lipschitz_two (G : BasicLength) (hT : Triangle G)
    (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |error G x-error G y| ≤ 2*|x-y| := by
  rcases le_total y x with h | h
  · exact error_lipschitz_ordered G hT x y hx hy h
  · rw [abs_sub_comm (error G x) (error G y),abs_sub_comm x y]
    exact error_lipschitz_ordered G hT y x hy hx h

theorem finite_sample_bound_two (G : BasicLength) (hT : Triangle G)
    (S : Finset ℝ) (ε δ : ℝ)
    (hcover : ∀ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ S, y ∈ Set.Icc (0:ℝ) 1 ∧ |x-y| ≤ δ)
    (hsample : ∀ y ∈ S, |error G y| ≤ ε) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, |error G x| ≤ ε+2*δ := by
  intro x hx
  obtain ⟨y,hy,hyI,hxy⟩ := hcover x hx
  calc
    |error G x| = |(error G x-error G y)+error G y| := by ring_nf
    _ ≤ |error G x-error G y|+|error G y| := abs_add_le _ _
    _ ≤ ε+2*δ := by linarith [error_lipschitz_two G hT x y hx hyI,hsample y hy]

theorem finite_sample_global_two (G : BasicLength) (hT : Triangle G)
    (S : Finset ℝ) (ε δ : ℝ) (he : 0 ≤ ε) (hd : 0 ≤ δ)
    (hcover : ∀ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ S, y ∈ Set.Icc (0:ℝ) 1 ∧ |x-y| ≤ δ)
    (hsample : ∀ y ∈ S, |error G y| ≤ ε) :
    ∀ p : Vec, |(G.len p)^2-Q p| ≤ (ε+2*δ)*Q p := by
  have hE : 0 ≤ ε+2*δ := by linarith
  have hsmall (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      |error G x|/(1+x^2) ≤ ε+2*δ := by
    apply (div_le_iff₀ (by positivity : 0 < 1+x^2)).2
    have h := finite_sample_bound_two G hT S ε δ hcover hsample x hx
    nlinarith [mul_nonneg hE (sq_nonneg x)]
  apply global_relative_bound G (ε+2*δ) hE
  intro x hx
  apply (relative_bound_iff G x (ε+2*δ) hx).2
  change |error G x| ≤ (ε+2*δ)*(1+x^2)
  apply (div_le_iff₀ (by positivity : 0 < 1+x^2)).1
  by_cases h : x ≤ 1
  · exact hsmall x ⟨hx.le,h⟩
  · rw [reciprocal_relative G x hx]
    exact hsmall (1/x) ⟨by positivity,(div_le_iff₀ hx).2 (by linarith)⟩

/-- The taxicab length satisfies all basic length rules and triangle
inequality, so it is a valid extremal example, not just a numeric test. -/
def taxicab : BasicLength where
  len p := |p.1| + |p.2|
  axis := by intro x; simp
  swap := by intro x y; simp [add_comm]
  reflect := by intro x y; simp
  pos := by
    intro p hp
    rcases p with ⟨x,y⟩
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro h
        exact hp (by simp [hx,h])
      simp [hx,abs_pos.mpr hy]
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hx) (abs_nonneg y)
  homogeneous := by
    intro t p
    simp [scale,abs_mul]
    ring

theorem taxicab_triangle : Triangle taxicab := by
  intro p q
  change |p.1+q.1|+|p.2+q.2| ≤ (|p.1|+|p.2|)+(|q.1|+|q.2|)
  linarith [abs_add_le p.1 q.1,abs_add_le p.2 q.2]

/-- Two is optimal for the universal absolute-error Lipschitz bound.
The taxicab norm attains equality at slopes zero and one. -/
theorem lipschitz_two_sharp (C : ℝ)
    (h : ∀ (G : BasicLength), Triangle G →
      ∀ x y : ℝ, x ∈ Set.Icc (0:ℝ) 1 → y ∈ Set.Icc (0:ℝ) 1 →
      |error G x-error G y| ≤ C*|x-y|) : 2 ≤ C := by
  have hh := h taxicab taxicab_triangle 1 0 (by constructor <;> norm_num)
    (by constructor <;> norm_num)
  norm_num [error,taxicab] at hh
  exact hh

/-- Dense rational slopes suffice under triangle inequality. -/
theorem rational_slopes (G : BasicLength) (hT : Triangle G)
    (h : ∀ q : ℚ, 0 < q → (q:ℝ) ≤ 1 → error G (q:ℝ) = 0) :
    Quadratic G := by
  have hsmall (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : error G x = 0 := by
    by_contra hn
    have he : 0 < |error G x| := abs_pos.mpr hn
    have hlo : max 0 (x-|error G x|/4) < x := max_lt hx (by linarith)
    obtain ⟨q,hq₁,hq₂⟩ := exists_rat_btwn hlo
    have hqp : 0 < (q:ℝ) := lt_of_le_of_lt (le_max_left _ _) hq₁
    have hq' : 0 < q := by exact_mod_cast hqp
    have hqI : (q:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨hqp.le, hq₂.le.trans hx1⟩
    have hh := error_lipschitz_two G hT x (q:ℝ) ⟨hx.le,hx1⟩ hqI
    rw [h q hq' hqI.2,sub_zero,abs_of_nonneg (sub_nonneg.mpr hq₂.le)] at hh
    have hdist := lt_of_le_of_lt (le_max_right 0 (x-|error G x|/4)) hq₁
    linarith
  have hzero : ∀ p : Vec, |(G.len p)^2-Q p| ≤ 0*Q p := by
    apply global_relative_bound G 0 (by norm_num)
    intro x hx
    apply (relative_bound_iff G x 0 hx).2
    change |error G x| ≤ 0*(1+x^2)
    by_cases hx1 : x ≤ 1
    · rw [hsmall x hx hx1]
      norm_num
    · have hrec := reciprocal_relative G x hx
      have hinv : 0 < 1/x := by positivity
      have hinv1 : 1/x ≤ 1 := (div_le_iff₀ hx).2 (by linarith)
      rw [hsmall (1/x) hinv hinv1,abs_zero,zero_div] at hrec
      have hz : |error G x| = 0 := (div_eq_zero_iff.mp hrec).resolve_right (by positivity)
      rw [hz,zero_mul]
  intro p
  have hh := hzero p
  simp only [zero_mul,abs_nonpos_iff,sub_eq_zero] at hh
  exact hh

#print axioms taxicab_triangle
#print axioms lipschitz_two_sharp
#print axioms rational_slopes
#print axioms slope_monotone
#print axioms error_lipschitz_two
#print axioms finite_sample_bound_two
#print axioms finite_sample_global_two
end Waffle.Refinement
