import Waffle.Stability

/-! Finite sampling of the normalized projection test.
A triangle inequality is an additional assumption, not a consequence
of the BasicLength interface. It provides the missing regularity. -/

noncomputable section
namespace Waffle.Sampling
open Waffle.Geometry Waffle.Characterization Waffle.Stability

def add (p q : Vec) : Vec := (p.1+q.1,p.2+q.2)

def Triangle (G : BasicLength) : Prop :=
  ∀ p q, G.len (add p q) ≤ G.len p + G.len q

def error (G : BasicLength) (x : ℝ) : ℝ :=
  (G.len (1,x))^2-(1+x^2)

theorem slope_lipschitz (G : BasicLength) (hT : Triangle G) (x y : ℝ) :
    |G.len (1,x)-G.len (1,y)| ≤ |x-y| := by
  have h₁ := hT (1,y) (0,x-y)
  have h₂ := hT (1,x) (0,y-x)
  have e₁ : add (1,y) (0,x-y) = (1,x) := by
    apply Prod.ext <;> simp [add] <;> ring
  have e₂ : add (1,x) (0,y-x) = (1,y) := by
    apply Prod.ext <;> simp [add] <;> ring
  rw [e₁,G.swap (x-y) 0,G.axis] at h₁
  rw [e₂,G.swap (y-x) 0,G.axis,abs_sub_comm y x] at h₂
  rw [abs_le]
  constructor <;> linarith

theorem slope_upper (G : BasicLength) (hT : Triangle G) (x : ℝ)
    (hx : 0 ≤ x) : G.len (1,x) ≤ 1+x := by
  have h := hT (1,0) (0,x)
  have e : add (1,0) (0,x) = (1,x) := by simp [add]
  rw [e] at h
  rw [G.swap x 0,G.axis,G.axis,abs_one,abs_of_nonneg hx] at h
  exact h

/-- The signed squared-length error is 6-Lipschitz on the symmetry-
reduced slope interval [0,1]. No differentiability is assumed. -/
theorem error_lipschitz (G : BasicLength) (hT : Triangle G)
    (x y : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) :
    |error G x-error G y| ≤ 6*|x-y| := by
  have hxL := slope_upper G hT x hx.1
  have hyL := slope_upper G hT y hy.1
  have hxN := len_nonneg G (1,x)
  have hyN := len_nonneg G (1,y)
  have hsum : |G.len (1,x)+G.len (1,y)| ≤ 4 := by
    rw [abs_of_nonneg (by linarith)]
    linarith [hx.2,hy.2]
  have hxy : |x+y| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hx.1,hy.1])]
    linarith [hx.2,hy.2]
  have hs : |(G.len (1,x))^2-(G.len (1,y))^2| ≤ 4*|x-y| := by
    rw [show (G.len (1,x))^2-(G.len (1,y))^2 =
      (G.len (1,x)-G.len (1,y))*(G.len (1,x)+G.len (1,y)) by ring,abs_mul]
    calc
      _ ≤ |x-y| * 4 := mul_le_mul (slope_lipschitz G hT x y) hsum (abs_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hq : |x^2-y^2| ≤ 2*|x-y| := by
    rw [show x^2-y^2 = (x-y)*(x+y) by ring,abs_mul]
    calc
      _ ≤ |x-y| * 2 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
      _ = _ := by ring
  unfold error
  rw [show G.len (1,x)^2-(1+x^2)-(G.len (1,y)^2-(1+y^2)) =
    (G.len (1,x)^2-G.len (1,y)^2)-(x^2-y^2) by ring]
  calc
    _ ≤ |G.len (1,x)^2-G.len (1,y)^2|+|x^2-y^2| := abs_sub _ _
    _ ≤ _ := by linarith

/-- A finite set of sample slopes suffices if it covers [0,1]
within mesh delta. The coverage hypothesis is explicit. -/
theorem finite_sample_bound (G : BasicLength) (hT : Triangle G)
    (S : Finset ℝ) (ε δ : ℝ)
    (hcover : ∀ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ S, y ∈ Set.Icc (0:ℝ) 1 ∧ |x-y| ≤ δ)
    (hsample : ∀ y ∈ S, |error G y| ≤ ε) :
    ∀ x ∈ Set.Icc (0:ℝ) 1, |error G x| ≤ ε+6*δ := by
  intro x hx
  obtain ⟨y,hy,hyI,hxy⟩ := hcover x hx
  calc
    |error G x| = |(error G x-error G y)+error G y| := by ring_nf
    _ ≤ |error G x-error G y|+|error G y| := abs_add_le _ _
    _ ≤ ε+6*δ := by linarith [error_lipschitz G hT x y hx hyI,hsample y hy]

/-- Reciprocal slopes have identical relative squared-length error. -/
theorem reciprocal_relative (G : BasicLength) (x : ℝ) (hx : 0 < x) :
    |error G x|/(1+x^2) = |error G (1/x)|/(1+(1/x)^2) := by
  have hv : (1,x) = scale x (1/x,1) := by
    apply Prod.ext
    · simp [scale]
      field_simp [hx.ne']
    · simp [scale]
  have hq : 1+x^2 = x^2*(1+(1/x)^2) := by
    field_simp [hx.ne'] <;> ring
  have hlen : G.len (1,x) = x*G.len (1,1/x) := by
    rw [hv,G.homogeneous,abs_of_pos hx,G.swap 1 (1/x)]
  unfold error
  rw [hlen,mul_pow,hq,← mul_sub,abs_mul,abs_of_nonneg (sq_nonneg x)]
  have hn : 1+(1/x)^2 ≠ 0 := by positivity
  field_simp [hx.ne',hn] <;> ring

/-- Uniform finite-sample error implies a relative squared-length
bound on the whole plane, not only the measured slope interval. -/
theorem finite_sample_global (G : BasicLength) (hT : Triangle G)
    (S : Finset ℝ) (ε δ : ℝ) (he : 0 ≤ ε) (hd : 0 ≤ δ)
    (hcover : ∀ x ∈ Set.Icc (0:ℝ) 1, ∃ y ∈ S, y ∈ Set.Icc (0:ℝ) 1 ∧ |x-y| ≤ δ)
    (hsample : ∀ y ∈ S, |error G y| ≤ ε) :
    ∀ p : Vec, |(G.len p)^2-Q p| ≤ (ε+6*δ)*Q p := by
  have hE : 0 ≤ ε+6*δ := by linarith
  have hsmall (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      |error G x|/(1+x^2) ≤ ε+6*δ := by
    apply (div_le_iff₀ (by positivity : 0 < 1+x^2)).2
    have h := finite_sample_bound G hT S ε δ hcover hsample x hx
    nlinarith [mul_nonneg hE (sq_nonneg x)]
  apply global_relative_bound G (ε+6*δ) hE
  intro x hx
  apply (relative_bound_iff G x (ε+6*δ) hx).2
  change |error G x| ≤ (ε+6*δ)*(1+x^2)
  apply (div_le_iff₀ (by positivity : 0 < 1+x^2)).1
  by_cases h : x ≤ 1
  · exact hsmall x ⟨hx.le,h⟩
  · rw [reciprocal_relative G x hx]
    exact hsmall (1/x) ⟨by positivity,(div_le_iff₀ hx).2 (by linarith)⟩

#print axioms slope_lipschitz
#print axioms error_lipschitz
#print axioms finite_sample_bound
#print axioms reciprocal_relative
#print axioms finite_sample_global
end Waffle.Sampling
