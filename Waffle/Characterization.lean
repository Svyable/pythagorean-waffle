import Waffle.Similarity

/-! Characterization of Euclidean length by the local AA rule.
The converse deliberately assumes the quadratic law; it is not used in
the forward waffle-cone derivation. The result identifies the exact
logical strength of the geometric assumption under the length rules. -/

noncomputable section
namespace Waffle.Characterization
open Waffle.Geometry

structure BasicLength where
  len : Vec → ℝ
  axis : ∀ x, len (x,0) = |x|
  swap : ∀ x y, len (y,x) = len (x,y)
  reflect : ∀ x y, len (x,-y) = len (x,y)
  pos : ∀ p, p ≠ (0,0) → 0 < len p
  homogeneous : ∀ t p, len (scale t p) = |t| * len p

def LocalAA (G : BasicLength) : Prop :=
  ∀ (p q : Vec) (k t : ℝ),
    p ≠ (0,0) → q ≠ (0,0) → 0 < k → 0 < t →
    Perp p (sub q p) →
    Perp (scale t q) (sub (scale k p) (scale t q)) →
    G.len (sub q p) * G.len (scale k p) =
      G.len (sub (scale k p) (scale t q)) * G.len q

def Q (p : Vec) : ℝ := p.1^2+p.2^2
def D (p q : Vec) : ℝ := p.1*q.1+p.2*q.2

def Quadratic (G : BasicLength) : Prop := ∀ p, (G.len p)^2 = Q p

theorem len_neg (G : BasicLength) (p : Vec) :
    G.len (scale (-1) p) = G.len p := by
  rw [G.homogeneous]
  norm_num

theorem len_left (G : BasicLength) (a b : ℝ) :
    G.len (-a,b) = G.len (a,b) := by
  have h : (-a,b) = scale (-1) (a,-b) := by
    apply Prod.ext <;> simp [scale]
  rw [h,len_neg,G.reflect]

theorem len_abs (G : BasicLength) (a b : ℝ) :
    G.len (a,b) = G.len (|a|,|b|) := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha,abs_of_nonneg hb]
  · rw [abs_of_nonneg ha,abs_of_neg hb,G.reflect]
  · rw [abs_of_neg ha,abs_of_nonneg hb,len_left]
  · rw [abs_of_neg ha,abs_of_neg hb,len_left,G.reflect]

theorem len_nonneg (G : BasicLength) (p : Vec) : 0 ≤ G.len p := by
  by_cases h : p = (0,0)
  · rw [h,G.axis,abs_zero]
  · exact le_of_lt (G.pos p h)

/-- All vectors, including zero and axes, follow from the positive-leg
waffle proof by reflection and axial calibration. -/
theorem quadratic_of_localAA (G : BasicLength) (hAA : LocalAA G) :
    Quadratic G := by
  let S : Waffle.Similarity.LengthPlane :=
    ⟨G.len,G.axis,G.swap,G.reflect,G.pos,G.homogeneous,hAA⟩
  rintro ⟨a,b⟩
  change (G.len (a,b))^2 = a^2+b^2
  rw [len_abs]
  have ha : |a|^2 = a^2 := sq_abs a
  have hb : |b|^2 = b^2 := sq_abs b
  by_cases haz : a = 0
  · subst a
    rw [abs_zero,G.swap |b| 0,G.axis,abs_abs]
    simpa using hb
  by_cases hbz : b = 0
  · subst b
    rw [abs_zero,G.axis,abs_abs]
    simpa using ha
  have h := Waffle.Similarity.pythagoras S |a| |b|
    (abs_pos.mpr haz) (abs_pos.mpr hbz)
  change |a|^2+|b|^2 = (G.len (|a|,|b|))^2 at h
  rw [ha,hb] at h
  exact h.symm

theorem perp_dot {p q : Vec} (h : Perp p q) : D p q = 0 := by
  obtain ⟨j,rfl⟩ := h
  simp [D,scale,rot]
  ring

theorem q_scale (k : ℝ) (p : Vec) : Q (scale k p) = k^2*Q p := by
  simp [Q,scale]
  ring

theorem q_sub (p q : Vec) : Q (sub p q) = Q p + Q q - 2*D p q := by
  simp [Q,D,sub]
  ring

/-- Converse: the quadratic law implies the local AA product relation.
Only affine perpendicularity and nonnegative length are needed. -/
theorem localAA_of_quadratic (G : BasicLength) (hQ : Quadratic G) :
    LocalAA G := by
  intro p q k t _ _ _ ht h₁ h₂
  have hP : D p q = Q p := by
    have h := perp_dot h₁
    simp [D,Q,sub] at *
    linarith
  have hT : k*D p q = t*Q q := by
    have h := perp_dot h₂
    have hh : t*(k*D p q-t*Q q) = 0 := by
      simp only [D,Q,scale,sub,Prod.fst,Prod.snd] at h ⊢
      linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ht.ne')
  have hcross : D (scale k p) (scale t q) = k*t*D p q := by
    simp [D,scale]
    ring
  have hpoly : Q (sub q p)*Q (scale k p) =
      Q (sub (scale k p) (scale t q))*Q q := by
    simp only [q_sub,q_scale,hcross]
    have hsym : D q p = D p q := by
      simp [D]
      ring
    rw [hsym,hP] at *
    linear_combination -(k*Q p-t*Q q)*hT
  have hsq : (G.len (sub q p)*G.len (scale k p))^2 =
      (G.len (sub (scale k p) (scale t q))*G.len q)^2 := by
    change ∀ p, (G.len p)^2 = Q p at hQ
    simp only [mul_pow,hQ]
    exact hpoly
  have hnon₁ := mul_nonneg (len_nonneg G (sub q p)) (len_nonneg G (scale k p))
  have hnon₂ := mul_nonneg (len_nonneg G (sub (scale k p) (scale t q))) (len_nonneg G q)
  nlinarith

theorem localAA_iff_quadratic (G : BasicLength) :
    LocalAA G ↔ Quadratic G :=
  ⟨quadratic_of_localAA G, localAA_of_quadratic G⟩

/-- A one-parameter slice of AA: one foot is (1,0), one hypotenuse
is (1,x), and the other foot is its projection onto that ray.
No division of lengths is built into this test. -/
def NormalizedTest (G : BasicLength) : Prop :=
  ∀ x : ℝ, 0 < x →
    G.len (0,x)*G.len (1,0) =
      G.len (sub (1,0) (scale (1/(1+x^2)) (1,x)))*G.len (1,x)

theorem normalized_of_localAA (G : BasicLength) (h : LocalAA G) :
    NormalizedTest G := by
  intro x hx
  have hd : 0 < 1+x^2 := by positivity
  have h₁ : Perp (1,0) (sub (1,x) (1,0)) := by
    refine ⟨x,?_⟩
    simp [sub,scale,rot]
  have h₂ : Perp (scale (1/(1+x^2)) (1,x))
      (sub (scale 1 (1,0)) (scale (1/(1+x^2)) (1,x))) := by
    refine ⟨-x,?_⟩
    apply Prod.ext <;> simp [sub,scale,rot] <;> field_simp [hd.ne'] <;> ring
  have hh := h (1,0) (1,x) 1 (1/(1+x^2)) (by norm_num)
    (by norm_num) (by norm_num) (by positivity) h₁ h₂
  simpa [sub,scale] using hh

/-- The single normalized test forces the square law on all positive slopes. -/
theorem normalized_square (G : BasicLength) (h : NormalizedTest G)
    (x : ℝ) (hx : 0 < x) :
    (G.len (1,x))^2 = 1+x^2 := by
  have hd : 0 < 1+x^2 := by positivity
  have hv : sub (1,0) (scale (1/(1+x^2)) (1,x)) =
      scale (x/(1+x^2)) (x,-1) := by
    apply Prod.ext <;> simp [sub,scale] <;> field_simp [hd.ne'] <;> ring
  have hh := h x hx
  rw [G.swap x 0,G.axis,G.axis,abs_of_pos hx,abs_one,hv,G.homogeneous,
    G.reflect,G.swap 1 x,abs_of_pos (div_pos hx hd)] at hh
  field_simp [hd.ne'] at hh
  have he : x*((G.len (1,x))^2-(1+x^2)) = 0 := by
    linear_combination -hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hx.ne')

/-- No general triangle rule is needed to force Euclidean length:
the normalized one-parameter family already suffices. -/
theorem quadratic_of_normalized (G : BasicLength) (h : NormalizedTest G) :
    Quadratic G := by
  rintro ⟨a,b⟩
  change (G.len (a,b))^2 = a^2+b^2
  rw [len_abs]
  have ha : |a|^2 = a^2 := sq_abs a
  have hb : |b|^2 = b^2 := sq_abs b
  by_cases haz : a = 0
  · subst a
    rw [abs_zero,G.swap |b| 0,G.axis,abs_abs]
    simpa using hb
  by_cases hbz : b = 0
  · subst b
    rw [abs_zero,G.axis,abs_abs]
    simpa using ha
  have hap := abs_pos.mpr haz
  have hbp := abs_pos.mpr hbz
  have hv : (|a|,|b|) = scale |a| (1,|b|/|a|) := by
    apply Prod.ext
    · simp [scale]
    · simp [scale]
      field_simp [hap.ne']
  rw [hv,G.homogeneous,abs_abs,mul_pow,normalized_square G h _ (div_pos hbp hap)]
  rw [← ha,← hb]
  field_simp [hap.ne'] <;> ring

theorem normalized_iff_quadratic (G : BasicLength) :
    NormalizedTest G ↔ Quadratic G :=
  ⟨quadratic_of_normalized G,
    fun h => normalized_of_localAA G (localAA_of_quadratic G h)⟩

theorem normalized_iff_localAA (G : BasicLength) :
    NormalizedTest G ↔ LocalAA G :=
  (normalized_iff_quadratic G).trans (localAA_iff_quadratic G).symm

#print axioms normalized_square
#print axioms normalized_iff_quadratic
#print axioms normalized_iff_localAA
#print axioms quadratic_of_localAA
#print axioms localAA_of_quadratic
#print axioms localAA_iff_quadratic
end Waffle.Characterization
