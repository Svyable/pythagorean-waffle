import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Jackson–Johnson's 2023 waffle-cone proof

A synthetic/affine presentation. The length of a vector is deliberately abstract.
The only geometric postulates are axis normalization, positivity, reflection,
quarter-turn invariance, and the scaling law for a direct similarity. No metric
or inner-product length formula, standard analytic sine, or Pythagorean lemma is
used. `SimilarityPlane` is the explicit foundational interface.

The construction follows C-K Shene, *A New Approach to Proving the Pythagorean
Theorem*, §§3–4 (2024-02-28), with base 2a. The equal-leg case is separate.
-/

noncomputable section
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace JacksonJohnson

abbrev Vec := ℝ × ℝ

def add (u v : Vec) : Vec := (u.1 + v.1, u.2 + v.2)
def sub (u v : Vec) : Vec := (u.1 - v.1, u.2 - v.2)
def neg (u : Vec) : Vec := (-u.1, -u.2)
def scale (k : ℝ) (u : Vec) : Vec := (k * u.1, k * u.2)
def dot (u v : Vec) : ℝ := u.1 * v.1 + u.2 * v.2
def cross (u v : Vec) : ℝ := u.1 * v.2 - u.2 * v.1

/-- A length function subject to elementary Euclidean similarity postulates.
The last field expresses that the map (x,y) ↦ (p*x-q*y,q*x+p*y)
is a direct similarity whose scale is the length of the image of (1,0).
It is a geometric postulate, not a theorem about Mathlib's Euclidean norm. -/
structure SimilarityPlane where
  len : ℝ → ℝ → ℝ
  axis : ∀ x : ℝ, len x 0 = |x|
  pos : ∀ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) → 0 < len x y
  mirror : ∀ x y : ℝ, len x (-y) = len x y
  quarter : ∀ x y : ℝ, len (-y) x = len x y
  similarity : ∀ p q x y : ℝ,
    len (p*x-q*y) (q*x+p*y) = len p q * len x y

def length (G : SimilarityPlane) (u : Vec) : ℝ := G.len u.1 u.2

/-- Sine of the angle between two rays, by the opposite / hypotenuse
ratio in a rotated coordinate frame. The coordinates of the second ray in
that frame are proportional to (dot, cross); no unit-circle identity is used.
The zero-ray cases are irrelevant to the geometric theorems below. -/
def sine (G : SimilarityPlane) (u v : Vec) : ℝ :=
  |cross u v| / G.len (dot u v) (cross u v)

variable (G : SimilarityPlane)

theorem vertical (x : ℝ) : G.len 0 x = |x| := by
  calc
    G.len 0 x = G.len x 0 := by simpa using G.quarter x 0
    _ = |x| := G.axis x

theorem length_scale (k : ℝ) (u : Vec) :
    length G (scale k u) = |k| * length G u := by
  simpa [length, scale, G.axis] using G.similarity k 0 u.1 u.2

theorem length_neg (u : Vec) : length G (neg u) = length G u := by
  simpa [neg, scale] using length_scale G (-1) u

theorem len_swap (a b : ℝ) : G.len b a = G.len a b := by
  calc
    G.len b a = G.len a (-b) := by simpa using G.quarter a (-b)
    _ = G.len a b := G.mirror a b

theorem len_neg_x (a b : ℝ) : G.len (-a) b = G.len a b := by
  calc
    G.len (-a) b = G.len a (-b) := by
      simpa [length, neg] using length_neg G (a, -b)
    _ = G.len a b := G.mirror a b

/-- The denominator is the length of a ray after a direct similarity.
This is the only use of the general similarity postulate in the sine theory. -/
theorem rotated_length (u v : Vec) :
    G.len (dot u v) (cross u v) = length G u * length G v := by
  have h := G.similarity u.1 (-u.2) v.1 v.2
  rw [G.mirror] at h
  calc
    G.len (dot u v) (cross u v) =
        G.len (u.1*v.1-(-u.2)*v.2) ((-u.2)*v.1+u.1*v.2) := by
          congr 1 <;> simp [dot, cross] <;> ring
    _ = length G u * length G v := h

theorem sine_eq (u v : Vec) :
    sine G u v = |cross u v| / (length G u * length G v) := by
  unfold sine
  rw [rotated_length G u v]

theorem sine_right (u v : Vec) (hperp : dot u v = 0)
    (hcross : cross u v ≠ 0) : sine G u v = 1 := by
  rw [sine, hperp, vertical]
  exact div_self (abs_ne_zero.mpr hcross)

/-- Scaling a ray does not change its (unsigned) angle sine. -/
theorem sine_scale_right (u v : Vec) (k : ℝ) (hk : 0 < k)
    (hu : length G u ≠ 0) (hv : length G v ≠ 0) :
    sine G u (scale k v) = sine G u v := by
  have h : cross u (scale k v) = k * cross u v := by
    simp [cross, scale] <;> ring
  simp only [sine_eq, h, abs_mul, length_scale, abs_of_pos hk]
  field_simp [hk.ne', hu, hv] <;> ring

/-- Law of Sines, in cross-multiplied form, for vertices 0, u, v.
The same unsigned determinant is twice the coordinate area at either vertex.
The proof uses only the sine ratio and similarity; it does not assume the
Law of Sines as a hypothesis. -/
theorem law_of_sines (u v : Vec) (hu : length G u ≠ 0)
    (hv : length G v ≠ 0) (hw : length G (sub v u) ≠ 0) :
    sine G u v * length G v =
      sine G (neg u) (sub v u) * length G (sub v u) := by
  have h : cross (neg u) (sub v u) = -cross u v := by
    simp [cross, neg, sub] <;> ring
  simp only [sine_eq, h, abs_neg, length_neg]
  field_simp [hu, hv, hw] <;> ring

/-! ## The actual infinite waffle-cone construction -/

def ratio (a b : ℝ) : ℝ := (a/b)^2
/-- Total scaling along the Y and Z cone boundaries. -/
def sy (a b : ℝ) : ℝ := (2*a/b)/(1-ratio a b)
def sz (a b : ℝ) : ℝ := (2*ratio a b)/(1-ratio a b)

theorem ratio_bounds (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < ratio a b ∧ ratio a b < 1 := by
  have hb : 0 < b := lt_trans ha hab
  have ht : 0 < a/b := div_pos ha hb
  have ht' : a/b < 1 := (div_lt_iff₀ hb).2 (by simpa using hab)
  unfold ratio
  constructor
  · positivity
  · nlinarith [mul_pos (sub_pos.mpr ht') (show 0 < 1+a/b by linarith)]

theorem scales_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < sy a b ∧ 0 < sz a b := by
  have hb : 0 < b := lt_trans ha hab
  obtain ⟨hr, hr'⟩ := ratio_bounds a b ha hab
  have hd : 0 < 1-ratio a b := sub_pos.mpr hr'
  unfold sy sz
  constructor <;> positivity

/-- The two boundary rays meet at a common point. -/
theorem scale_relations (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    sy a b*b - sz a b*a = 2*a ∧ sy a b*a = sz a b*b := by
  have hb : 0 < b := lt_trans ha hab
  have hd : 1-(a/b)^2 ≠ 0 := by
    have h := (ratio_bounds a b ha hab).2
    unfold ratio at h
    linarith
  constructor <;> unfold sy sz ratio <;>
    field_simp [hb.ne', hd] <;> ring

/-- The cone apex X; the original reflected triangle has vertices
T=(0,b), Y₀=(a,0), Z₀=(-a,0). -/
def apex (a b : ℝ) : Vec := (a-sy a b*b, -sy a b*a)
def Y (a b : ℝ) (n : ℕ) : Vec :=
  add (apex a b) (scale (sy a b * ratio a b ^ n) (b,a))
def Z (a b : ℝ) (n : ℕ) : Vec :=
  add (apex a b) (scale (sz a b * ratio a b ^ n) (a,b))

theorem Y_zero (a b : ℝ) : Y a b 0 = (a,0) := by
  apply Prod.ext <;> simp [Y, add, apex, scale] <;> ring

theorem Z_zero (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Z a b 0 = (-a,0) := by
  obtain ⟨h₁,h₂⟩ := scale_relations a b ha hab
  apply Prod.ext
  · simp [Z, add, apex, scale] <;> linear_combination -h₁
  · simp [Z, add, apex, scale] <;> linear_combination -h₂

/-- Each horizontal cross-section is parallel to the initial base. -/
theorem horizontal (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    (Y a b n).2 = (Z a b n).2 := by
  have h := (scale_relations a b ha hab).2
  simp only [Y, Z, add, scale]
  linear_combination (ratio a b ^ n) * h

/-- The base width at level n is the original width multiplied by r^n. -/
theorem base_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    sub (Y a b n) (Z a b n) = (2*a*ratio a b^n,0) := by
  obtain ⟨h₁,h₂⟩ := scale_relations a b ha hab
  apply Prod.ext
  · simp only [Y, Z, add, sub, scale]
    linear_combination (ratio a b^n) * h₁
  · simp only [Y, Z, add, sub, scale]
    linear_combination (ratio a b^n) * h₂

/-- The intervening cross-section is perpendicular to the base:
Z_n and Y_(n+1) have identical first coordinate. -/
theorem vertical_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    (Y a b (n+1)).1 = (Z a b n).1 := by
  have hb : 0 < b := lt_trans ha hab
  have hd : 1-(a/b)^2 ≠ 0 := by
    have h := (ratio_bounds a b ha hab).2
    unfold ratio at h
    linarith
  have h : sy a b * ratio a b * b = sz a b * a := by
    unfold sy sz ratio
    field_simp [hb.ne', hd] <;> ring
  simp only [Y, Z, add, scale, pow_succ]
  linear_combination (ratio a b ^ n) * h

/-- Explicit homothety of successive boundary points about X. -/
theorem Y_homothety (a b : ℝ) (n : ℕ) :
    sub (Y a b (n+1)) (apex a b) =
      scale (ratio a b) (sub (Y a b n) (apex a b)) := by
  apply Prod.ext <;> simp [Y, add, sub, scale, pow_succ] <;> ring

theorem Z_homothety (a b : ℝ) (n : ℕ) :
    sub (Z a b (n+1)) (apex a b) =
      scale (ratio a b) (sub (Z a b n) (apex a b)) := by
  apply Prod.ext <;> simp [Z, add, sub, scale, pow_succ] <;> ring

/-- Both step vectors are scalar multiples of the original triangle's
hypotenuse directions; the multiplier decreases by ratio at each step. -/
theorem Y_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    sub (Y a b n) (Y a b (n+1)) =
      scale ((2*a/b)*ratio a b^n) (b,a) := by
  have hd : 1-ratio a b ≠ 0 := by
    linarith [(ratio_bounds a b ha hab).2]
  have h : sy a b * (1-ratio a b) = 2*a/b := by
    unfold sy
    field_simp [hd] <;> ring
  apply Prod.ext
  · simp only [Y, add, sub, scale, pow_succ]
    linear_combination (ratio a b^n*b) * h
  · simp only [Y, add, sub, scale, pow_succ]
    linear_combination (ratio a b^n*a) * h

theorem Z_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    sub (Z a b n) (Z a b (n+1)) =
      scale ((2*ratio a b)*ratio a b^n) (a,b) := by
  have hd : 1-ratio a b ≠ 0 := by
    linarith [(ratio_bounds a b ha hab).2]
  have h : sz a b * (1-ratio a b) = 2*ratio a b := by
    unfold sz
    field_simp [hd] <;> ring
  apply Prod.ext
  · simp only [Z, add, sub, scale, pow_succ]
    linear_combination (ratio a b^n*a) * h
  · simp only [Z, add, sub, scale, pow_succ]
    linear_combination (ratio a b^n*b) * h

/-- Convergence and exact sum of the lengths of the boundary segments.
In particular, no convergence or closed-form side length is assumed. -/
theorem cone_side_sums (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    HasSum (fun n : ℕ => length G (sub (Y a b n) (Y a b (n+1))))
      (sy a b * G.len a b) ∧
    HasSum (fun n : ℕ => length G (sub (Z a b n) (Z a b (n+1))))
      (sz a b * G.len a b) := by
  have hb : 0 < b := lt_trans ha hab
  obtain ⟨hr, hr'⟩ := ratio_bounds a b ha hab
  have hs := hasSum_geometric_of_lt_one hr.le hr'
  have hy (n : ℕ) : length G (sub (Y a b n) (Y a b (n+1))) =
      ((2*a/b)*G.len a b) * ratio a b^n := by
    rw [Y_step a b ha hab, length_scale]
    have hp : 0 ≤ (2*a/b)*ratio a b^n := by positivity
    rw [abs_of_nonneg hp]
    simp only [length, len_swap G a b] <;> ring
  have hz (n : ℕ) : length G (sub (Z a b n) (Z a b (n+1))) =
      ((2*ratio a b)*G.len a b) * ratio a b^n := by
    rw [Z_step a b ha hab, length_scale]
    have hp : 0 ≤ (2*ratio a b)*ratio a b^n := by positivity
    rw [abs_of_nonneg hp]
    simp only [length] <;> ring
  constructor
  · have h := hs.mul_left ((2*a/b)*G.len a b)
    convert h using 1
    · funext n; exact hy n
    · unfold sy; rw [div_eq_mul_inv]; ring
  · have h := hs.mul_left ((2*ratio a b)*G.len a b)
    convert h using 1
    · funext n; exact hz n
    · unfold sz; rw [div_eq_mul_inv]; ring

/-! ## Two computations of the same sine -/

/-- The two rays from T=(0,b) to the reflected base endpoints. -/
def u (a b : ℝ) : Vec := (a,-b)
def v (a b : ℝ) : Vec := (-a,-b)
def w (a b : ℝ) : Vec := sub (apex a b) (0,b)

theorem u_length (a b : ℝ) : length G (u a b) = G.len a b := by
  exact G.mirror a b

theorem v_length (a b : ℝ) : length G (v a b) = G.len a b := by
  simpa [length, v, neg] using length_neg G (a,b)

theorem base_length (a b : ℝ) (ha : 0 < a) :
    length G (sub (v a b) (u a b)) = 2*a := by
  change G.len (-a-a) (-b-(-b)) = 2*a
  rw [show -b-(-b) = 0 by ring, G.axis, abs_of_nonpos (by linarith : -a-a ≤ 0)]
  ring

/-- The base angle β of the reflected triangle, by the sine ratio. -/
theorem beta_sine (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sine G (neg (u a b)) (sub (v a b) (u a b)) = b/G.len a b := by
  have hc : 0 < G.len a b := G.pos a b (Or.inl ha.ne')
  have hcross : cross (neg (u a b)) (sub (v a b) (u a b)) = 2*a*b := by
    simp [cross, neg, sub, u, v] <;> ring
  rw [sine_eq, hcross, length_neg, u_length, base_length G a b ha,
    abs_of_pos (by positivity : 0 < 2*a*b)]
  field_simp [ha.ne', hc.ne'] <;> ring

/-- First computation: the reflected isosceles triangle and the Law of Sines. -/
theorem reflected_sine (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    sine G (u a b) (v a b) = 2*a*b/(G.len a b)^2 := by
  have hc : 0 < G.len a b := G.pos a b (Or.inl ha.ne')
  have hu : length G (u a b) ≠ 0 := by rw [u_length]; exact hc.ne'
  have hv : length G (v a b) ≠ 0 := by rw [v_length]; exact hc.ne'
  have hbase : length G (sub (v a b) (u a b)) ≠ 0 := by
    rw [base_length G a b ha]; positivity
  have h := law_of_sines G (u a b) (v a b) hu hv hbase
  rw [v_length, beta_sine G a b ha hb, base_length G a b ha] at h
  calc
    sine G (u a b) (v a b) = (b/G.len a b*(2*a))/G.len a b :=
      (eq_div_iff hc.ne').2 h
    _ = 2*a*b/(G.len a b)^2 := by field_simp [hc.ne'] <;> ring

/-- The extended side TX is the same ray as TZ. -/
theorem w_eq (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    w a b = scale (1+sz a b) (v a b) := by
  obtain ⟨h₁,h₂⟩ := scale_relations a b ha hab
  apply Prod.ext
  · simp [w, apex, sub, scale, v] <;> linear_combination -h₁
  · simp [w, apex, sub, scale, v] <;> linear_combination -h₂

/-- The side Y₀X is perpendicular to TY₀. -/
theorem cone_leg_eq (a b : ℝ) :
    sub (w a b) (u a b) = scale (sy a b) (-b,-a) := by
  apply Prod.ext <;> simp [w, apex, sub, scale, u] <;> ring

theorem cone_right (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    sine G (neg (u a b)) (sub (w a b) (u a b)) = 1 := by
  have hb : 0 < b := lt_trans ha hab
  have hs := (scales_pos a b ha hab).1
  apply sine_right G
  · rw [cone_leg_eq]; simp [dot, neg, scale, u] <;> ring
  · rw [cone_leg_eq]
    have h : cross (neg (u a b)) (scale (sy a b) (-b,-a)) =
        sy a b * (a^2+b^2) := by simp [cross, neg, scale, u] <;> ring
    rw [h]
    exact ne_of_gt (mul_pos hs (by positivity))

/-- The geometric side lengths from the sums, including the initial side c
on the long boundary. These equalities link the series to actual segments. -/
theorem cone_lengths (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    length G (sub (w a b) (u a b)) =
      (∑' n : ℕ, length G (sub (Y a b n) (Y a b (n+1)))) ∧
    length G (w a b) = G.len a b +
      (∑' n : ℕ, length G (sub (Z a b n) (Z a b (n+1)))) := by
  obtain ⟨hs,ht⟩ := scales_pos a b ha hab
  obtain ⟨hy,hz⟩ := cone_side_sums G a b ha hab
  have hn : length G (-b,-a) = G.len a b := by
    calc
      length G (-b,-a) = length G (b,a) := length_neg G (b,a)
      _ = G.len a b := len_swap G a b
  constructor
  · rw [cone_leg_eq, length_scale, abs_of_pos hs, hn, hy.tsum_eq]
  · rw [w_eq a b ha hab, length_scale, abs_of_pos (by linarith : 0 < 1+sz a b),
      v_length, hz.tsum_eq]
    ring

/-- Second computation: the large right triangle and the two geometric series. -/
theorem waffle_cone_sine (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    sine G (u a b) (v a b) = 2*a*b/(a^2+b^2) := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < G.len a b := G.pos a b (Or.inl ha.ne')
  obtain ⟨hs,ht⟩ := scales_pos a b ha hab
  obtain ⟨hy,hz⟩ := cone_side_sums G a b ha hab
  obtain ⟨hleg,hlong⟩ := cone_lengths G a b ha hab
  rw [hy.tsum_eq] at hleg
  rw [hz.tsum_eq] at hlong
  have hu : length G (u a b) ≠ 0 := by rw [u_length]; exact hc.ne'
  have hv : length G (v a b) ≠ 0 := by rw [v_length]; exact hc.ne'
  have hw : 0 < length G (w a b) := by rw [hlong]; positivity
  have hleg' : 0 < length G (sub (w a b) (u a b)) := by rw [hleg]; positivity
  have hsame : sine G (u a b) (w a b) = sine G (u a b) (v a b) := by
    rw [w_eq a b ha hab]
    exact sine_scale_right G _ _ _ (by linarith) hu hv
  have h := law_of_sines G (u a b) (w a b) hu hw.ne' hleg'.ne'
  rw [hsame, cone_right G a b ha hab, one_mul] at h
  have hd : 1-(a/b)^2 ≠ 0 := by
    have hr := (ratio_bounds a b ha hab).2
    unfold ratio at hr
    linarith
  have hab2 : a^2+b^2 ≠ 0 := ne_of_gt (by positivity)
  calc
    sine G (u a b) (v a b) =
        length G (sub (w a b) (u a b)) / length G (w a b) :=
      (eq_div_iff hw.ne').2 h
    _ = (sy a b * G.len a b)/(G.len a b+sz a b*G.len a b) := by
      rw [hleg, hlong]
    _ = sy a b / (1+sz a b) := by
      have h₁ : 1+sz a b ≠ 0 := by linarith
      have h₂ : G.len a b+sz a b*G.len a b ≠ 0 := by positivity
      field_simp [h₁,h₂] <;> ring
    _ = 2*a*b/(a^2+b^2) := by
      have h₁ : 1+sz a b ≠ 0 := by linarith
      -- Cross-multiply before expanding the scale definitions.
      apply (div_eq_div_iff h₁ hab2).2
      unfold sy sz ratio
      field_simp [hb.ne',hd] <;> ring

/-! ## Pythagoras, including the isosceles and swapped-leg cases -/

theorem pythagoras_strict (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a^2+b^2 = (G.len a b)^2 := by
  have hb : 0 < b := lt_trans ha hab
  have hc : 0 < G.len a b := G.pos a b (Or.inl ha.ne')
  have h₁ : a^2+b^2 ≠ 0 := ne_of_gt (by positivity)
  have h₂ : (G.len a b)^2 ≠ 0 := pow_ne_zero _ hc.ne'
  have h := (waffle_cone_sine G a b ha hab).symm.trans (reflected_sine G a b ha hb)
  have h' := (div_eq_div_iff h₁ h₂).1 h
  have hn : 2*a*b ≠ 0 := ne_of_gt (by positivity)
  exact (mul_left_cancel₀ hn h').symm

/-- The infinite cone degenerates for equal legs, but the reflected apex
angle is then a right angle; the same sine-law computation still applies. -/
theorem pythagoras_equal (a : ℝ) (ha : 0 < a) :
    a^2+a^2 = (G.len a a)^2 := by
  have hc : 0 < G.len a a := G.pos a a (Or.inl ha.ne')
  have hperp : dot (u a a) (v a a) = 0 := by
    simp [dot,u,v] <;> ring
  have hcross : cross (u a a) (v a a) ≠ 0 := by
    have h : cross (u a a) (v a a) = -(2*a*a) := by
      simp [cross,u,v] <;> ring
    rw [h]
    exact neg_ne_zero.mpr (ne_of_gt (by positivity))
  have h := (sine_right G _ _ hperp hcross).symm.trans (reflected_sine G a a ha ha)
  have h' := (eq_div_iff (pow_ne_zero 2 hc.ne')).1 h
  linarith [show 2*a*a = a^2+a^2 by ring]

/-- Main theorem, with no Pythagorean equality in the hypotheses. -/
theorem pythagoras (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2+b^2 = (G.len a b)^2 := by
  rcases lt_trichotomy a b with h | h | h
  · exact pythagoras_strict G a b ha h
  · subst b; exact pythagoras_equal G a ha
  · have h' := pythagoras_strict G b a hb h
    rw [len_swap G a b] at h'
    simpa [add_comm] using h'

/-- The original textbook statement with an explicitly named hypotenuse c. -/
theorem pythagorean_theorem_jackson_johnson (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : c = G.len a b) :
    a^2+b^2 = c^2 := by
  rw [hc]
  exact pythagoras G a b ha hb

#print axioms pythagorean_theorem_jackson_johnson

end JacksonJohnson