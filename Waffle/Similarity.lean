import Waffle.Geometry

/-!
An area-free bridge for the finite cone.
The geometric assumption is a local AA right-triangle similarity rule,
stated as equality of cross-multiplied opposite/hypotenuse ratios.
Unlike the archived global complex multiplication law, it refers only
to two right triangles sharing an acute angle, with their hypotenuses
on opposite rays of that angle. No area function is required.
A derivation of AA from elementary synthetic axioms remains open.
-/

noncomputable section
namespace Waffle.Similarity
open Waffle.Geometry

structure LengthPlane where
  len : Vec → ℝ
  axis : ∀ x, len (x,0) = |x|
  swap : ∀ x y, len (y,x) = len (x,y)
  reflect : ∀ x y, len (x,-y) = len (x,y)
  pos : ∀ p, p ≠ (0,0) → 0 < len p
  homogeneous : ∀ t p, len (scale t p) = |t| * len p
  /-- At the origin, p and q are on the two rays of a common angle.
  The first right triangle has foot p and hypotenuse q.
  The second has foot tq and hypotenuse kp. AA gives equal sines. -/
  common_angle : ∀ (p q : Vec) (k t : ℝ),
    p ≠ (0,0) → q ≠ (0,0) → 0 < k → 0 < t →
    Perp p (sub q p) →
    Perp (scale t q) (sub (scale k p) (scale t q)) →
    len (sub q p) * len (scale k p) =
      len (sub (scale k p) (scale t q)) * len q

theorem len_neg (G : LengthPlane) (p : Vec) :
    G.len (scale (-1) p) = G.len p := by
  rw [G.homogeneous]
  norm_num

theorem len_vertical (G : LengthPlane) (x : ℝ) :
    G.len (0,x) = |x| := by
  rw [G.swap x 0,G.axis]

theorem len_left (G : LengthPlane) (a b : ℝ) :
    G.len (-a,b) = G.len (a,b) := by
  have h : (-a,b) = scale (-1) (a,-b) := by
    apply Prod.ext <;> simp [scale]
  rw [h,len_neg,G.reflect]

/-- For the original acute angle at Y, the first triangle is YMT
and the second is YHZ. The foot H lies on the same ray as T. -/
theorem local_similarity (G : LengthPlane) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    G.len (sub (Z a) (H a b)) * G.len (a,b) = 2*a*b := by
  have hb : 0 < b := lt_trans ha hab
  obtain ⟨_,hv,_,_⟩ := scales a b ha hab
  obtain ⟨_,_,hp⟩ := foot_geometry a b ha hab
  have hn : 1+V a b ≠ 0 := by linarith
  let p : Vec := (-a,0)
  let q : Vec := (-a,b)
  let t : ℝ := V a b/(1+V a b)
  have hq : scale t q = sub (H a b) (Y a) := by
    dsimp [t,q]
    apply Prod.ext <;> simp [scale,sub,H,Y] <;> field_simp [hn] <;> ring
  have hp2 : scale 2 p = sub (Z a) (Y a) := by
    apply Prod.ext <;> simp [p,scale,sub,Z,Y] <;> ring
  have hdiff : sub (scale 2 p) (scale t q) = sub (Z a) (H a b) := by
    rw [hp2,hq]
    apply Prod.ext <;> simp [sub]
  have hqp : sub q p = (0,b) := by
    simp [q,p,sub]
  have hfirst : Perp p (sub q p) := by
    refine ⟨-b/a,?_⟩
    rw [hqp]
    apply Prod.ext <;> simp [p,scale,rot] <;> field_simp [ha.ne']
  have hsecond : Perp (scale t q) (sub (scale 2 p) (scale t q)) := by
    rw [hdiff]
    obtain ⟨j,hj⟩ := hp
    refine ⟨-j/t,?_⟩
    rw [hj]
    have ht : 0 < t := div_pos hv (by linarith)
    apply Prod.ext <;> simp [q,sub,scale,rot,Y,T] <;> field_simp [ht.ne'] <;> ring
  have hpne : p ≠ (0,0) := by
    intro h
    have hh := congrArg Prod.fst h
    dsimp [p] at hh
    linarith
  have hqne : q ≠ (0,0) := by
    intro h
    have hh := congrArg Prod.snd h
    dsimp [q] at hh
    linarith
  have ht : 0 < t := div_pos hv (by linarith)
  have hh := G.common_angle p q 2 t hpne hqne (by norm_num) ht hfirst hsecond
  rw [hqp,hdiff,G.homogeneous,len_vertical,G.axis,abs_of_pos hb] at hh
  change b * (abs (2:ℝ) * abs (-a)) =
    G.len (sub (Z a) (H a b)) * G.len (-a,b) at hh
  rw [len_left] at hh
  norm_num [abs_neg,abs_of_pos ha] at hh
  linear_combination -hh

/-- The sine transfer is a homothety; AA supplies the reflected relation. -/
theorem strict_pythagoras (G : LengthPlane) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) : a^2+b^2 = (G.len (a,b))^2 := by
  obtain ⟨hu,hv,hx,hy⟩ := scales a b ha hab
  obtain ⟨_,hfoot,_⟩ := foot_geometry a b ha hab
  have hc : 0 < G.len (a,b) := G.pos _ (by
    intro h
    exact ha.ne' (congrArg Prod.fst h))
  have hn : 0 < 1+V a b := by linarith
  have hneg : sub (Z a) (H a b) = scale (-1) (sub (H a b) (Z a)) := by
    apply Prod.ext <;> simp [sub,scale]
  have hl : G.len (sub (Z a) (H a b)) =
      (U a b/(1+V a b))*G.len (a,b) := by
    rw [hneg,len_neg,hfoot,G.homogeneous,G.swap a b,abs_of_pos (div_pos hu hn)]
  have hsim := local_similarity G a b ha hab
  let s := G.len (sub (Z a) (H a b))/G.len (a,b)
  have hs : s*(1+V a b) = U a b := by
    dsimp [s]
    rw [hl]
    field_simp [hc.ne',hn.ne'] <;> ring
  have hr : s*(G.len (a,b))^2 = 2*a*b := by
    dsimp [s]
    field_simp [hc.ne']
    linear_combination G.len (a,b)*hsim
  exact Waffle.finite_pythagoras a b _ _ _ s hx hy hs hr (by rw [hs]; exact hu.ne')

/-- At equal legs the reflected triangle itself is right at T;
the common-angle rule still applies, with the second foot equal to T. -/
theorem equal_pythagoras (G : LengthPlane) (a : ℝ) (ha : 0 < a) :
    a^2+a^2 = (G.len (a,a))^2 := by
  let p : Vec := (-a,0)
  let q : Vec := (-a,a)
  have hp : p ≠ (0,0) := by
    intro h
    have hh := congrArg Prod.fst h
    dsimp [p] at hh
    linarith
  have hq : q ≠ (0,0) := by
    intro h
    have hh := congrArg Prod.snd h
    dsimp [q] at hh
    linarith
  have hfirst : Perp p (sub q p) := by
    refine ⟨-1,?_⟩
    apply Prod.ext <;> simp [p,q,sub,scale,rot]
  have hsecond : Perp (scale 1 q) (sub (scale 2 p) (scale 1 q)) := by
    refine ⟨1,?_⟩
    apply Prod.ext <;> simp [p,q,sub,scale,rot] <;> ring
  have h := G.common_angle p q 2 1 hp hq (by norm_num) (by norm_num) hfirst hsecond
  have h1 : sub q p = (0,a) := by simp [p,q,sub]
  have h2 : sub (scale 2 p) (scale 1 q) = scale (-1) (a,a) := by
    apply Prod.ext <;> simp [p,q,sub,scale] <;> ring
  rw [h1,h2,len_vertical,G.homogeneous,len_neg,abs_of_pos ha] at h
  change a*(abs (2:ℝ) * G.len (-a,0)) = G.len (a,a)*G.len (-a,a) at h
  rw [G.axis,len_left] at h
  norm_num [abs_neg,abs_of_pos ha] at h
  nlinarith

theorem pythagoras (G : LengthPlane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2+b^2 = (G.len (a,b))^2 := by
  rcases lt_trichotomy a b with h | h | h
  · exact strict_pythagoras G a b ha h
  · subst b
    exact equal_pythagoras G a ha
  · have h' := strict_pythagoras G b a hb h
    rw [G.swap a b] at h'
    simpa [add_comm] using h'

/-- A concrete witness that axial calibration, symmetry and homogeneity
alone do not supply the local angle rule: taxicab length fails on the
3-4 configuration. The perpendicularity predicates remain affine. -/
theorem taxicab_counterexample :
    let L : Vec → ℝ := fun p => |p.1| + |p.2|
    let p : Vec := (-3,0)
    let q : Vec := (-3,4)
    let t : ℝ := 18/25
    Perp p (sub q p) ∧
    Perp (scale t q) (sub (scale 2 p) (scale t q)) ∧
    L (sub q p) * L (scale 2 p) ≠
      L (sub (scale 2 p) (scale t q)) * L q := by
  dsimp
  constructor
  · refine ⟨-4/3,?_⟩
    norm_num [sub,scale,rot]
  constructor
  · refine ⟨4/3,?_⟩
    norm_num [sub,scale,rot]
  · norm_num [sub,scale,rot,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 96/25),abs_of_nonneg (by norm_num : (0:ℝ) ≤ 72/25)]

#print axioms taxicab_counterexample
#print axioms local_similarity
#print axioms strict_pythagoras
#print axioms equal_pythagoras
#print axioms pythagoras
end Waffle.Similarity
