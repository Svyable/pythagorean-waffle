import Waffle

/-!
An intermediate geometric bridge, not a derivation from Tarski axioms.
The only length assumptions are axial calibration, symmetry, positivity and
homogeneity. An abstract area satisfies cyclic invariance and the
base-times-altitude formula for perpendicular feet on the entire base line.
Perpendicularity below is defined by quarter-turn directions, not a metric.
-/

noncomputable section

namespace Waffle.Geometry

abbrev Vec := ℝ × ℝ
def sub (p q : Vec) : Vec := (p.1-q.1, p.2-q.2)
def scale (t : ℝ) (p : Vec) : Vec := (t*p.1,t*p.2)
def rot (p : Vec) : Vec := (-p.2,p.1)
def OnLine (p q h : Vec) : Prop :=
  ∃ t : ℝ, sub h p = scale t (sub q p)
def Perp (p q : Vec) : Prop := ∃ t : ℝ, q = scale t (rot p)

structure AreaPlane where
  len : Vec → ℝ
  axis : ∀ x, len (x,0) = |x|
  swap : ∀ x y, len (y,x) = len (x,y)
  reflect : ∀ x y, len (x,-y) = len (x,y)
  pos : ∀ p, p ≠ (0,0) → 0 < len p
  homogeneous : ∀ t p, len (scale t p) = |t| * len p
  area : Vec → Vec → Vec → ℝ
  cyclic : ∀ p q r, area p q r = area q r p
  base_height : ∀ p q r h, OnLine p q h → Perp (sub q p) (sub r h) →
    area p q r = len (sub q p) * len (sub r h) / 2

def T (b : ℝ) : Vec := (0,b)
def Y (a : ℝ) : Vec := (a,0)
def Z (a : ℝ) : Vec := (-a,0)
def M : Vec := (0,0)
def U (a b : ℝ) : ℝ := 2*a*b/(b^2-a^2)
def V (a b : ℝ) : ℝ := 2*a^2/(b^2-a^2)
def X (a b : ℝ) : Vec := (a-U a b*b,-U a b*a)
def H (a b : ℝ) : Vec := (a/(1+V a b), b-b/(1+V a b))

theorem denom_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < b^2-a^2 := by
  nlinarith [mul_pos (sub_pos.mpr hab) (show 0 < b+a by linarith)]

theorem scales (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < U a b ∧ 0 < V a b ∧
    U a b*b-V a b*a = 2*a ∧ U a b*a = V a b*b := by
  have hb : 0 < b := lt_trans ha hab
  have hd := denom_pos a b ha hab
  unfold U V
  refine ⟨by positivity, by positivity, ?_, ?_⟩ <;>
    field_simp [hd.ne'] <;> ring

/-- X lies on the extended reflected side, and YX is perpendicular to TY. -/
theorem apex_geometry (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    sub (X a b) (Z a) = scale (-V a b) (a,b) ∧
    sub (Y a) (X a b) = scale (U a b) (b,a) ∧
    Perp (sub (Y a) (T b)) (sub (Y a) (X a b)) := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  have h₁ : sub (X a b) (Z a) = scale (-V a b) (a,b) := by
    apply Prod.ext
    · simp [sub, X, Z, scale]
      linarith
    · simp [sub, X, Z, scale]
      linarith
  have h₂ : sub (Y a) (X a b) = scale (U a b) (b,a) := by
    apply Prod.ext <;> simp [sub, Y, X, scale]
  refine ⟨h₁,h₂, U a b, ?_⟩
  rw [h₂]
  congr 1
  simp [rot, sub, Y, T]

/-- H is the altitude foot of Z onto TY, constructed by affine scaling.
Its altitude vector is the scaled cone leg, without any metric formula. -/
theorem foot_geometry (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    OnLine (T b) (Y a) (H a b) ∧
    sub (H a b) (Z a) = scale (U a b/(1+V a b)) (b,a) ∧
    Perp (sub (Y a) (T b)) (sub (Z a) (H a b)) := by
  obtain ⟨_,hv,hx,hy⟩ := scales a b ha hab
  have hn : 1+V a b ≠ 0 := by linarith
  have h₁ : OnLine (T b) (Y a) (H a b) := by
    refine ⟨1/(1+V a b), ?_⟩
    apply Prod.ext <;> simp [sub, T, Y, H, scale] <;> ring
  have h₂ : sub (H a b) (Z a) = scale (U a b/(1+V a b)) (b,a) := by
    apply Prod.ext
    · simp [sub, H, Z, scale]
      field_simp [hn]
      linear_combination -hx
    · simp [sub, H, Z, scale]
      field_simp [hn]
      linear_combination -hy
  refine ⟨h₁,h₂, -(U a b/(1+V a b)), ?_⟩
  have h₃ : sub (Z a) (H a b) = scale (-1) (sub (H a b) (Z a)) := by
    apply Prod.ext <;> simp [sub, scale]
  rw [h₃,h₂]
  apply Prod.ext <;> simp [rot, sub, Y, T, scale]

/-- The cone hypotenuse is an extension of TZ, with positive factor 1+V. -/
theorem hypotenuse_geometry (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    sub (T b) (X a b) = scale (1+V a b) (a,b) := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  apply Prod.ext
  · simp [sub,T,X,scale]
    linear_combination hx
  · simp [sub,T,X,scale]
    linear_combination hy

/-- The two right triangles share the same sine: the reflected altitude
ratio equals the opposite/hypotenuse ratio in the finite cone. -/
theorem cone_angle_transfer (G : AreaPlane) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    G.len (sub (Z a) (H a b))/G.len (a,b) =
      G.len (sub (Y a) (X a b))/G.len (sub (T b) (X a b)) := by
  obtain ⟨hu,hv,_,_⟩ := scales a b ha hab
  obtain ⟨_,hleg,_⟩ := apex_geometry a b ha hab
  obtain ⟨_,hfoot,_⟩ := foot_geometry a b ha hab
  have hc : 0 < G.len (a,b) := G.pos _ (by
    intro h
    exact ha.ne' (congrArg Prod.fst h))
  have hn : 0 < 1+V a b := by linarith
  have hneg : sub (Z a) (H a b) = scale (-1) (sub (H a b) (Z a)) := by
    apply Prod.ext <;> simp [sub,scale]
  rw [hneg,G.homogeneous,hfoot,G.homogeneous,G.swap a b,
    hleg,G.homogeneous,G.swap a b,hypotenuse_geometry a b ha hab,G.homogeneous]
  rw [abs_of_pos (div_pos hu hn),abs_of_pos hu,abs_of_pos hn]
  norm_num
  field_simp [hc.ne',hn.ne']

/-- The area of the reflected triangle measured from its horizontal base. -/
theorem reflected_area (G : AreaPlane) (a b : ℝ) (ha : 0 < a)
    (hb : 0 < b) : G.area (T b) (Y a) (Z a) = a*b := by
  have hl : OnLine (Y a) (Z a) M := by
    refine ⟨1/2, ?_⟩
    apply Prod.ext <;> simp [OnLine, sub, Y, Z, M, scale] <;> ring
  have hp : Perp (sub (Z a) (Y a)) (sub (T b) M) := by
    refine ⟨-b/(2*a), ?_⟩
    apply Prod.ext <;> simp [Perp, sub, Y, Z, T, M, scale, rot]
    field_simp [ha.ne'] <;> ring
  rw [G.cyclic (T b) (Y a) (Z a), G.base_height _ _ _ _ hl hp]
  change G.len (-a-a,0-0) * G.len (0-0,b-0) / 2 = a*b
  simp only [sub_zero, G.axis]
  rw [G.swap b 0, G.axis, abs_of_pos hb, abs_of_neg (by linarith : -a-a < 0)]
  ring

/-- The reflected sine is its opposite altitude divided by the equal side c.
Both sine equations are derived from the geometric bridge assumptions. -/
theorem reflected_sine (G : AreaPlane) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    let c := G.len (a,b)
    let s := G.len (sub (Z a) (H a b))/c
    s*(1+V a b) = U a b ∧ s*c^2 = 2*a*b ∧ s*(1+V a b) ≠ 0 := by
  dsimp
  obtain ⟨hu,hv,_,_⟩ := scales a b ha hab
  obtain ⟨hl,hvec,hp⟩ := foot_geometry a b ha hab
  have hc : 0 < G.len (a,b) := G.pos _ (by
    intro h
    have := congrArg Prod.fst h
    exact ha.ne' this)
  have hty : G.len (sub (Y a) (T b)) = G.len (a,b) := by
    simpa [sub,Y,T] using G.reflect a b
  have hneg : sub (Z a) (H a b) = scale (-1) (sub (H a b) (Z a)) := by
    apply Prod.ext <;> simp [sub,scale]
  have hlength : G.len (sub (Z a) (H a b)) =
      (U a b/(1+V a b))*G.len (a,b) := by
    rw [hneg,G.homogeneous,hvec,G.homogeneous,G.swap a b]
    rw [abs_of_pos (div_pos hu (by linarith))]
    norm_num
  have harea := G.base_height _ _ _ _ hl hp
  rw [reflected_area G a b ha (lt_trans ha hab),hty] at harea
  have hs : G.len (sub (Z a) (H a b))/G.len (a,b)*(1+V a b) = U a b := by
    rw [hlength]
    field_simp [hc.ne',show 1+V a b ≠ 0 by linarith] <;> ring
  refine ⟨hs,?_,?_⟩
  · field_simp [hc.ne']
    linear_combination -2*harea*G.len (a,b)
  · rw [hs]
    exact hu.ne'

theorem strict_pythagoras (G : AreaPlane) (a b : ℝ) (ha : 0 < a)
    (hab : a < b) : a^2+b^2 = (G.len (a,b))^2 := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  obtain ⟨hs,hr,hn⟩ := reflected_sine G a b ha hab
  exact Waffle.finite_pythagoras a b _ _ _ _ hx hy hs hr hn

/-- The cone degenerates at equal legs; the reflected triangle itself
has a right angle, so its area is half the product of its equal sides. -/
theorem equal_pythagoras (G : AreaPlane) (a : ℝ) (ha : 0 < a) :
    a^2+a^2 = (G.len (a,a))^2 := by
  have hl : OnLine (T a) (Y a) (T a) := by
    refine ⟨0, ?_⟩
    simp [sub,scale]
  have hp : Perp (sub (Y a) (T a)) (sub (Z a) (T a)) := by
    refine ⟨-1, ?_⟩
    apply Prod.ext <;> simp [sub,rot,scale,Y,Z,T]
  have harea := G.base_height _ _ _ _ hl hp
  have hty : G.len (sub (Y a) (T a)) = G.len (a,a) := by
    simpa [sub,Y,T] using G.reflect a a
  have htz : sub (Z a) (T a) = scale (-1) (a,a) := by
    apply Prod.ext <;> simp [sub,scale,Z,T]
  rw [reflected_area G a a ha ha,hty,htz,G.homogeneous] at harea
  norm_num at harea
  linarith

theorem pythagoras (G : AreaPlane) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a^2+b^2 = (G.len (a,b))^2 := by
  rcases lt_trichotomy a b with h | h | h
  · exact strict_pythagoras G a b ha h
  · subst b
    exact equal_pythagoras G a ha
  · have h' := strict_pythagoras G b a hb h
    rw [G.swap a b] at h'
    simpa [add_comm] using h'

#print axioms apex_geometry
#print axioms foot_geometry
#print axioms hypotenuse_geometry
#print axioms cone_angle_transfer
#print axioms reflected_area
#print axioms reflected_sine
#print axioms pythagoras

end Waffle.Geometry
