import Waffle.Characterization
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual affine shrinking cone and its boundary lengths.
No local AA rule or area principle is assumed in these results. -/
noncomputable section
namespace Waffle.Chain
open Waffle.Geometry Waffle.Characterization

def ratio (a b : ℝ) := (a/b)^2

def YN (a b : ℝ) (n : ℕ) : Vec :=
  ( (X a b).1 + U a b*ratio a b^n*b,
    (X a b).2 + U a b*ratio a b^n*a )

def ZN (a b : ℝ) (n : ℕ) : Vec :=
  ( (X a b).1 + V a b*ratio a b^n*a,
    (X a b).2 + V a b*ratio a b^n*b )

theorem ratio_bounds (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < ratio a b ∧ ratio a b < 1 := by
  have hb := lt_trans ha hab
  have h := div_pos ha hb
  have h' : a/b < 1 := (div_lt_iff₀ hb).2 (by simpa using hab)
  unfold ratio
  constructor
  · positivity
  · nlinarith [mul_pos (sub_pos.mpr h') (show 0 < 1+a/b by linarith)]

theorem initial (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    YN a b 0 = Y a ∧ ZN a b 0 = Z a := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  constructor
  · apply Prod.ext <;> simp [YN,X,Y] <;> ring
  · apply Prod.ext
    · simp [ZN,X,Z]
      linear_combination -hx
    · simp [ZN,X,Z]
      linear_combination -hy

theorem horizontal_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    sub (YN a b n) (ZN a b n) = (2*a*ratio a b^n,0) := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  apply Prod.ext
  · simp only [sub,YN,ZN,Prod.fst]
    linear_combination (ratio a b^n)*hx
  · simp only [sub,YN,ZN,Prod.snd]
    linear_combination (ratio a b^n)*hy

theorem vertical_step (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    (YN a b (n+1)).1 = (ZN a b n).1 := by
  have hb := lt_trans ha hab
  have hd := denom_pos a b ha hab
  have h : U a b*ratio a b*b = V a b*a := by
    unfold U V ratio
    field_simp [hb.ne',hd.ne'] <;> ring
  simp only [YN,ZN,pow_succ]
  linear_combination (ratio a b^n)*h

theorem right_zigzag (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    Perp (sub (YN a b n) (ZN a b n))
      (sub (YN a b (n+1)) (ZN a b n)) := by
  rw [horizontal_step a b ha hab n]
  have h := vertical_step a b ha hab n
  have hd : 2*a*ratio a b^n ≠ 0 := by
    have := (ratio_bounds a b ha hab).1
    positivity
  refine ⟨((YN a b (n+1)).2-(ZN a b n).2)/(2*a*ratio a b^n),?_⟩
  apply Prod.ext
  · simp [sub,scale,rot,h]
  · simp [sub,scale,rot]
    field_simp [hd]

theorem boundary_steps (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    sub (YN a b n) (YN a b (n+1)) =
      scale ((2*a/b)*ratio a b^n) (b,a) ∧
    sub (ZN a b n) (ZN a b (n+1)) =
      scale (2*ratio a b*ratio a b^n) (a,b) := by
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  have hb := lt_trans ha hab
  obtain ⟨hu,hv⟩ := Waffle.intersection_fixed_points a b (U a b) (V a b) hb.ne' hx hy
  change U a b = 2*a/b+ratio a b*U a b at hu
  change V a b = 2*ratio a b+ratio a b*V a b at hv
  constructor
  · apply Prod.ext
    · simp only [sub,YN,scale,Prod.fst,pow_succ]
      linear_combination (ratio a b^n*b)*hu
    · simp only [sub,YN,scale,Prod.snd,pow_succ]
      linear_combination (ratio a b^n*a)*hu
  · apply Prod.ext
    · simp only [sub,ZN,scale,Prod.fst,pow_succ]
      linear_combination (ratio a b^n*a)*hv
    · simp only [sub,ZN,scale,Prod.snd,pow_succ]
      linear_combination (ratio a b^n*b)*hv

theorem step_lengths (G : BasicLength) (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    G.len (sub (YN a b n) (YN a b (n+1))) =
      ((2*a/b)*G.len (a,b))*ratio a b^n ∧
    G.len (sub (ZN a b n) (ZN a b (n+1))) =
      (2*ratio a b*G.len (a,b))*ratio a b^n := by
  have hb := lt_trans ha hab
  have hr := (ratio_bounds a b ha hab).1
  obtain ⟨hy,hz⟩ := boundary_steps a b ha hab n
  constructor
  · rw [hy,G.homogeneous,G.swap a b,abs_of_pos (by positivity)]
    ring
  · rw [hz,G.homogeneous,abs_of_pos (by positivity)]
    ring

theorem boundary_sums (G : BasicLength) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    HasSum (fun n : ℕ => G.len (sub (YN a b n) (YN a b (n+1)))) (U a b*G.len (a,b)) ∧
    HasSum (fun n : ℕ => G.len (sub (ZN a b n) (ZN a b (n+1)))) (V a b*G.len (a,b)) := by
  have hb := lt_trans ha hab
  obtain ⟨hr,hr1⟩ := ratio_bounds a b ha hab
  obtain ⟨_,_,hx,hy⟩ := scales a b ha hab
  obtain ⟨hu,hv⟩ := Waffle.intersection_fixed_points a b (U a b) (V a b) hb.ne' hx hy
  change U a b = 2*a/b+ratio a b*U a b at hu
  change V a b = 2*ratio a b+ratio a b*V a b at hv
  have hg := hasSum_geometric_of_lt_one hr.le hr1
  have hd : 1-ratio a b ≠ 0 := by linarith
  have eu : (2*a/b*G.len (a,b))*(1-ratio a b)⁻¹ = U a b*G.len (a,b) := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff hd).2
    linear_combination -G.len (a,b)*hu
  have ev : (2*ratio a b*G.len (a,b))*(1-ratio a b)⁻¹ = V a b*G.len (a,b) := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff hd).2
    linear_combination -G.len (a,b)*hv
  constructor
  · have h := hg.mul_left (2*a/b*G.len (a,b))
    rw [eu] at h
    convert h using 1
    funext n
    exact (step_lengths G a b ha hab n).1
  · have h := hg.mul_left (2*ratio a b*G.len (a,b))
    rw [ev] at h
    convert h using 1
    funext n
    exact (step_lengths G a b ha hab n).2

#print axioms initial
#print axioms horizontal_step
#print axioms vertical_step
#print axioms right_zigzag
#print axioms boundary_steps
#print axioms step_lengths
#print axioms boundary_sums
end Waffle.Chain
