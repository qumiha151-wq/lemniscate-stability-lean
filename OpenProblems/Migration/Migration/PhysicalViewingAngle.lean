import Migration.ExteriorAperture
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Set
namespace MigrationGeometry.Adjoint.ClosedExpander
variable {rate L : ℝ} (c : ClosedExpander rate L)

/-- The actual polar angle in a given oriented orthonormal frame when
    the image lies in its open right half-plane. -/
def viewingAngle (a b s : ℝ) : ℝ :=
  Real.arctan ((-b*c.x s+a*c.y s)/(a*c.x s+b*c.y s))

private theorem polar_components {x y r : ℝ} (hx : 0<x) (hr : 0<r)
    (sq : x^2+y^2=r^2) :
    r*Real.cos (Real.arctan (y/x))=x ∧ r*Real.sin (Real.arctan (y/x))=y := by
  have root : Real.sqrt (1+(y/x)^2)=r/x := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg hr.le hx.le)).mpr
    field_simp
    linarith
  rw [Real.cos_arctan,Real.sin_arctan,root]
  constructor <;> field_simp

private theorem fourth_root_bound {D k : ℝ} (dp : 0≤D) (kp : 0<k) (h : 1<k*D^4) :
    k^(-(1:ℝ)/4) < D := by
  have root : (k^(-(1:ℝ)/4))^4 = k⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul kp.le]
    norm_num
    exact Real.rpow_neg_one k
  by_contra! small
  have le := pow_le_pow_left₀ dp small 4
  rw [root] at le
  have hi := mul_le_mul_of_nonneg_left le kp.le
  rw [mul_inv_cancel₀ kp.ne'] at hi
  linarith

/-- Extrema of the actual single-valued polar argument and of the actual
    radius are attained on one whole period. Their width w and maximum
    radius R satisfy R sin(w/2) > (2 rate)^(-1/4). -/
theorem external_viewing_angle_bound {a b : ℝ} (ha : 0<rate) (hL : 0<L)
    (unit : a^2+b^2=1) (sep : ∀ s, 0<a*c.x s+b*c.y s) :
    ∃ lo∈Icc (0:ℝ) L, ∃ hi∈Icc (0:ℝ) L, ∃ far∈Icc (0:ℝ) L,
      (∀ t∈Icc (0:ℝ) L, c.viewingAngle a b lo≤c.viewingAngle a b t ∧
        c.viewingAngle a b t≤c.viewingAngle a b hi ∧ c.centeredRadius t≤c.centeredRadius far) ∧
      let w := c.viewingAngle a b hi-c.viewingAngle a b lo
      0<w ∧ w<Real.pi ∧
        (2*rate)^(-(1:ℝ)/4) < c.centeredRadius far*Real.sin (w/2) := by
  let x (s : ℝ) := a*c.x s+b*c.y s
  let y (s : ℝ) := -b*c.x s+a*c.y s
  let r := c.centeredRadius
  let θ := c.viewingAngle a b
  have cx : Continuous x := (c.hx.continuous.const_mul a).add (c.hy.continuous.const_mul b)
  have cy : Continuous y := (c.hx.continuous.const_mul (-b)).add (c.hy.continuous.const_mul a)
  have ct : Continuous θ := Real.continuous_arctan.comp (cy.div cx (fun s => (sep s).ne'))
  have cr : Continuous r := ((c.hx.continuous.pow 2).add (c.hy.continuous.pow 2)).sqrt
  have sq (s) : x s^2+y s^2=r s^2 := by
    rw [show r s^2=c.x s^2+c.y s^2 from Real.sq_sqrt (by positivity)]
    dsimp [x,y]
    linear_combination (c.x s^2+c.y s^2)*unit
  have rp (s) : 0<r s := by
    have n : 0≤r s := Real.sqrt_nonneg _
    have xp : 0<x s := sep s
    nlinarith only [sq s,n,sq_pos_of_pos xp,sq_nonneg (y s)]
  have xy (s) : r s*Real.cos (θ s)=x s ∧ r s*Real.sin (θ s)=y s :=
    polar_components (sep s) (rp s) (sq s)
  obtain ⟨lo,hlo,mn⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) ct.continuousOn
  obtain ⟨hi,hhi,mx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) ct.continuousOn
  obtain ⟨far,hf,cap⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hL.le) cr.continuousOn
  let mid := (θ hi+θ lo)/2
  let w := θ hi-θ lo
  have wn : 0≤w := sub_nonneg.mpr (mn hhi)
  have top : w<Real.pi := by
    have left : -(Real.pi/2)<θ lo := Real.neg_pi_div_two_lt_arctan _
    have right : θ hi<Real.pi/2 := Real.arctan_lt_pi_div_two _
    dsimp [w]; linarith
  let A := a*Real.cos mid-b*Real.sin mid
  let B := b*Real.cos mid+a*Real.sin mid
  have direction : A^2+B^2=1 := by
    dsimp [A,B]
    linear_combination (Real.cos mid^2+Real.sin mid^2)*unit + Real.cos_sq_add_sin_sq mid
  have cosine := Real.cos_pos_of_mem_Ioo
    (show w/2 ∈ Ioo (-(Real.pi/2)) (Real.pi/2) from ⟨by linarith [Real.pi_pos],by linarith⟩)
  have cone (s : ℝ) (hs : s∈Icc 0 L) : Real.cos (w/2)*r s≤A*c.x s+B*c.y s := by
    have dist : |θ s-mid|≤w/2 := by
      rw [abs_le]; dsimp [mid,w]
      have l : θ lo≤θ s := mn hs
      have u : θ s≤θ hi := mx hs
      exact ⟨by linarith only [l],by linarith only [u]⟩
    have tilt := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (θ s-mid))
      (show w/2≤Real.pi by linarith [Real.pi_pos]) dist
    rw [Real.cos_abs] at tilt
    calc
      _ ≤ r s * Real.cos (θ s-mid) := by
        rw [mul_comm (Real.cos _)]; exact mul_le_mul_of_nonneg_left tilt (rp s).le
      _ = _ := by
        rw [Real.cos_sub]
        calc
          _ = (r s*Real.cos (θ s))*Real.cos mid+(r s*Real.sin (θ s))*Real.sin mid := by ring
          _ = _ := by rw [(xy s).1,(xy s).2]; dsimp [x,y,A,B]; ring
  have inequality := c.radius_sector_bound ha hL direction cosine (Real.cos_le_one _) rp
    (fun _ ht => cap ht) cone
  have normalized : 1<2*rate*(r far*Real.sin (w/2))^4 := by
    rw [show 1-Real.cos (w/2)^2=Real.sin (w/2)^2 by linarith [Real.sin_sq_add_cos_sq (w/2)]] at inequality
    convert! inequality using 1
    ring
  have wp : 0<w := by
    by_contra! nonpos
    have zero := le_antisymm nonpos wn
    simp [zero] at normalized
    linarith
  have sil := Real.sin_nonneg_of_mem_Icc (show w/2∈Icc 0 Real.pi from
    ⟨by linarith,by linarith [Real.pi_pos]⟩)
  exact ⟨lo,hlo,hi,hhi,far,hf,fun t ht => ⟨mn ht,mx ht,cap ht⟩, wp,top,
    fourth_root_bound (mul_nonneg (rp far).le sil) (by positivity) normalized⟩

end MigrationGeometry.Adjoint.ClosedExpander
#print axioms MigrationGeometry.Adjoint.ClosedExpander.external_viewing_angle_bound
