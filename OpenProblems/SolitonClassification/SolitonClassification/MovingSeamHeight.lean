import SolitonClassification.FrozenActualSection
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set FrozenStress

def radiusSquared (z : Phase) := z 2^2+z 3^2
def stressSquared (z : Phase) := (z 0^2/2)^2+z 1^2
def regular (z : Phase) := 0<radiusSquared z ∧ 0<stressSquared z
def scale (z : Phase) := (radiusSquared z)^(1/6:ℝ)
def amplitude (z : Phase) := Real.sqrt (stressSquared z)
def root (z : Phase) := Real.sqrt (amplitude z)
def shape (z : Phase) := z 0/root z
def slope (z : Phase) := z 1/amplitude z
def along (z : Phase) := (z 0^2/2*z 3+z 1*z 2)/(amplitude z*(scale z)^3)
def across (z : Phase) := (z 0^2/2*z 2-z 1*z 3)/(amplitude z*(scale z)^3)

/-- Corrected radial stress in the instantaneous position frame, starting
    from support data expressed in the constant radius units at the seam. -/
def height (z : Phase) := -(root z/scale z)^2*along z -
  chi (shape z) (slope z) (along z) (across z)/(root z/scale z)

def heightRate (u : Data) := (fderiv ℝ height u.2) (rhs u.1 u.2)

theorem regular_open : IsOpen {z | regular z} := by
  have hr : Continuous radiusSquared := by unfold radiusSquared; fun_prop
  have ha : Continuous stressSquared := by unfold stressSquared; fun_prop
  exact (isOpen_lt continuous_const hr).inter (isOpen_lt continuous_const ha)

theorem height_smooth {z : Phase} (h : regular z) : ContDiffAt ℝ 1 height z := by
  have scale_pos : 0<scale z := Real.rpow_pos_of_pos h.1 _
  have amp_pos : 0<amplitude z := Real.sqrt_pos.mpr h.2
  have root_pos : 0<root z := Real.sqrt_pos.mpr amp_pos
  have cs : ContDiffAt ℝ 1 scale z := by
    apply ContDiffAt.rpow_const_of_ne _ h.1.ne'
    unfold radiusSquared; fun_prop
  have ca : ContDiffAt ℝ 1 amplitude z := by
    apply ContDiffAt.sqrt _ h.2.ne'
    unfold stressSquared; fun_prop
  have cr : ContDiffAt ℝ 1 root z := ca.sqrt amp_pos.ne'
  have cu : ContDiffAt ℝ 1 shape z := by
    apply ContDiffAt.div _ cr root_pos.ne'; fun_prop
  have cw : ContDiffAt ℝ 1 slope z := by
    apply ContDiffAt.div _ ca amp_pos.ne'; fun_prop
  have denom := ca.mul (cs.pow 3)
  have nonzero : amplitude z*scale z^3 ≠ 0 := by positivity
  have cl : ContDiffAt ℝ 1 along z := by
    apply ContDiffAt.div _ denom nonzero; fun_prop
  have cb : ContDiffAt ℝ 1 across z := by
    apply ContDiffAt.div _ denom nonzero; fun_prop
  have rr := cr.div cs scale_pos.ne'
  have corr : ContDiffAt ℝ 1 (fun x => chi (shape x) (slope x) (along x) (across x)) z := by
    unfold chi; fun_prop
  exact ((rr.pow 2).neg.mul cl).sub (corr.div rr (div_ne_zero root_pos.ne' scale_pos.ne'))

theorem rate_continuousAt {u : Data} (h : regular u.2) : ContinuousAt heightRate u := by
  have f := (height_smooth h).continuousAt_fderiv (by norm_num)
  have r : Continuous (fun x : Data => rhs x.1 x.2) := continuous_snd.comp velocity_smooth.continuous
  exact (f.comp continuous_snd.continuousAt).clm_apply r.continuousAt

theorem rate_eq (d : ℝ) (x : Phase) (t : ℝ) (h : regular (solution d x t)) :
    HasDerivAt (fun s => height (solution d x s)) (heightRate (d,solution d x t)) t :=
  ((height_smooth h).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (solution_derivative d x t)

theorem frozen_height (c t : ℝ) : height (coords (seam c) t) = (seam c).outgoingHeight t := by
  let z := seam c
  have hs : scale (coords z t)=1 := by simp [scale,radiusSquared,coords,z.unit t]
  have hA : amplitude (coords z t) = z.amplitude t := rfl
  have hR : root (coords z t) = z.root t := rfl
  change height (coords z t)=z.outgoingHeight t
  simp only [height,Orbit.outgoingHeight,correctedOutgoing,shape,slope,along,across,hs,hA,hR,
    div_one,one_pow,mul_one,neg_mul]
  rfl

theorem frozen_regular (c t : ℝ) (ha : 0<(seam c).amplitude t) : regular (coords (seam c) t) := by
  refine ⟨?_,Real.sqrt_pos.mp ha⟩
  change 0<((seam c).p t)^2+((seam c).q t)^2
  rw [(seam c).unit t]; norm_num

theorem frozen_rate (c t : ℝ) (ha : 0<(seam c).amplitude t) :
    heightRate (0,coords (seam c) t)=deriv (seam c).outgoingHeight t := by
  have reg := frozen_regular c t ha
  rw [seam_solution] at reg ⊢
  have eq : (fun s => height (solution 0 ![c,0,1,0] s)) = (seam c).outgoingHeight := by
    funext s
    rw [←seam_solution,frozen_height]
  rw [←eq,(rate_eq 0 ![c,0,1,0] t reg).deriv]

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.frozen_rate
