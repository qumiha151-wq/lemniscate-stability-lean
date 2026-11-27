import SolitonClassification.Rotating.IntegerClosedImmersion
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
noncomputable section
open Set
set_option maxHeartbeats 1800000

/-- A curvature bound makes the midpoint tangent projection strictly increasing
on this arclength interval. -/
theorem short_arc_ne {b L : ℝ} (I : WindingOneImmersion b L) {s t : ℝ}
    (ord : s<t) (small : t-s≤3/10) (cap : ∀v∈Icc s t, |I.k v|≤10) :
    (I.x s,I.y s) ≠ (I.x t,I.y t) := by
  let m := (s+t)/2
  have hm : m∈Icc s t := ⟨by dsimp [m];linarith,by dsimp [m];linarith⟩
  let f := fun v => I.x v*Real.cos (I.theta m)+I.y v*Real.sin (I.theta m)
  have df (v : ℝ) : HasDerivAt f (Real.cos (I.theta v-I.theta m)) v := by
    rw [Real.cos_sub]
    exact ((I.tangentX v).mul_const _).add ((I.tangentY v).mul_const _)
  intro eq
  have feq : f s=f t := by
    change I.x s*_+I.y s*_=I.x t*_+I.y t*_
    rw [show I.x s=I.x t from congrArg Prod.fst eq,show I.y s=I.y t from congrArg Prod.snd eq]
  obtain ⟨v,hv,zero⟩ := exists_deriv_eq_zero ord
    ((continuous_iff_continuousAt.mpr (fun v => (df v).continuousAt)).continuousOn) feq
  rw [(df v).deriv] at zero
  have diff := (convex_Icc s t).norm_image_sub_le_of_norm_deriv_le
    (f:=I.theta) (fun w _ => (I.angleDerivative w).differentiableAt)
    (fun w hw => by rw [(I.angleDerivative w).deriv,Real.norm_eq_abs];exact cap w hw)
    hm (Ioo_subset_Icc_self hv)
  simp only [Real.norm_eq_abs] at diff
  have md : |v-m|≤(t-s)/2 := abs_le.mpr ⟨by dsimp [m];linarith [hv.1],by dsimp [m];linarith [hv.2]⟩
  have ang : |I.theta v-I.theta m|<Real.pi/2 := by linarith only [diff,md,small,Real.pi_gt_d2]
  exact (Real.cos_pos_of_mem_Ioo (abs_lt.mp ang)).ne' zero

/-- The shift by an arbitrary multiple of the physical period is included. -/
theorem short_modulo_period_ne {b L : ℝ} (I : WindingOneImmersion b L) (cap : ∀w,|I.k w|≤10)
    {s t : ℝ} (m : ℤ) (sep : 0 < |t+m•L-s|) (small : |t+m•L-s|≤3/10) :
    (I.x s,I.y s)≠(I.x t,I.y t) := by
  have px := (I.periodX.zsmul m) t
  have py := (I.periodY.zsmul m) t
  intro same
  have eq : (I.x s,I.y s)=(I.x (t+m•L),I.y (t+m•L)) := by rw [px,py];exact same
  rcases lt_or_gt_of_ne (sub_ne_zero.mp (abs_pos.mp sep)) with left | right
  · rw [abs_of_neg (sub_neg.mpr left)] at small
    exact (short_arc_ne I left (by linarith) (fun w _ => cap w)) eq.symm
  · rw [abs_of_nonneg (sub_nonneg.mpr right.le)] at small
    exact (short_arc_ne I right small (fun w _ => cap w)) eq

def chord (z p q : ℝ) := (1-z)*p+z*q

private theorem chord_upper {f g d : ℝ→ℝ} (df : ∀v,HasDerivAt f (g v) v)
    (dg : ∀v,HasDerivAt g (d v) v) {a b K z : ℝ} (ord : a≤b) (K0 : 0≤K)
    (lower : ∀v∈Icc a b,-K≤d v) (hz : z∈Icc 0 1) :
    f (chord z a b)-chord z (f a) (f b) ≤ K*(b-a)^2/8 := by
  let F := fun x => f x+K/2*(x*x)
  have dF (x : ℝ) : HasDerivAt F (g x+K*x) x := by
    have h := (df x).add (((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (K/2))
    convert! h using 1; dsimp only [F,id_eq,Pi.add_apply,Pi.mul_apply]; ring
  have dFe : deriv F = fun x => g x+K*x := funext fun x => (dF x).deriv
  have d2 (x : ℝ) : HasDerivAt (deriv F) (d x+K) x := by
    rw [dFe]
    simpa only [id_eq,mul_one,Pi.add_def] using (dg x).add ((hasDerivAt_id x).const_mul K)
  have cv : ConvexOn ℝ (Icc a b) F := convexOn_of_deriv2_nonneg' (convex_Icc a b)
    (fun x _ => (dF x).differentiableAt.differentiableWithinAt)
    (fun x _ => (d2 x).differentiableAt.differentiableWithinAt)
    (fun x hx => by change 0≤deriv (deriv F) x;rw [(d2 x).deriv]; linarith [lower x hx])
  have j := cv.2 (left_mem_Icc.mpr ord) (right_mem_Icc.mpr ord) (sub_nonneg.mpr hz.2) hz.1
    (show 1-z+z=1 by ring)
  simp only [smul_eq_mul] at j
  change f (chord z a b)+K/2*((chord z a b)*(chord z a b))≤chord z (F a) (F b) at j
  have raw : f (chord z a b)-chord z (f a) (f b) ≤ K/2*(b-a)^2*(z*(1-z)) := by
    dsimp only [chord,F] at j ⊢
    linarith only [j]
  have zz : z*(1-z)≤1/4 := by nlinarith [sq_nonneg (z-1/2)]
  exact raw.trans ((mul_le_mul_of_nonneg_left zz (show 0≤K/2*(b-a)^2 by positivity)).trans_eq (by ring))

theorem chord_error {f g d : ℝ→ℝ} (df : ∀v,HasDerivAt f (g v) v)
    (dg : ∀v,HasDerivAt g (d v) v) {a b K z : ℝ} (ord : a≤b) (K0 : 0≤K)
    (bound : ∀v∈Icc a b,|d v|≤K) (hz : z∈Icc 0 1) :
    |f (chord z a b)-chord z (f a) (f b)| ≤ K*(b-a)^2/8 := by
  have up := chord_upper df dg ord K0 (fun v hv=>(abs_le.mp (bound v hv)).1) hz
  have dn := chord_upper (f:=fun v=> -(f v)) (g:=fun v=> -(g v)) (d:=fun v=> -(d v))
    (fun v=>(df v).neg) (fun v=>(dg v).neg) ord K0
    (fun v hv => by linarith [(abs_le.mp (bound v hv)).2]) hz
  apply abs_le.mpr
  refine ⟨?_,up⟩
  change -(f (chord z a b))-chord z (-(f a)) (-(f b))≤_ at dn
  have eq : chord z (-(f a)) (-(f b))= -(chord z (f a) (f b)) := by unfold chord;ring
  rw [eq] at dn;linarith

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCrossings
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCrossings.short_modulo_period_ne
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCrossings.chord_error
