import SolitonClassification.SupportFlowContinuity
import SolitonClassification.RadialLayer

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Filter
open scoped Topology

/-- Scaling from coordinates normalized by the radius at the seam to the
    physical support coordinates with dilation coefficient one. -/
def restore (l : ℝ) (x : Phase) : Phase := ![l*x 0,l^2*x 1,l^3*x 2,l^3*x 3]

/-- The small constant driving rate is exactly the reciprocal fourth power of
    the scale. This conjugacy holds for positive and negative arclength. -/
theorem physical_support_conjugacy {l d : ℝ} (scale_eq : l^4*d=1) (x : Phase) (s : ℝ) :
    solution 1 (restore l x) s = restore l (solution d x (l*s)) := by
  let z := solution d x
  let f := fun t : ℝ => restore l (z (l*t))
  have sol : f 0 = restore l x ∧ ∀ t, HasDerivAt f (rhs 1 (f t)) t := by
    refine ⟨by simp [f,z,solution_zero],?_⟩
    intro t
    have time : HasDerivAt (fun u : ℝ => l*u) l t := by
      simpa using (hasDerivAt_id t).const_mul l
    have h := hasDerivAt_pi.mp (solution_derivative d x (l*t))
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! ((h 0).scomp t time).const_mul l using 1
      simp [f,z,restore,rhs]; ring
    · convert! ((h 1).scomp t time).const_mul (l^2) using 1
      simp [f,z,restore,rhs]; ring
    · convert! ((h 2).scomp t time).const_mul (l^3) using 1
      simp [f,z,restore,rhs]; ring
    · convert! ((h 3).scomp t time).const_mul (l^3) using 1
      simp [f,z,restore,rhs]; nlinarith only [scale_eq]
  have same := (exists_unique_solution 1 (restore l x)).unique
    (show solution 1 (restore l x) 0 = _ ∧ _ from
      ⟨solution_zero _ _,solution_derivative _ _⟩) sol
  exact congrFun same s

def radiusSq (x : Phase) := (x 2)^2 + (x 3)^2

theorem radiusSq_rate (d : ℝ) (x : Phase) (t : ℝ) :
    HasDerivAt (fun u => radiusSq (solution d x u)) (2*d*(solution d x t 3)) t := by
  have h := hasDerivAt_pi.mp (solution_derivative d x t)
  convert! ((h 2).pow 2).add ((h 3).pow 2) using 1
  simp [rhs]; ring

/-- The radius parameter seen by a physical incoming shot at this point,
    expressed entirely in the global polynomial flow coordinates. -/
theorem incoming_radius_parameter {l d : ℝ} (hl : 0 < l) (scale_eq : l^4*d=1)
    (x : Phase) (s : ℝ) (hoff : 0 < radiusSq (solution d x (l*s))) :
    ReflectedArc.RadialLayer.eps (solution 1 (restore l x)) s =
      d * (radiusSq (solution d x (l*s))) ^ (-2/3 : ℝ) := by
  let A := radiusSq (solution d x (l*s))
  have hA : 0 < A := hoff
  have prod : radiusSq (solution 1 (restore l x) s) = l^6*A := by
    rw [physical_support_conjugacy scale_eq]
    simp [A,radiusSq,restore]; ring
  have power (a : ℝ) (ha : 0 ≤ a) : 1/(a^(1/6:ℝ))^4 = a^(-2/3:ℝ) := by
    rw [← Real.rpow_natCast _ 4,← Real.rpow_mul ha,one_div,← Real.rpow_neg ha]
    norm_num
  unfold ReflectedArc.RadialLayer.eps ReflectedArc.RadialLayer.scale
  change 1/((radiusSq (solution 1 (restore l x) s))^(1/6:ℝ))^4 = d*A^(-2/3:ℝ)
  rw [prod,power _ (by positivity),Real.mul_rpow (by positivity) hA.le,
    ← Real.rpow_natCast l 6,← Real.rpow_mul hl.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_neg hl.le (4:ℝ)]
  norm_num only [Real.rpow_ofNat]
  have inv : (l^4)⁻¹ = d := by
    apply (mul_left_cancel₀ (pow_ne_zero 4 hl.ne'))
    rw [mul_inv_cancel₀ (pow_ne_zero 4 hl.ne'),scale_eq]
  rw [inv]

/-- The true radius in seam units moves at speed at most |d|, even along
    trajectories that pass through the origin. The estimate is uniform in the
    curvature data and does not use a stress or energy bound. -/
theorem radius_speed (d : ℝ) (x : Phase) (s t : ℝ) :
    |Real.sqrt (radiusSq (solution d x t)) - Real.sqrt (radiusSq (solution d x s))|
      ≤ |d| * |t-s| := by
  let A := fun u => radiusSq (solution d x u)
  have hA (u : ℝ) : 0 ≤ A u := by unfold A radiusSq; positivity
  have bound (e : ℝ) (he : 0 < e) :
      |Real.sqrt (e+A t)-Real.sqrt (e+A s)| ≤ |d| * |t-s| := by
    let f := fun u => Real.sqrt (e+A u)
    have hd (u : ℝ) : HasDerivAt f
        ((0+2*d*solution d x u 3)/(2*Real.sqrt (e+A u))) u := by
      apply ((hasDerivAt_const u e).add (radiusSq_rate d x u)).sqrt
      exact (add_pos_of_pos_of_nonneg he (hA u)).ne'
    have b (u : ℝ) : ‖deriv f u‖ ≤ |d| := by
      have hr := Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg he (hA u))
      have hq : |solution d x u 3| ≤ Real.sqrt (e+A u) := by
        rw [← Real.sqrt_sq_eq_abs]
        apply Real.sqrt_le_sqrt
        unfold A radiusSq
        linarith [sq_nonneg (solution d x u 2)]
      rw [(hd u).deriv,Real.norm_eq_abs,zero_add,abs_div,abs_mul,abs_mul,
        abs_of_pos (mul_pos (by norm_num) hr),abs_of_pos (by norm_num : (0:ℝ)<2)]
      apply (div_le_iff₀ (mul_pos (by norm_num) hr)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hq (abs_nonneg d)]
    have v := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u (_ : u ∈ (univ : Set ℝ)) => (hd u).differentiableAt) (fun u _ => b u)
      convex_univ (mem_univ s) (mem_univ t)
    exact v
  have cont : Continuous (fun e : ℝ => |Real.sqrt (e+A t)-Real.sqrt (e+A s)|) := by fun_prop
  have lim := (cont.continuousAt (x := (0:ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have h := le_of_tendsto lim (Filter.mem_of_superset self_mem_nhdsWithin
    (fun e (he : e ∈ Ioi (0:ℝ)) => bound e he))
  simpa [A] using h

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.physical_support_conjugacy
#print axioms ClosedSimilarity.GlobalSupport.incoming_radius_parameter
#print axioms ClosedSimilarity.GlobalSupport.radius_speed
