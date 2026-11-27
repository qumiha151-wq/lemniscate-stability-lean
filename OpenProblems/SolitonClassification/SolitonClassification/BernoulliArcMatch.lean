import SolitonClassification.BernoulliArcModel
import SolitonClassification.BernoulliOscillator

noncomputable section
open Complex
namespace ClosedSimilarity.BernoulliGeometry
set_option backward.isDefEq.respectTransparency false

theorem canonical_dk (s : ℝ) :
    HasDerivAt (fun t=>curvature (angle t)) (slope (angle s)) s := by
  convert! (dcurvature (angle s)).comp s (angle_deriv s) using 1
  dsimp only [speed]
  field_simp [(root_pos _).ne']

theorem canonical_dv (s : ℝ) :
    HasDerivAt (fun t=>slope (angle t)) (-2/9*curvature (angle s)^3) s := by
  convert! (dslope (angle s)).comp s (angle_deriv s) using 1
  field_simp [(root_pos _).ne']

theorem canonical_dpos (s : ℝ) :
    HasDerivAt (fun t=>beta (angle t)) (tangent (angle s)) s := by
  convert! (dbeta (angle s)).scomp s (angle_deriv s) using 1
  simp only [Complex.real_smul,speed,Complex.ofReal_inv]
  field_simp [show (root (angle s):ℂ)≠0 by exact_mod_cast (root_pos _).ne']

theorem canonical_dtang (s : ℝ) : HasDerivAt (fun t=>tangent (angle t))
    (I*(curvature (angle s):ℂ)*tangent (angle s)) s := by
  convert! (dtangent (angle s)).scomp s (angle_deriv s) using 1
  simp only [Complex.real_smul,speed,Complex.ofReal_inv]
  field_simp [show (root (angle s):ℂ)≠0 by exact_mod_cast (root_pos _).ne']

@[simp] theorem beta_zero : beta 0=0 := by simp [beta,height]
@[simp] theorem curvature_zero : curvature 0=0 := by simp [curvature,height]
@[simp] theorem slope_zero : slope 0=3 := by norm_num [slope]

/-- Matching the positive inflection permits exactly one positive
spatial scale and gives equality of the actual curvature and its slope. -/
theorem oscillator_matches {k v : ℝ→ℝ} {s₀ : ℝ}
    (dk : ∀s,HasDerivAt k (v s) s) (dv : ∀s,HasDerivAt v (-2/9*k s^3) s)
    (k0 : k s₀=0) (v0 : 0<v s₀) : ∃d : ℝ,0<d ∧ d^2*v s₀=3 ∧
    ∀t,d*k (s₀+d*t)=curvature (angle t) ∧ d^2*v (s₀+d*t)=slope (angle t) := by
  let d := Real.sqrt (3/v s₀)
  have dp : 0<d := by dsimp [d];positivity
  have vv : d^2*v s₀=3 := by
    rw [show d^2=3/v s₀ from Real.sq_sqrt (by positivity)]
    field_simp [v0.ne']
  have clock (t : ℝ) : HasDerivAt (fun u=>s₀+d*u) d t := by
    simpa using (((hasDerivAt_id t).const_mul d).const_add s₀)
  have d1 (t : ℝ) : HasDerivAt (fun t=>d*k (s₀+d*t)) (d^2*v (s₀+d*t)) t := by
    convert! ((dk _).comp t (clock t)).const_mul d using 1
    ring
  have d2 (t : ℝ) : HasDerivAt (fun t=>d^2*v (s₀+d*t)) (-2/9*(d*k (s₀+d*t))^3) t := by
    convert! ((dv _).comp t (clock t)).const_mul (d^2) using 1
    ring
  refine ⟨d,dp,vv,oscillator_unique d1 d2 canonical_dk canonical_dv (s₀:=0) ?_ ?_⟩
  · simp [k0]
  · simpa using vv

theorem full_turn_count {v : ℝ→ℝ} {s₀ L d : ℝ} (hL : 0<L) (dp : 0<d)
    (per : Function.Periodic v L) (vv : d^2*v s₀=3)
    (matchv : ∀t,d^2*v (s₀+d*t)=slope (angle t)) :
    ∃m : ℕ, 0<m ∧ L=d*((m:ℝ)*arc (2*Real.pi)) := by
  let u := angle (L/d)
  have uu : arc u=L/d := arc_angle _
  have up : 0<u := arc_strictMono.lt_iff_lt.mp (by rw [arc_zero,uu];exact div_pos hL dp)
  have hit : s₀+d*(L/d)=s₀+L := by field_simp
  have sl := matchv (L/d)
  rw [hit,per,vv] at sl
  have cs : Real.cos u=1 := by
    change 3=6*Real.cos u/(1+Real.cos u^2) at sl
    have qq := (eq_div_iff (show (1:ℝ)+Real.cos u^2≠0 by positivity)).mp sl
    nlinarith [sq_nonneg (Real.cos u-1)]
  obtain ⟨j,je⟩ := (Real.cos_eq_one_iff u).mp cs
  have jp : (0:ℝ)<j := by
    by_contra! le
    have := mul_nonpos_of_nonpos_of_nonneg le (show 0≤2*Real.pi by positivity)
    linarith
  have jpos : 0<j := by exact_mod_cast jp
  refine ⟨j.toNat,by omega,?_⟩
  have cast : (j.toNat:ℝ)=(j:ℝ) := by exact_mod_cast Int.toNat_of_nonneg jpos.le
  rw [←arc_nat_period,cast,je,uu]
  field_simp

end ClosedSimilarity.BernoulliGeometry
