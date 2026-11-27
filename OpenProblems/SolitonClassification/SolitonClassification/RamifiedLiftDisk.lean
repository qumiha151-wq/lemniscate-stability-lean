import SolitonClassification.RamifiedPowerDescent
import SolitonClassification.MeromorphicOrdinaryPole
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section
open Complex Set Filter Metric Function
open scoped Topology
namespace ClosedSimilarity.RamifiedCurvature
open MeromorphicCurvature

/-- A single holomorphic inverse sheet above a disk of half the distance
to the branch value. Its value at the center is the prescribed lift. -/
def inverseSheet (q : ℕ) (w s : ℂ) : ℂ := w*rootSection q (s/w^q)

theorem inverse_center {q : ℕ} {w : ℂ} (nw : w≠0) :
    inverseSheet q w (w^q)=w := by simp [inverseSheet,rootSection,pow_ne_zero _ nw]

theorem inverse_power {q : ℕ} (hq : 0<q) {w : ℂ} (nw : w≠0) (s : ℂ) :
    (inverseSheet q w s)^q=s := by
  dsimp only [inverseSheet]
  rw [mul_pow,root_pow hq,mul_div_cancel₀ _ (pow_ne_zero _ nw)]

theorem inverse_geometry {q : ℕ} (hq : 0<q) {w s : ℂ} (nw : w≠0)
    (hs : s∈ball (w^q) (‖w^q‖/2)) :
    AnalyticAt ℂ (inverseSheet q w) s ∧ inverseSheet q w s≠0 ∧ ‖inverseSheet q w s‖<2*‖w‖ := by
  have pn:=pow_ne_zero q nw
  have np:=norm_pos_iff.mpr pn
  have distance : ‖s-w^q‖<‖w^q‖/2 := by simpa only [mem_ball,dist_eq_norm] using hs
  have close : ‖s/w^q-1‖<1/2 := by
    rw [show s/w^q-1=(s-w^q)/w^q by field_simp,norm_div,div_lt_iff₀ np]
    linarith only [distance]
  have posRe : 0<(s/w^q).re := by
    have d:=Complex.abs_re_le_norm (s/w^q-1)
    rw [Complex.sub_re,Complex.one_re] at d
    have lo:=neg_abs_le ((s/w^q).re-1)
    linarith
  have cut : s/w^q∈Complex.slitPlane := Or.inl posRe
  have hol : AnalyticAt ℂ (fun z:ℂ=>z/w^q) s := analyticAt_id.div analyticAt_const pn
  refine ⟨analyticAt_const.mul (hol.cpow analyticAt_const cut),?_,?_⟩
  · intro eq
    have zero : s=0 := (inverse_power hq nw s).symm.trans (by simp [eq,zero_pow hq.ne'])
    simp [zero] at posRe
  · apply lt_of_pow_lt_pow_left₀ q (by positivity)
    rw [←norm_pow,inverse_power hq nw,mul_pow]
    have tri := norm_add_le (s-w^q) (w^q)
    rw [sub_add_cancel] at tri
    have leq : (2:ℝ)≤2^q := by
      simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show 1≤q from hq)
    rw [←norm_pow]
    have grow:=mul_le_mul_of_nonneg_right leq np.le
    linarith only [distance,tri,grow,np]

/-- Local ordinary arclength representatives glue into an ordinary solution
on this disk, with no global choice of a branch of the root. -/
theorem ordinary_on_lift_disk {q : ℕ} (hq : 0<q) {r : ℝ} {w : ℂ} (nw : w≠0)
    (small : 2*‖w‖≤r) (a b s₀ : ℂ) (f : ℂ→ℂ)
    (charts : ∀v : ℂ,v≠0 → ‖v‖<r → ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+v^q) ∧
      (f =ᶠ[𝓝 v] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+v^q)=0) :
    ∃K : ℂ→ℂ,K (s₀+w^q)=f w ∧ ∀t∈ball (s₀+w^q) (‖w^q‖/2),
      AnalyticAt ℂ K t ∧ ordinaryResidual a b K t=0 := by
  let B (s : ℂ) := inverseSheet q w (s-s₀)
  let K (s : ℂ) := f (B s)
  have proj (t : ℂ) : s₀+(B t)^q=t := by dsimp [B];rw [inverse_power hq nw];ring
  refine ⟨K,?_,?_⟩
  · dsimp [K,B];rw [add_sub_cancel_left,inverse_center nw]
  intro t ht
  have near : t-s₀∈ball (w^q) (‖w^q‖/2) := by
    rw [mem_ball,dist_eq_norm] at ht ⊢
    rwa [show t-s₀-w^q=t-(s₀+w^q) by ring]
  obtain ⟨analytic,nz,hz⟩:=inverse_geometry hq nw near
  obtain ⟨k,ak,agree,law⟩:=charts (B t) nz (hz.trans_le small)
  have ab : AnalyticAt ℂ B t := analytic.comp (f:=fun z:ℂ=>z-s₀) (analyticAt_id.sub analyticAt_const)
  have matchAt : K =ᶠ[𝓝 t] k := by
    filter_upwards [ab.continuousAt.tendsto.eventually agree] with u hu
    exact hu.trans (congrArg k (proj u))
  rw [proj] at ak law
  refine ⟨(analyticAt_congr matchAt).mpr ak,?_⟩
  simpa only [ordinaryResidual,ordinaryQuadratic,ordinaryQuartic,matchAt.eq_of_nhds,
    matchAt.deriv.eq_of_nhds,matchAt.deriv.deriv.eq_of_nhds,matchAt.deriv.deriv.deriv.eq_of_nhds,
    matchAt.deriv.deriv.deriv.deriv.eq_of_nhds] using law

end ClosedSimilarity.RamifiedCurvature

