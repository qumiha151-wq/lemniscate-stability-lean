import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Lean.Util.CollectAxioms

/-! Independent real-analysis bridge for the rotating shooting certificate.
The actual map and its actual Fréchet derivative enter the hypotheses. A zero
is a conclusion. No certificate data or numerical enclosure is assumed to
prove its own validity. Only Mathlib is imported. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Banach's theorem applied to the *derived* Newton-like map x-B(F x).
The mean-value theorem derives contraction from an actual derivative bound,
and the center residual derives invariance of the closed ball. -/
theorem exists_unique_zero_of_preconditioned_bounds
    (F : E → E) (DF : E → E →L[ℝ] E) (B : E →L[ℝ] E)
    (p : E) (r η : ℝ) (q : ℝ≥0)
    (hr : 0≤r) (hq : q<1) (hB : Function.Injective B)
    (hF : ∀x∈closedBall p r, HasFDerivAt F (DF x) x)
    (hD : ∀x∈closedBall p r,
      ‖ContinuousLinearMap.id ℝ E-B.comp (DF x)‖≤(q:ℝ))
    (hres : ‖B (F p)‖≤η) (hself : η+(q:ℝ)*r≤r) :
    ∃x∈closedBall p r, F x=0 ∧ ∀y∈closedBall p r, F y=0 → y=x := by
  let T : E → E := fun x => x-B (F x)
  have hp : p∈closedBall p r := mem_closedBall_self hr
  have hT : ∀x∈closedBall p r,
      HasFDerivAt T (ContinuousLinearMap.id ℝ E-B.comp (DF x)) x := by
    intro x hx
    exact (hasFDerivAt_id x).sub (B.hasFDerivAt.comp x (hF x hx))
  have hLip : ∀x∈closedBall p r, ∀y∈closedBall p r,
      ‖T x-T y‖≤(q:ℝ)*‖x-y‖ := by
    intro x hx y hy
    exact (convex_closedBall p r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hT z hz).hasFDerivWithinAt) hD hy hx
  have hcenter : ‖T p-p‖≤η := by
    simpa only [T,sub_sub_cancel_left,norm_neg] using hres
  have hmap : MapsTo T (closedBall p r) (closedBall p r) := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖T x-p‖≤‖T x-T p‖+‖T p-p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _≤(q:ℝ)*‖x-p‖+η := add_le_add (hLip x hx p hp) hcenter
      _≤(q:ℝ)*r+η := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hx) q.coe_nonneg) le_rfl
      _≤r := by linarith
  have hcontract : ContractingWith q (hmap.restrict T _ _) := by
    refine ⟨hq,LipschitzWith.of_dist_le_mul ?_⟩
    intro x y
    change dist (T x) (T y)≤(q:ℝ)*dist (x:E) (y:E)
    simpa only [dist_eq_norm] using hLip x x.property y y.property
  obtain ⟨x,hx,hfix,_⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmap hcontract hp (edist_ne_top p (T p))
  have hroot : F x=0 := by
    apply hB
    rw [map_zero]
    have h : x-B (F x)=x := hfix
    exact sub_eq_self.mp h
  refine ⟨x,hx,hroot,?_⟩
  intro y hy hyroot
  have hdist := hLip y hy x hx
  simp only [T,hyroot,hroot,map_zero,sub_zero] at hdist
  have hq' : (q:ℝ)<1 := hq
  have hz : ‖y-x‖=0 := by nlinarith [norm_nonneg (y-x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

omit [CompleteSpace E] in
/-- In finite dimension, the matrix-defect certificate also proves B
injective. Thus nonsingularity is derived instead of independently assumed. -/
theorem preconditioner_injective_of_defect [FiniteDimensional ℝ E]
    (B J : E →L[ℝ] E)
    (hdef : ‖ContinuousLinearMap.id ℝ E-B.comp J‖<1) : Function.Injective B := by
  have hcomp : Function.Injective (B.comp J) := by
    intro x y hxy
    have hz : (B.comp J) (x-y)=0 := by rw [map_sub,hxy,sub_self]
    have he : (ContinuousLinearMap.id ℝ E-B.comp J) (x-y)=x-y := by
      simp only [sub_apply,ContinuousLinearMap.id_apply,hz,sub_zero]
    have hn := (ContinuousLinearMap.id ℝ E-B.comp J).le_opNorm (x-y)
    rw [he] at hn
    have hnorm : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hsurj : Function.Surjective (B.comp J) :=
    (LinearMap.injective_iff_surjective (f:=(B.comp J).toLinearMap)).mp hcomp
  have hBsurj : Function.Surjective B := by
    intro y
    obtain ⟨x,hx⟩ := hsurj y
    exact ⟨J x,hx⟩
  exact (LinearMap.injective_iff_surjective (f:=B.toLinearMap)).mpr hBsurj

omit [CompleteSpace E] in
theorem preconditioned_derivative_from_center (D : E → E →L[ℝ] E)
    (B J : E →L[ℝ] E) {p x : E} {β ε H r q₀ : ℝ}
    (hβ : 0≤β) (hH : 0≤H) (hB : ‖B‖≤β)
    (hJ : ‖J-D p‖≤ε) (hD : ‖D x-D p‖≤H*dist x p) (hx : dist x p≤r)
    (hcenter : ‖ContinuousLinearMap.id ℝ E-B.comp J‖≤q₀) :
    ‖ContinuousLinearMap.id ℝ E-B.comp (D x)‖≤q₀+β*(ε+H*r) := by
  have he : ContinuousLinearMap.id ℝ E-B.comp (D x)=
      (ContinuousLinearMap.id ℝ E-B.comp J)+B.comp (J-D x) := by
    ext v
    simp only [sub_apply,add_apply,ContinuousLinearMap.comp_apply,map_sub]
    abel
  have htri := norm_sub_le_norm_sub_add_norm_sub J (D p) (D x)
  rw [norm_sub_rev (D p) (D x)] at htri
  have hJx : ‖J-D x‖≤ε+H*r := by
    have hh := mul_le_mul_of_nonneg_left hx hH
    linarith
  have hcomp := B.opNorm_comp_le (J-D x)
  have hprod := mul_le_mul hB hJx (norm_nonneg _) hβ
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hcenter (hcomp.trans hprod))

omit [CompleteSpace E] in
/-- A bound on the actual derivative of the derivative map yields the
variation hypothesis. This is the analytic use of a genuine Hessian bound. -/
theorem derivative_variation_of_second_derivative
    (D : E → E →L[ℝ] E) (DD : E → E →L[ℝ] (E →L[ℝ] E))
    {p : E} {r H : ℝ} (hr : 0≤r)
    (hDD : ∀x∈closedBall p r, HasFDerivAt D (DD x) x)
    (hbound : ∀x∈closedBall p r, ‖DD x‖≤H) :
    ∀x∈closedBall p r, ‖D x-D p‖≤H*dist x p := by
  intro x hx
  simpa only [dist_eq_norm] using
    (convex_closedBall p r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hDD z hz).hasFDerivWithinAt) hbound (mem_closedBall_self hr) hx

/-- Converts approximate center residual/Jacobian and actual derivative
variation bounds into a unique true zero. All approximation errors are
explicit; J need not be the actual derivative and y need not be F(p). -/
theorem exists_unique_zero_of_center_certificate [FiniteDimensional ℝ E]
    (F : E → E) (D : E → E →L[ℝ] E) (B J : E →L[ℝ] E) (p y : E)
    {r η ε β H q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hH : 0≤H) (hq : q<1) (hq₀ : q₀<1)
    (hF : ∀x∈closedBall p r, HasFDerivAt F (D x) x)
    (hvariation : ∀x∈closedBall p r, ‖D x-D p‖≤H*dist x p)
    (hzero : ‖y-F p‖≤η) (hJ : ‖J-D p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ E-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ) (hcontraction : q₀+β*(ε+H*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃x∈closedBall p r, F x=0 ∧ ∀x'∈closedBall p r, F x'=0 → x'=x := by
  have hD : ∀x∈closedBall p r,
      ‖ContinuousLinearMap.id ℝ E-B.comp (D x)‖≤(q:ℝ) := by
    intro x hx
    exact (preconditioned_derivative_from_center D B J hβ hH hB hJ
      (hvariation x hx) hx hmatrix).trans hcontraction
  have hres : ‖B (F p)‖≤ζ+β*η := by
    have he : B (F p)=B y+B (F p-y) := by rw [map_sub]; abel
    have herror : ‖F p-y‖≤η := by simpa only [norm_sub_rev] using hzero
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hresidual
      ((B.le_opNorm _).trans (mul_le_mul hB herror (norm_nonneg _) hβ)))
  exact exists_unique_zero_of_preconditioned_bounds F D B p r (ζ+β*η) q hr hq
    (preconditioner_injective_of_defect B J (hmatrix.trans_lt hq₀)) hF hD hres hself

/-- A strict-derivative interface for local C1 shooting-flow constructions. -/
theorem exists_unique_zero_of_strict_certificate [FiniteDimensional ℝ E]
    (F : E → E) (D : E → E →L[ℝ] E) (B J : E →L[ℝ] E) (p y : E)
    {r η ε β H q₀ ζ : ℝ} (q : ℝ≥0)
    (hr : 0≤r) (hβ : 0≤β) (hH : 0≤H) (hq : q<1) (hq₀ : q₀<1)
    (hF : ∀x∈closedBall p r, HasStrictFDerivAt F (D x) x)
    (hvariation : ∀x∈closedBall p r, ‖D x-D p‖≤H*dist x p)
    (hzero : ‖y-F p‖≤η) (hJ : ‖J-D p‖≤ε) (hB : ‖B‖≤β)
    (hmatrix : ‖ContinuousLinearMap.id ℝ E-B.comp J‖≤q₀)
    (hresidual : ‖B y‖≤ζ) (hcontraction : q₀+β*(ε+H*r)≤(q:ℝ))
    (hself : (ζ+β*η)+(q:ℝ)*r≤r) :
    ∃x∈closedBall p r, F x=0 ∧ ∀x'∈closedBall p r, F x'=0 → x'=x :=
  exists_unique_zero_of_center_certificate F D B J p y q hr hβ hH hq hq₀
    (fun x hx => (hF x hx).hasFDerivAt) hvariation hzero hJ hB hmatrix
    hresidual hcontraction hself

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating Banach root audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating Banach root audit passed for {count} declarations."
