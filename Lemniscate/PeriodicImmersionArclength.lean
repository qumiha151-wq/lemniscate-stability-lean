import Lemniscate.PeriodicArclength
import Lemniscate.ArclengthFrame
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.GroupWithZero.OrderIso
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Order.Compact

/-! The actual global arclength coordinate of a smooth periodic immersion. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped Topology ContDiff ComplexConjugate

private theorem immersion_periodic_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (P : ℝ) (hp : Function.Periodic f P) :
    Function.Periodic (deriv f) P := by
  intro u
  have heq : (fun x => f (x+P))=f := funext hp
  simpa only [deriv_comp_add_const] using congrArg (fun F => deriv F u) heq

private theorem periodic_positive_speed_lower_bound
    (v : ℝ → ℝ) (hv : Continuous v) (hpos : ∀ u, 0<v u)
    (P : ℝ) (hP : 0<P) (hp : Function.Periodic v P) :
    ∃ m>0, ∀ u, m≤v u := by
  letI : Fact (0<P) := ⟨hP⟩
  let V : C(AddCircle P,ℝ) := ⟨hp.lift,hv.quotient_lift _⟩
  have hVpos (x : AddCircle P) : 0<V x := by
    induction x using QuotientAddGroup.induction_on
    exact hpos _
  obtain ⟨m,hm,hbound⟩ := isCompact_univ.exists_forall_le'
    V.continuous.continuousOn (fun x _ => hVpos x)
  exact ⟨m,hm,fun u => hbound (u:AddCircle P) (mem_univ _)⟩

/-- A smooth periodic immersion has a genuine global arclength coordinate
and a smooth inverse. The resulting unit-speed curve has its actual signed
curvature and Frenet frame, with the same orientation. -/
theorem periodic_immersion_arclength
    (P : ℝ) (hP : 0<P) (γ : ℝ → ℂ)
    (hγ : ContDiff ℝ ∞ γ) (hper : Function.Periodic γ P)
    (hreg : ∀ u, deriv γ u≠0) :
    ∃ e : ℝ ≃o ℝ,
      (∀ u, e u=∫ x in (0:ℝ)..u, ‖deriv γ x‖) ∧
      ContDiff ℝ ∞ (e : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e.symm : ℝ → ℝ) ∧
      (∀ u, HasDerivAt e ‖deriv γ u‖ u) ∧
      (∀ s, HasDerivAt e.symm (‖deriv γ (e.symm s)‖)⁻¹ s) ∧
      let L := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
      let Γ := γ ∘ e.symm
      let t : ℝ → ℂ := fun s => deriv γ (e.symm s)/(‖deriv γ (e.symm s)‖:ℂ)
      let k : ℝ → ℝ := fun s => planarSignedCurvature γ (e.symm s)
      0<L ∧ (∀ u, e (u+P)=e u+L) ∧
      ContDiff ℝ ∞ Γ ∧ Function.Periodic Γ L ∧
      ContDiff ℝ ∞ t ∧ Function.Periodic t L ∧
      ContDiff ℝ ∞ k ∧ Function.Periodic k L ∧
      ∀ s, HasDerivAt Γ (t s) s ∧ ‖t s‖=1 ∧
        HasDerivAt t (I*(k s:ℂ)*t s) s ∧
        planarSignedCurvature Γ s=k s := by
  let v : ℝ → ℝ := fun u => ‖deriv γ u‖
  have hγ₁ : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hγ₂ : ContDiff ℝ ∞ (deriv (deriv γ)) := (contDiff_infty_iff_deriv.mp hγ₁).2
  have hv : ContDiff ℝ ∞ v := hγ₁.norm ℂ hreg
  have hvpos (u : ℝ) : 0<v u := norm_pos_iff.mpr (hreg u)
  have hvelper := immersion_periodic_deriv γ P hper
  have haccper := immersion_periodic_deriv (deriv γ) P hvelper
  have hvper : Function.Periodic v P := by
    intro u
    change ‖deriv γ (u+P)‖=‖deriv γ u‖
    rw [hvelper u]
  obtain ⟨m,hm,hmlower⟩ := periodic_positive_speed_lower_bound v hv.continuous hvpos P hP hvper
  let w : ℝ → ℝ := fun u => v u/m
  have hw : Continuous w := hv.continuous.div_const m
  have hwlower (u : ℝ) : 1≤w u := by
    apply (le_div_iff₀ hm).mpr
    simpa only [one_mul] using hmlower u
  have hwper : Function.Periodic w P := by
    intro u
    change v (u+P)/m=v u/m
    rw [hvper u]
  obtain ⟨e₁,he₁,_,_,_⟩ := periodic_integral_coordinate_exists w hw hwlower P hP hwper
  let e : ℝ ≃o ℝ := e₁.trans (OrderIso.mulLeft₀ m hm)
  have he (u : ℝ) : e u=∫ x in (0:ℝ)..u, v x := by
    change m*e₁ u=∫ x in (0:ℝ)..u, v x
    rw [he₁,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change m*(v x/m)=v x
    field_simp [ne_of_gt hm]
  have heD (u : ℝ) : HasDerivAt e (v u) u := by
    have hefun : (e : ℝ → ℝ)=(fun u => ∫ x in (0:ℝ)..u, v x) := funext he
    rw [hefun]
    exact intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable 0 u)
      hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuous.continuousAt
  have hederiv : deriv (e : ℝ → ℝ)=v := funext fun u => (heD u).deriv
  have hesmooth : ContDiff ℝ ∞ (e : ℝ → ℝ) := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun u => (heD u).differentiableAt,?_⟩
    rw [hederiv]
    exact hv
  have hinv (s : ℝ) : HasDerivAt e.symm (v (e.symm s))⁻¹ s := by
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
      (heD (e.symm s)) (ne_of_gt (hvpos (e.symm s)))
    exact Eventually.of_forall e.apply_symm_apply
  have hismooth : ContDiff ℝ ∞ (e.symm : ℝ → ℝ) := by
    exact e.toHomeomorph.contDiff_symm_deriv (fun u => ne_of_gt (hvpos u)) heD hesmooth
  have he0 : e 0=0 := by rw [he]; simp
  let L : ℝ := ∫ u in (0:ℝ)..P, v u
  have heP : e P=L := he P
  have hL : 0<L := by
    have hs := e.strictMono hP
    rw [he0,heP] at hs
    exact hs
  have hshift (u : ℝ) : e (u+P)=e u+L := by
    simpa only [he,zero_add,L] using
      hvper.intervalIntegral_add_eq_add 0 u (fun a b => hv.continuous.intervalIntegrable a b)
  have hishift (s : ℝ) : e.symm (s+L)=e.symm s+P := by
    apply e.injective
    rw [e.apply_symm_apply,hshift,e.apply_symm_apply]
  let Γ := γ ∘ e.symm
  let t : ℝ → ℂ := fun s => deriv γ (e.symm s)/(v (e.symm s):ℂ)
  let k : ℝ → ℝ := fun s => planarSignedCurvature γ (e.symm s)
  have hframe := arclength_frenet_frame γ (deriv γ) (deriv (deriv γ)) e.symm
    (fun u => (hγ.differentiable (by simp) u).hasDerivAt)
    (fun u => (hγ₁.differentiable (by simp) u).hasDerivAt)
    (fun s => by simpa only [one_div] using hinv s) (fun s => hreg (e.symm s))
  obtain ⟨hΓ,htunit,ht,_,hkΓ,_⟩ := hframe
  have hΓsmooth : ContDiff ℝ ∞ Γ := hγ.comp hismooth
  have hΓper : Function.Periodic Γ L := by
    intro s
    change γ (e.symm (s+L))=γ (e.symm s)
    rw [hishift,hper]
  have hdΓ : deriv Γ=t := funext fun s => (hΓ s).deriv
  have htsmooth : ContDiff ℝ ∞ t := by
    rw [← hdΓ]
    exact (contDiff_infty_iff_deriv.mp hΓsmooth).2
  have htper : Function.Periodic t L := by
    rw [← hdΓ]
    exact immersion_periodic_deriv Γ L hΓper
  have hkγsmooth : ContDiff ℝ ∞ (planarSignedCurvature γ) := by
    have hn : ContDiff ℝ ∞ (fun u => (conj (deriv γ u)*deriv (deriv γ) u).im) :=
      Complex.imCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp hγ₁).mul hγ₂)
    exact hn.div (hv.pow 3) (fun u => pow_ne_zero 3 (ne_of_gt (hvpos u)))
  have hkγper : Function.Periodic (planarSignedCurvature γ) P := by
    intro u
    change (conj (deriv γ (u+P))*deriv (deriv γ) (u+P)).im/‖deriv γ (u+P)‖^3 =
      (conj (deriv γ u)*deriv (deriv γ) u).im/‖deriv γ u‖^3
    rw [hvelper,haccper]
  have hksmooth : ContDiff ℝ ∞ k := hkγsmooth.comp hismooth
  have hkper : Function.Periodic k L := by
    intro s
    change planarSignedCurvature γ (e.symm (s+L))=planarSignedCurvature γ (e.symm s)
    rw [hishift,hkγper]
  refine ⟨e,he,hesmooth,hismooth,heD,hinv,?_⟩
  change 0<L ∧ (∀ u, e (u+P)=e u+L) ∧
    ContDiff ℝ ∞ Γ ∧ Function.Periodic Γ L ∧
    ContDiff ℝ ∞ t ∧ Function.Periodic t L ∧
    ContDiff ℝ ∞ k ∧ Function.Periodic k L ∧ _
  refine ⟨hL,hshift,hΓsmooth,hΓper,htsmooth,htper,hksmooth,hkper,?_⟩
  intro s
  refine ⟨hΓ s,htunit s,?_,hkΓ s⟩
  apply (ht s).congr_deriv
  dsimp only
  ring

end Lemniscate
