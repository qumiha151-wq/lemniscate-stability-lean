import Lemniscate.NormalGraphPhaseIntegral
import Lemniscate.PeriodicWeakSecond
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The actual circle phase of a real-line normal height is C1 directly
from joint C1 regularity of that height. No derivative family in the
circle supremum norm, and no periodicity of that derivative, is assumed. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set Filter
open scoped ContDiff Topology ComplexConjugate

/-- A jointly C1 real-line height with its actual continuous circle
representatives has a C1 adjoint phase. Its angular derivative is the
negative pairing with the geometric rotation field whenever the true
pointwise height variation has that value. -/
theorem normal_graph_real_line_phase
    (L : ℝ) [Fact (0 < L)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (U : Set (P × ℝ)) (hU : IsOpen U)
    (H : (P × ℝ) × ℝ → ℝ)
    (hH : ContDiffOn ℝ 1 H (U ×ˢ (univ : Set ℝ)))
    (Q G : (P × ℝ) → C(AddCircle L,ℂ)) (ψ : CircleL2 L)
    (hQ : ∀ q ∈ U, ∀ s : ℝ, Q q (s:AddCircle L) = (H (q,s):ℂ))
    (hangle : ∀ q ∈ U, ∀ s : ℝ,
      HasDerivAt (fun θ => (H ((q.1,θ),s):ℂ)) (-G q (s:AddCircle L)) q.2) :
    ContDiffOn ℝ 1 (fun q => (inner ℂ ψ (circleContinuousL2 L (Q q))).re) U ∧
      ∀ p θ, (p,θ) ∈ U →
        HasDerivAt (fun a => (inner ℂ ψ (circleContinuousL2 L (Q (p,a)))).re)
          (-(inner ℂ ψ (circleContinuousL2 L (G (p,θ)))).re) θ := by
  let A := U ×ˢ (univ : Set ℝ)
  have hA : IsOpen A := hU.prod isOpen_univ
  let HC : (P × ℝ) × ℝ → ℂ := fun z => (H z:ℂ)
  have hcast : ContDiff ℝ 1 (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff
  have hHC : ContDiffOn ℝ 1 HC A := hcast.comp_contDiffOn hH
  have hcalc := (contDiffOn_succ_iff_fderivWithin
    (𝕜 := ℝ) (n := (0:ℕ∞ω)) hA.uniqueDiffOn).mp (by simpa only [zero_add] using hHC)
  let D : (P × ℝ) × ℝ → (P × ℝ) →L[ℝ] ℂ := fun z =>
    (fderivWithin ℝ HC A z).comp (ContinuousLinearMap.inl ℝ (P × ℝ) ℝ)
  have hD : ContinuousOn D A := hcalc.2.2.continuousOn.clm_comp continuousOn_const
  have hd (q : P × ℝ) (hq : q ∈ U) (s : ℝ) :
      HasFDerivAt (fun z : P × ℝ => HC (z,s)) (D (q,s)) q := by
    have hfull := (hcalc.1 (q,s) ⟨hq,mem_univ s⟩).hasFDerivWithinAt
    have hpartial := hfull.comp q (hasFDerivAt_prodMk_left q s).hasFDerivWithinAt
      (fun z hz => (show (z,s) ∈ A from ⟨hz,mem_univ s⟩))
    exact hpartial.hasFDerivAt (hU.mem_nhds hq)
  let X := Icc (0:ℝ) L
  haveI : CompactSpace X :=
    isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Icc (0:ℝ) L))
  let rep : AddCircle L → X := fun x =>
    ⟨(AddCircle.equivIoc L 0 x:ℝ),
      ⟨(AddCircle.equivIoc L 0 x).property.1.le,
        by simpa only [zero_add] using (AddCircle.equivIoc L 0 x).property.2⟩⟩
  have hrep : Measurable rep :=
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc L 0).measurable).subtype_mk
  have hrepcircle (x : AddCircle L) : ((rep x:ℝ):AddCircle L) = x :=
    AddCircle.coe_equivIoc
  let μ : Measure X := Measure.map rep AddCircle.haarAddCircle
  let w : X → ℂ := fun s => conj (ψ ((s:ℝ):AddCircle L))
  have hcircle : Continuous (fun s : X => ((s:ℝ):AddCircle L)) :=
    (AddCircle.continuous_mk' L).comp continuous_subtype_val
  have hwmeas : Measurable w :=
    Complex.continuous_conj.measurable.comp ((Lp.stronglyMeasurable ψ).measurable.comp hcircle.measurable)
  have hψint : Integrable (fun x : AddCircle L => conj (ψ x)) AddCircle.haarAddCircle := by
    have hi : Integrable (ψ : AddCircle L → ℂ) AddCircle.haarAddCircle :=
      memLp_one_iff_integrable.mp ((Lp.memLp ψ).mono_exponent (by norm_num))
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi
  have hw : Integrable w μ := by
    apply (integrable_map_measure hwmeas.aestronglyMeasurable hrep.aemeasurable).mpr
    simpa only [Function.comp_def,w,hrepcircle] using hψint
  let Hc : (P × ℝ) × X → ℂ := fun z => HC (z.1,(z.2:ℝ))
  let Gc : (P × ℝ) × X → ℂ := fun z => G z.1 ((z.2:ℝ):AddCircle L)
  let Dc : (P × ℝ) × X → (P × ℝ) →L[ℝ] ℂ := fun z => D (z.1,(z.2:ℝ))
  have hi : Continuous (fun z : (P × ℝ) × X => (z.1,(z.2:ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmaps : MapsTo (fun z : (P × ℝ) × X => (z.1,(z.2:ℝ)))
      (U ×ˢ (univ : Set X)) A := fun z hz => ⟨hz.1,mem_univ _⟩
  obtain ⟨hC,hderiv⟩ := normal_graph_phase_integral μ w hw U hU Hc Gc Dc
    (hHC.continuousOn.comp hi.continuousOn hmaps)
    (hD.comp hi.continuousOn hmaps)
    (fun q hq x => hd q hq x)
    (fun q hq x => hangle q hq x)
  have hpair (F : C(AddCircle L,ℂ)) :
      (∫ s : X, w s*F ((s:ℝ):AddCircle L) ∂μ) =
        inner ℂ ψ (circleContinuousL2 L F) := by
    have hm : AEStronglyMeasurable
        (fun s : X => w s*F ((s:ℝ):AddCircle L)) μ :=
      hwmeas.aestronglyMeasurable.mul (F.continuous.comp hcircle).aestronglyMeasurable
    rw [integral_map hrep.aemeasurable hm,circle_inner_continuous_integral]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp only [w,hrepcircle]
  have hphase (q : P × ℝ) (hq : q ∈ U) :
      (∫ s : X, w s*Hc (q,s) ∂μ).re =
        (inner ℂ ψ (circleContinuousL2 L (Q q))).re := by
    have heq : (fun s : X => w s*Hc (q,s)) =
        (fun s : X => w s*Q q ((s:ℝ):AddCircle L)) := by
      funext s
      rw [hQ q hq]
    rw [heq,hpair]
  refine ⟨hC.congr (fun q hq => (hphase q hq).symm),?_⟩
  intro p θ hq
  have hevent : (fun a => (inner ℂ ψ (circleContinuousL2 L (Q (p,a)))).re) =ᶠ[𝓝 θ]
      (fun a => (∫ s : X, w s*Hc ((p,a),s) ∂μ).re) := by
    have hmap : Tendsto (fun a : ℝ => (p,a)) (𝓝 θ) (𝓝 (p,θ)) :=
      (continuous_const.prodMk continuous_id).continuousAt
    filter_upwards [hmap.eventually (hU.mem_nhds hq)] with a ha
    exact (hphase (p,a) ha).symm
  have hh := (hderiv p θ hq).congr_of_eventuallyEq hevent
  simpa only [Gc,hpair] using hh

end Lemniscate
