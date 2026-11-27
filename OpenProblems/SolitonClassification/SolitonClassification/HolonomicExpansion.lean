import SolitonClassification.HolonomicSpectrum
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

noncomputable section
open MeasureTheory Set Function Real
open scoped ContDiff
namespace ClosedSimilarity.Holonomic

/-- Fourier inversion of the finite sequence on the genuine period, at every real arclength. -/
theorem finite_expansion {P : ℝ} (hp : 0 < P) {f : ℝ→ℂ} (cf : Continuous f)
    (pf : Periodic f P) (fin : (support (fourierCoeffOn hp f)).Finite) :
    ∃ (S : Finset ℤ) (c : ℤ → ℂ), ∀ s : ℝ, f s =
      ∑ j ∈ S, c j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(s:ℂ)/(P:ℂ)) := by
  classical
  let : Fact (0<P) := ⟨hp⟩
  let g : C(AddCircle P, ℂ) :=
    ⟨AddCircle.liftIoc P 0 f, AddCircle.liftIoc_zero_continuous (by simpa using (pf 0).symm) cf.continuousOn⟩
  have val (x : ℝ) : g (x : AddCircle P) = f x := by
    let t := (AddCircle.equivIoc P 0) (x : AddCircle P)
    have back : ((t:ℝ) : AddCircle P) = (x : AddCircle P) := AddCircle.coe_equivIoc
    change f t = f x
    rw [← pf.lift_coe (t:ℝ), ←pf.lift_coe x, back]
  have coeff (j : ℤ) : fourierCoeff g j = fourierCoeffOn hp f j := by
    change fourierCoeff (AddCircle.liftIoc P 0 f) j = _
    rw [fourierCoeff_liftIoc_eq]
    simp
  have fs : (support (fourierCoeff g)).Finite := by
    rw [funext coeff]
    exact fin
  let S := fs.toFinset
  have zero (j : ℤ) (hj : j ∉ S) : fourierCoeff g j = 0 := by
    by_contra! h
    exact hj (fs.mem_toFinset.mpr h)
  refine ⟨S,fourierCoeff g,fun s => ?_⟩
  have total := has_pointwise_sum_fourier_series_of_summable (summable_of_hasFiniteSupport fs) (s : AddCircle P)
  have finite : HasSum (fun j : ℤ => fourierCoeff g j • fourier j (s : AddCircle P))
      (∑ j ∈ S, fourierCoeff g j • fourier j (s : AddCircle P)) :=
    hasSum_sum_of_ne_finset_zero (fun j hj => by rw [zero j hj,zero_smul])
  simpa only [val, smul_eq_mul, fourier_coe_apply] using (total.unique finite)

/-- The relation uses the actual iterated derivatives of the smooth real function. -/
theorem periodic_dfinite_expansion {P : ℝ} (hp : 0 < P) {f : ℝ→ℝ} (smooth : ContDiff ℝ ∞ f)
    (per : Periodic f P) (J : Finset ℕ) (p : ℕ → Polynomial ℂ)
    (nonzero : ∃ j ∈ J, p j ≠ 0)
    (ode : ∀ s : ℝ, ∑ j ∈ J, (p j).eval (s : ℂ)*((iteratedDeriv j f s : ℝ) : ℂ) = 0) :
    ∃ (S : Finset ℤ) (c : ℤ → ℂ), ∀ s : ℝ, (f s : ℂ) =
      ∑ j ∈ S, c j * Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*(s:ℂ)/(P:ℂ)) := by
  let u := fun (j : ℕ) (s : ℝ) => ((iteratedDeriv j f s : ℝ) : ℂ)
  have order (j : ℕ) : (j : WithTop ℕ∞) < (∞ : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
  have cu (j : ℕ) : Continuous (u j) :=
    Complex.continuous_ofReal.comp (smooth.continuous_iteratedDeriv j (order j).le)
  have pu (j : ℕ) : Periodic (u j) P := by
    intro s
    have shifts := iteratedDeriv_comp_add_const j f P
    rw [show (fun x:ℝ => f (x+P)) = f by funext x; exact per x] at shifts
    exact congrArg Complex.ofReal (congrFun shifts s).symm
  have jet (j : ℕ) (s : ℝ) : HasDerivAt (u j) (u (j+1) s) s := by
    have h := (smooth.differentiable_iteratedDeriv j (order j) s).hasDerivAt.ofReal_comp
    simpa only [u,iteratedDeriv_succ] using h
  have fin := fourier_support_finite hp J u p cu pu jet nonzero ode
  have e := finite_expansion hp (cu 0) (pu 0) fin
  simpa only [u,iteratedDeriv_zero] using e

end ClosedSimilarity.Holonomic
#print axioms ClosedSimilarity.Holonomic.periodic_dfinite_expansion

