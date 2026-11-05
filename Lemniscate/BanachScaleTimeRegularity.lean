import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Smoothness of an existing solution on a Banach scale with derivative
loss. The equation is only assumed after an injective map to a fixed weak
space. No same-space ordinary differential equation theorem is used. -/
noncomputable section
namespace Lemniscate
open Set MeasureTheory
open scoped ContDiff Topology

private theorem lift_derivative_on_Ici
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a : ℝ) (L : E →L[ℝ] F) (hL : Function.Injective L)
    (u v : ℝ → E) (hu : ContinuousOn u (Ici a)) (hv : ContinuousOn v (Ici a))
    (hderiv : ∀ t ∈ Ici a,
      HasDerivWithinAt (fun s => L (u s)) (L (v t)) (Ici a) t) :
    ∀ t ∈ Ici a, HasDerivWithinAt u (v t) (Ici a) t := by
  let W (s : ℝ) : E := v (max a s)
  have hW : Continuous W :=
    hv.comp_continuous (continuous_const.max continuous_id) (fun s => le_max_left a s)
  have hWvalue (s : ℝ) (hs : s ∈ Ici a) : W s = v s := by
    dsimp only [W]
    rw [max_eq_right hs]
  let P (s : ℝ) : E := u a + ∫ x in a..s, W x
  have hidentity (t : ℝ) (ht : t ∈ Ici a) : u t = P t := by
    have hint : IntervalIntegrable (fun s => L (W s)) volume a t :=
      (L.continuous.comp hW).intervalIntegrable a t
    have hFTC : (∫ s in a..t, L (W s)) = L (u t)-L (u a) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
      · exact L.continuous.comp_continuousOn
          (hu.mono (fun s hs => hs.1))
      · intro s hs
        have hd := (hderiv s hs.1.le).hasDerivAt (Ici_mem_nhds hs.1)
        simpa only [hWvalue s hs.1.le] using hd
      · exact hint
    apply hL
    calc
      L (u t) = L (u a)+(∫ s in a..t, L (W s)) := by rw [hFTC]; abel
      _ = L (u a)+L (∫ s in a..t, W s) := by
        rw [L.intervalIntegral_comp_comm (hW.intervalIntegrable a t)]
      _ = L (P t) := by simp only [P,map_add]
  intro t ht
  have hP : HasDerivAt P (W t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hW.intervalIntegrable a t)
      hW.aestronglyMeasurable.stronglyMeasurableAtFilter hW.continuousAt).const_add (u a)
  have hPwithin : HasDerivWithinAt P (v t) (Ici a) t := by
    simpa only [hWvalue t ht] using hP.hasDerivWithinAt
  exact hPwithin.congr_of_mem hidentity ht

/-- A compatible equation losing any fixed number of scale levels upgrades
continuous curves in every level to smooth curves in every level, including
the one-sided initial endpoint. Only the weak-space time derivative is an
input; the higher-space time derivatives follow by Bochner integration. -/
theorem banach_scale_time_smooth
    (E : ℕ → Type*) [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace ℝ (E n)] [∀ n, CompleteSpace (E n)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a : ℝ) (loss : ℕ)
    (L : ∀ n, E n →L[ℝ] F) (hL : ∀ n, Function.Injective (L n))
    (u : ∀ n, ℝ → E n) (hu : ∀ n, ContinuousOn (u n) (Ici a))
    (O : ∀ n, Set (E (n+loss)))
    (R : ∀ n, E (n+loss) → E n)
    (hR : ∀ n, ContDiffOn ℝ ∞ (R n) (O n))
    (hO : ∀ n, MapsTo (u (n+loss)) (Ici a) (O n))
    (hbase : ∀ n t, t ∈ Ici a →
      HasDerivWithinAt (fun s => L n (u n s))
        (L n (R n (u (n+loss) t))) (Ici a) t) :
    (∀ n t, t ∈ Ici a →
      HasDerivWithinAt (u n) (R n (u (n+loss) t)) (Ici a) t) ∧
    ∀ n, ContDiffOn ℝ ∞ (u n) (Ici a) := by
  have hvelocity (n : ℕ) :
      ContinuousOn (fun t => R n (u (n+loss) t)) (Ici a) :=
    (hR n).continuousOn.comp (hu (n+loss)) (hO n)
  have hdu (n : ℕ) := lift_derivative_on_Ici a (L n) (hL n) (u n)
    (fun t => R n (u (n+loss) t)) (hu n) (hvelocity n) (hbase n)
  refine ⟨hdu,?_⟩
  have hfinite : ∀ k : ℕ, ∀ n, ContDiffOn ℝ (k : ℕ∞ω) (u n) (Ici a) := by
    intro k
    induction k with
    | zero =>
      intro n
      exact contDiffOn_zero.mpr (hu n)
    | succ k ih =>
      intro n
      have horder : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
        ENat.natCast_le_of_coe_top_le_withTop le_rfl k
      have hfield : ContDiffOn ℝ (k : ℕ∞ω)
          (fun t => R n (u (n+loss) t)) (Ici a) :=
        ((hR n).of_le horder).comp (ih (n+loss)) (hO n)
      have hderivative : ContDiffOn ℝ (k : ℕ∞ω)
          (derivWithin (u n) (Ici a)) (Ici a) :=
        hfield.congr (fun t ht => (hdu n t ht).derivWithin (uniqueDiffOn_Ici a t ht))
      rw [Nat.cast_add,Nat.cast_one]
      apply (contDiffOn_succ_iff_derivWithin (n := (k : ℕ∞ω)) (uniqueDiffOn_Ici a)).mpr
      refine ⟨fun t ht => (hdu n t ht).differentiableWithinAt,?_,hderivative⟩
      simp
  intro n
  exact contDiffOn_infty.mpr (fun k => hfinite k n)

end Lemniscate
