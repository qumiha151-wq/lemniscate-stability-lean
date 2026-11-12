import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Util.CollectAxioms

/-!
# Local exclusion of odd zeros

A strict derivative bounded below only in the odd directions suffices.  The
full derivative need not be injective.  The proof compares `(e,o)` with
`(e,-o)` using the uniform two-point remainder of strict differentiability.

This module is independent of the numerical shooting data.  It makes no
claim that a particular computed orbit satisfies a rank hypothesis.
-/

open Filter Topology

namespace ClosedSimilarity.OddLocalRigidity

variable {E O Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup O] [NormedSpace ℝ O]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ E] in
/-- The norm of the difference of a point and its odd reflection. -/
theorem norm_sub_odd_reflection (x : E × O) :
    ‖x - (x.1, -x.2)‖ = 2 * ‖x.2‖ := by
  have hd : x - (x.1, -x.2) = (0, x.2 - -x.2) := by
    ext <;> simp
  rw [hd, Prod.norm_def]
  simp only [norm_zero, max_eq_right (norm_nonneg _)]
  calc
    ‖x.2 - -x.2‖ = ‖(2 : ℝ) • x.2‖ := by rw [two_smul, sub_neg_eq_add]
    _ = 2 * ‖x.2‖ := by rw [norm_smul]; norm_num

/-- Strict differentiability and a lower bound on the odd restriction of
the derivative yield a local quantitative separation of reflected points. -/
theorem eventually_odd_separation
    {F : E × O → Y} {A : (E × O) →L[ℝ] Y} {e₀ : E} {c : ℝ}
    (hF : HasStrictFDerivAt F A (e₀, 0)) (hc : 0 < c)
    (hA : ∀ v : O, c * ‖v‖ ≤ ‖A (0, v)‖) :
    ∀ᶠ x in 𝓝 (e₀, (0 : O)), c * ‖x.2‖ ≤ ‖F x - F (x.1, -x.2)‖ := by
  have ht : Tendsto (fun x : E × O => (x, (x.1, -x.2)))
      (𝓝 (e₀, 0)) (𝓝 ((e₀, 0), (e₀, (0 : O)))) := by
    have hcont : Continuous (fun x : E × O => (x, (x.1, -x.2))) := by fun_prop
    simpa only [ContinuousAt, neg_zero] using hcont.continuousAt (x := (e₀, (0 : O)))
  have hsmall := ht.eventually (hF.isLittleO.def (show 0 < c / 2 by linarith))
  filter_upwards [hsmall] with x hx
  change ‖F x - F (x.1, -x.2) - A (x - (x.1, -x.2))‖ ≤
    c / 2 * ‖x - (x.1, -x.2)‖ at hx
  have hd : x - (x.1, -x.2) = (0, x.2 - -x.2) := by
    ext <;> simp
  have hlower : c * ‖x - (x.1, -x.2)‖ ≤ ‖A (x - (x.1, -x.2))‖ := by
    rw [hd, Prod.norm_def]
    simpa using hA (x.2 - -x.2)
  have htriangle : ‖A (x - (x.1, -x.2))‖ ≤
      ‖F x - F (x.1, -x.2)‖ +
        ‖F x - F (x.1, -x.2) - A (x - (x.1, -x.2))‖ := by
    calc
      ‖A (x - (x.1, -x.2))‖ =
          ‖(F x - F (x.1, -x.2)) -
            (F x - F (x.1, -x.2) - A (x - (x.1, -x.2)))‖ := by
              congr 1
              abel
      _ ≤ _ := norm_sub_le _ _
  rw [norm_sub_odd_reflection] at hx hlower
  nlinarith

/-- A locally reflection-invariant zero set has no nearby odd zeros when
the strict derivative is bounded below on odd directions. -/
theorem eventually_odd_eq_zero
    {F : E × O → Y} {A : (E × O) →L[ℝ] Y} {e₀ : E} {c : ℝ}
    (hF : HasStrictFDerivAt F A (e₀, 0)) (hc : 0 < c)
    (hA : ∀ v : O, c * ‖v‖ ≤ ‖A (0, v)‖)
    (hsym : ∀ᶠ x in 𝓝 (e₀, (0 : O)), F x = 0 → F (x.1, -x.2) = 0) :
    ∀ᶠ x in 𝓝 (e₀, (0 : O)), F x = 0 → x.2 = 0 := by
  filter_upwards [eventually_odd_separation hF hc hA, hsym] with x hx hs
  intro hzero
  have hnonpos : c * ‖x.2‖ ≤ 0 := by simpa [hzero, hs hzero] using hx
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg x.2]

/-- Ball form of local odd rigidity, suitable for a shooting-map interface. -/
theorem exists_ball_odd_eq_zero
    {F : E × O → Y} {A : (E × O) →L[ℝ] Y} {e₀ : E} {c : ℝ}
    (hF : HasStrictFDerivAt F A (e₀, 0)) (hc : 0 < c)
    (hA : ∀ v : O, c * ‖v‖ ≤ ‖A (0, v)‖)
    (hsym : ∀ᶠ x in 𝓝 (e₀, (0 : O)), F x = 0 → F (x.1, -x.2) = 0) :
    ∃ r > 0, ∀ (e : E) (o : O),
      dist (e, o) (e₀, 0) < r → F (e, o) = 0 → o = 0 := by
  rcases Metric.eventually_nhds_iff.mp (eventually_odd_eq_zero hF hc hA hsym) with
    ⟨r, hr, hball⟩
  exact ⟨r, hr, fun e o hdist hz => hball hdist hz⟩

/-- In a finite-dimensional odd space, injectivity of the odd restriction
supplies the quantitative lower bound used above. No assumption is made on
the even restriction or on injectivity of the full derivative. -/
theorem exists_odd_lower_bound [FiniteDimensional ℝ O]
    {A : (E × O) →L[ℝ] Y}
    (hinj : Function.Injective (fun v : O => A (0, v))) :
    ∃ c > 0, ∀ v : O, c * ‖v‖ ≤ ‖A (0, v)‖ := by
  let B : O →ₗ[ℝ] Y := A.toLinearMap.comp (LinearMap.inr ℝ E O)
  have hB : Function.Injective B := hinj
  obtain ⟨K, hK, hanti⟩ := B.injective_iff_antilipschitz.mp hB
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKr, fun v => ?_⟩
  have hz : A (0, (0 : O)) = 0 := A.map_zero
  have hn : ‖v‖ ≤ (K : ℝ) * ‖A (0, v)‖ := by
    simpa [B, dist_eq_norm, hz] using hanti.le_mul_dist v 0
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ hKr).mpr (by simpa [mul_comm] using hn)

/-- Finite-dimensional rank form of the local exclusion theorem. It applies
even when the full derivative has a kernel in the even directions. -/
theorem exists_ball_odd_eq_zero_of_injective [FiniteDimensional ℝ O]
    {F : E × O → Y} {A : (E × O) →L[ℝ] Y} {e₀ : E}
    (hF : HasStrictFDerivAt F A (e₀, 0))
    (hinj : Function.Injective (fun v : O => A (0, v)))
    (hsym : ∀ᶠ x in 𝓝 (e₀, (0 : O)), F x = 0 → F (x.1, -x.2) = 0) :
    ∃ r > 0, ∀ (e : E) (o : O),
      dist (e, o) (e₀, 0) < r → F (e, o) = 0 → o = 0 := by
  obtain ⟨c, hc, hA⟩ := exists_odd_lower_bound hinj
  exact exists_ball_odd_eq_zero hF hc hA hsym

/-- A sequence of genuinely odd zeros accumulating at an even point forces
loss of injectivity in the odd derivative. Even-direction rank loss alone
does not meet this necessary condition. -/
theorem not_injective_of_accumulating_odd_zeros [FiniteDimensional ℝ O]
    {F : E × O → Y} {A : (E × O) →L[ℝ] Y} {e₀ : E}
    (hF : HasStrictFDerivAt F A (e₀, 0))
    (hsym : ∀ᶠ x in 𝓝 (e₀, (0 : O)), F x = 0 → F (x.1, -x.2) = 0)
    {u : ℕ → E × O} (hu : Tendsto u atTop (𝓝 (e₀, (0 : O))))
    (hzero : ∀ n, F (u n) = 0) (hodd : ∀ n, (u n).2 ≠ 0) :
    ¬ Function.Injective (fun v : O => A (0, v)) := by
  intro hinj
  obtain ⟨c, hc, hA⟩ := exists_odd_lower_bound hinj
  obtain ⟨n, hn⟩ := (hu.eventually (eventually_odd_eq_zero hF hc hA hsym)).exists
  exact hodd n (hn (hzero n))

end ClosedSimilarity.OddLocalRigidity

#print axioms ClosedSimilarity.OddLocalRigidity.exists_ball_odd_eq_zero_of_injective
#print axioms ClosedSimilarity.OddLocalRigidity.not_injective_of_accumulating_odd_zeros

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.OddLocalRigidity).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "OddLocalRigidity audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do
    throwError "OddLocalRigidity audit checked no declarations"
  logInfo m!"OddLocalRigidity audit passed: {checked} declarations; standard axioms only."
