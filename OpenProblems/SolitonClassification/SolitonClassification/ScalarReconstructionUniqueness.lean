import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Zero-jet uniqueness for the regular scalar reconstruction equation.
The third-order equation is used through its actual three scalar derivatives.
The growth estimate is proved from its polynomial vector field; uniqueness is
then obtained from Grönwall on compact segments, in either orientation. -/

namespace ClosedSimilarity.ScalarReconstruction
noncomputable section
open Set

/-- The regular nonautonomous reconstruction field at a fixed value of `H`. -/
def reconstructionField (H : ℝ) (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (z.2.1, z.2.2, z.1 * H - (3 / 2 : ℝ) * z.1 ^ 2 * z.2.1)

/-- The actual polynomial field is smooth jointly in the coefficient and state. -/
theorem reconstructionField_joint_contDiff :
    ContDiff ℝ 1 (fun p : ℝ × (ℝ × ℝ × ℝ) => reconstructionField p.1 p.2) := by
  unfold reconstructionField
  fun_prop

/-- Local Lipschitz regularity is derived from the polynomial, not postulated. -/
theorem reconstructionField_joint_locallyLipschitz :
    LocallyLipschitz (fun p : ℝ × (ℝ × ℝ × ℝ) => reconstructionField p.1 p.2) :=
  reconstructionField_joint_contDiff.locallyLipschitz

/-- In particular, the state field at each fixed coefficient is locally Lipschitz. -/
theorem reconstructionField_locallyLipschitz (H : ℝ) :
    LocallyLipschitz (reconstructionField H) := by
  have h : ContDiff ℝ 1 (reconstructionField H) := by
    unfold reconstructionField
    fun_prop
  exact h.locallyLipschitz

/-- A growth bound derived directly from the reconstruction polynomial. -/
theorem reconstructionField_norm_le (H : ℝ) (z : ℝ × ℝ × ℝ) :
    ‖reconstructionField H z‖ ≤ (1 + |H| + (3 / 2 : ℝ) * z.1 ^ 2) * ‖z‖ := by
  have hk : |z.1| ≤ ‖z‖ := norm_fst_le z
  have hv : |z.2.1| ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  have hw : |z.2.2| ≤ ‖z‖ := (norm_snd_le z.2).trans (norm_snd_le z)
  have hn := norm_nonneg z
  have hc : 0 ≤ (3 / 2 : ℝ) * z.1 ^ 2 := by positivity
  have hC : ‖z‖ ≤ (1 + |H| + (3 / 2 : ℝ) * z.1 ^ 2) * ‖z‖ := by
    nlinarith [abs_nonneg H, mul_nonneg (abs_nonneg H) hn, mul_nonneg hc hn]
  have hthird : |z.1 * H - (3 / 2 : ℝ) * z.1 ^ 2 * z.2.1| ≤
      (|H| + (3 / 2 : ℝ) * z.1 ^ 2) * ‖z‖ := by
    calc
      _ ≤ |z.1 * H| + |(3 / 2 : ℝ) * z.1 ^ 2 * z.2.1| := abs_sub _ _
      _ = |H| * |z.1| + ((3 / 2 : ℝ) * z.1 ^ 2) * |z.2.1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc]
        ring
      _ ≤ |H| * ‖z‖ + ((3 / 2 : ℝ) * z.1 ^ 2) * ‖z‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hk (abs_nonneg H))
          (mul_le_mul_of_nonneg_left hv hc)
      _ = _ := by ring
  change max |z.2.1| (max |z.2.2| |z.1 * H - (3 / 2 : ℝ) * z.1 ^ 2 * z.2.1|) ≤ _
  exact max_le (hv.trans hC) (max_le (hw.trans hC) (by nlinarith))

/-- Grönwall zero propagation in either direction on a real segment. -/
theorem zero_of_norm_deriv_le_on_uIcc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {s t C : ℝ} (hf : Continuous f)
    (hd : ∀ x ∈ uIcc s t, HasDerivAt f (f' x) x)
    (hb : ∀ x ∈ uIcc s t, ‖f' x‖ ≤ C * ‖f x‖)
    (hs : f s = 0) : f t = 0 := by
  rcases le_total s t with hst | hts
  · have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (a := s) (b := t) (f := f) (f' := f') (K := C) hf.continuousOn
      (fun x hx => (hd x (by simpa [uIcc_of_le hst] using ⟨hx.1, hx.2.le⟩)).hasDerivWithinAt)
      hs (fun x hx => hb x (by simpa [uIcc_of_le hst] using ⟨hx.1, hx.2.le⟩))
    exact h t ⟨hst, le_rfl⟩
  · have hmem : ∀ x ∈ Ico 0 (s - t), s - x ∈ uIcc s t := by
      intro x hx
      rw [uIcc_of_ge hts]
      constructor <;> linarith [hx.1, hx.2]
    have hdrev : ∀ x ∈ Ico 0 (s - t),
        HasDerivWithinAt (fun x => f (s - x)) (-f' (s - x)) (Ici x) x := by
      intro x hx
      exact ((hd (s - x) (hmem x hx)).comp_const_sub s x).hasDerivWithinAt
    have hbrev : ∀ x ∈ Ico 0 (s - t),
        ‖-f' (s - x)‖ ≤ C * ‖f (s - x)‖ := by
      intro x hx
      simpa only [norm_neg] using hb (s - x) (hmem x hx)
    have h := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (a := 0) (b := s - t) (f := fun x => f (s - x))
      (f' := fun x => -f' (s - x)) (K := C)
      (hf.comp (continuous_const.sub continuous_id)).continuousOn
      hdrev (by simpa using hs) hbrev
    simpa using h (s - t) ⟨by linarith, le_rfl⟩

/-- A zero curvature jet cannot leave zero while it solves the regular scalar
equation. The interval is unoriented, so this also propagates backwards. -/
theorem zero_jet_of_regular_ode_on_uIcc
    {k v w H : ℝ → ℝ} {s t : ℝ}
    (hk : Continuous k) (hv : Continuous v) (hw : Continuous w) (hH : Continuous H)
    (hdk : ∀ x ∈ uIcc s t, HasDerivAt k (v x) x)
    (hdv : ∀ x ∈ uIcc s t, HasDerivAt v (w x) x)
    (hdw : ∀ x ∈ uIcc s t,
      HasDerivAt w (k x * H x - (3 / 2 : ℝ) * k x ^ 2 * v x) x)
    (hks : k s = 0) (hvs : v s = 0) (hws : w s = 0) :
    k t = 0 ∧ v t = 0 ∧ w t = 0 := by
  let f : ℝ → ℝ × ℝ × ℝ := fun x => (k x, v x, w x)
  let C : ℝ → ℝ := fun x => 1 + |H x| + (3 / 2 : ℝ) * k x ^ 2
  have hC : Continuous C := continuous_const.add hH.abs |>.add
    (continuous_const.mul (hk.pow 2))
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn hC.continuousOn
  have hzero : f t = 0 := zero_of_norm_deriv_le_on_uIcc
      (f' := fun x => reconstructionField (H x) (f x))
      (hk.prodMk (hv.prodMk hw))
      (fun x hx => (hdk x hx).prodMk ((hdv x hx).prodMk (hdw x hx)))
      (fun x hx => (reconstructionField_norm_le (H x) (f x)).trans
        (mul_le_mul_of_nonneg_right
          ((le_abs_self (C x)).trans (hM x hx)) (norm_nonneg (f x))))
      (by simp [f, hks, hvs, hws])
  simpa [f] using hzero

/-- The zero jet propagates throughout any real interval on which the actual
regular ODE holds. No maximality or nonvanishing-curvature hypothesis is used. -/
theorem zero_jet_of_regular_ode_on_ordConnected
    {k v w H : ℝ → ℝ} {I : Set ℝ} {s : ℝ}
    (hI : OrdConnected I) (hs : s ∈ I)
    (hk : Continuous k) (hv : Continuous v) (hw : Continuous w) (hH : Continuous H)
    (hdk : ∀ x ∈ I, HasDerivAt k (v x) x)
    (hdv : ∀ x ∈ I, HasDerivAt v (w x) x)
    (hdw : ∀ x ∈ I,
      HasDerivAt w (k x * H x - (3 / 2 : ℝ) * k x ^ 2 * v x) x)
    (hks : k s = 0) (hvs : v s = 0) (hws : w s = 0) :
    ∀ t ∈ I, k t = 0 ∧ v t = 0 ∧ w t = 0 := by
  intro t ht
  exact zero_jet_of_regular_ode_on_uIcc hk hv hw hH
    (fun x hx => hdk x (hI.uIcc_subset hs ht hx))
    (fun x hx => hdv x (hI.uIcc_subset hs ht hx))
    (fun x hx => hdw x (hI.uIcc_subset hs ht hx)) hks hvs hws

end
end ClosedSimilarity.ScalarReconstruction

#print axioms ClosedSimilarity.ScalarReconstruction.zero_jet_of_regular_ode_on_uIcc

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"ScalarReconstructionUniqueness: audited {checked} declarations; standard axioms only."
