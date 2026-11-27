import SolitonClassification.CrossingStressResponse
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! Persistence of a simple zero under continuous, pointwise convergent
perturbations, and its application to the physical centre shot. -/
noncomputable section
open Filter Set Metric
open scoped Topology
namespace ClosedSimilarity.CrossingResponse

private theorem nearby_zero_of_positive_derivative {f : ℝ → ℝ} {a v : ℝ}
    (zero : f a = 0) (der : HasDerivAt f v a) (pos : 0 < v)
    (F : ℕ → ℝ → ℝ) (cont : ∀ n, Continuous (F n))
    (lim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∃ t, F n t = 0 ∧ dist a t < η := by
  have ev : ∀ᶠ x in 𝓝[≠] a, 0 < slope f a x := der.tendsto_slope.eventually (Ioi_mem_nhds pos)
  obtain ⟨ρ, hρ, slopePos⟩ := Metric.mem_nhdsWithin_iff.mp ev
  let d := min ρ η / 2
  have hd : 0 < d := half_pos (lt_min hρ hη)
  have dρ : d < ρ := (half_lt_self (lt_min hρ hη)).trans_le (min_le_left _ _)
  have dη : d < η := (half_lt_self (lt_min hρ hη)).trans_le (min_le_right _ _)
  have sgn (t : ℝ) (ht : |t-a| < ρ) (hne : t ≠ a) : 0 < f t / (t-a) := by
    have h := slopePos (show t ∈ Metric.ball a ρ ∩ ({a}ᶜ : Set ℝ) from
      ⟨by simpa [Metric.mem_ball, Real.dist_eq] using ht, hne⟩)
    simpa [slope_def_field, zero] using h
  have left : f (a-d) < 0 := by
    have h := sgn (a-d) (by simpa [abs_of_pos hd] using dρ) (by linarith)
    rcases div_pos_iff.mp h with h | h <;> linarith
  have right : 0 < f (a+d) := by
    have h := sgn (a+d) (by simpa [abs_of_pos hd] using dρ) (by linarith)
    rcases div_pos_iff.mp h with h | h <;> linarith
  filter_upwards [(lim (a-d)).eventually (Iio_mem_nhds left),
    (lim (a+d)).eventually (Ioi_mem_nhds right)] with n hn hp
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (show a-d ≤ a+d by linarith)
    (cont n).continuousOn (show (0:ℝ) ∈ Icc (F n (a-d)) (F n (a+d)) from ⟨le_of_lt hn,le_of_lt hp⟩)
  refine ⟨t, hzero, ?_⟩
  obtain ⟨lo,hi⟩ := ht
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

/-- Every simple zero has a sequence of true perturbed zeros converging to it.
Only pointwise convergence of the continuous perturbed functions is used. -/
theorem exists_roots_of_simple_limit {f : ℝ → ℝ} {a v : ℝ} (zero : f a = 0)
    (der : HasDerivAt f v a) (simple : v ≠ 0) (F : ℕ → ℝ → ℝ)
    (cont : ∀ n, Continuous (F n)) (lim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 a) ∧ ∀ᶠ n in atTop, F n (r n) = 0 := by
  classical
  have nearby (η : ℝ) (hη : 0 < η) : ∀ᶠ n in atTop, ∃ t, F n t = 0 ∧ dist a t < η := by
    rcases lt_or_gt_of_ne simple with hv | hv
    · have h := nearby_zero_of_positive_derivative (f := fun t => - f t) (by simp [zero])
        der.neg (neg_pos.mpr hv) (fun n t => -F n t) (fun n => (cont n).neg)
        (fun t => (lim t).neg) η hη
      simpa using h
    · exact nearby_zero_of_positive_derivative zero der hv F cont lim η hη
  let Z (n : ℕ) := {t | F n t = 0}
  have sel (n : ℕ) : ∃ x : ℝ, (Z n).Nonempty → x ∈ Z n ∧ infDist a (Z n) = dist a x := by
    by_cases ne : (Z n).Nonempty
    · obtain ⟨x, mem, least⟩ := (isClosed_eq (cont n) continuous_const).exists_infDist_eq_dist ne a
      exact ⟨x, fun _ => ⟨mem,least⟩⟩
    · exact ⟨a, fun h => (ne h).elim⟩
  choose r spec using sel
  refine ⟨r, Metric.tendsto_nhds.mpr ?_, ?_⟩
  · intro η hη
    filter_upwards [nearby η hη] with n hn
    obtain ⟨t,ht,close⟩ := hn
    have minr := (spec n ⟨t,ht⟩).2
    rw [dist_comm,← minr]
    exact (infDist_le_dist_of_mem (show t ∈ Z n from ht)).trans_lt close
  · filter_upwards [nearby 1 (by norm_num)] with n hn
    obtain ⟨t,ht,_⟩ := hn
    exact (spec n ⟨t,ht⟩).1

private theorem moving_value {F : ℝ → ℝ → ℝ} (cont : Continuous (fun z : ℝ × ℝ => F z.1 z.2))
    {e r : ℕ → ℝ} {d t : ℝ} (he : Tendsto e atTop (𝓝 d)) (hr : Tendsto r atTop (𝓝 t)) :
    Tendsto (fun n => F (e n) (r n)) atTop (𝓝 (F d t)) :=
  (cont.tendsto (d,t)).comp (he.prodMk_nhds hr)

/-- Actual intersections of the fast centre trajectory with a varying
seam line near any simple zero of the frozen horizontal coordinate. -/
theorem exists_axis_roots {a : ℝ} (root : K 0 a = 0) (simple : V 0 a ≠ 0)
    (e β : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hβ : Tendsto β atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 a) ∧
      ∀ᶠ n in atTop, X (e n) (r n) = β n * Y (e n) (r n) := by
  let F (n : ℕ) (t : ℝ) := X (e n) t - β n * Y (e n) t
  have cont n : Continuous (F n) := by
    have line : Continuous (fun t : ℝ => (e n,t)) := continuous_const.prodMk continuous_id
    exact (X_cont.comp line).sub ((Y_cont.comp line).const_mul (β n))
  have lim (t : ℝ) : Tendsto (fun n => F n t) atTop (𝓝 (K 0 t)) := by
    have tx := moving_value (F := X) X_cont he (tendsto_const_nhds (x := t))
    have ty := moving_value (F := Y) Y_cont he (tendsto_const_nhds (x := t))
    have q := tx.sub (hβ.mul ty)
    simpa [F, Function.comp_def, frozen_positionX] using q
  obtain ⟨r,hr,root'⟩ := exists_roots_of_simple_limit root (frozen_data.2.1 a) simple F cont lim
  exact ⟨r,hr,root'.mono fun n hn => sub_eq_zero.mp hn⟩

/-- Distinct limiting heights remain distinct simultaneously on a finite list. -/
theorem eventually_injective_heights {ι : Type*} [Finite ι] (h : ι → ℝ) (H : ℕ → ι → ℝ)
    (lim : ∀ i, Tendsto (fun n => H n i) atTop (𝓝 (h i))) (sep : Function.Injective h) :
    ∀ᶠ n in atTop, Function.Injective (H n) := by
  classical
  have pair (i j : ι) : ∀ᶠ n in atTop, H n i = H n j → i = j := by
    by_cases eq : i = j
    · exact Eventually.of_forall (fun _ _ => eq)
    · have neq : h i - h j ≠ 0 := sub_ne_zero.mpr (fun hh => eq (sep hh))
      filter_upwards [((lim i).sub (lim j)).eventually_ne neq] with n hn
      exact fun hh => (hn (sub_eq_zero.mpr hh)).elim
  filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (pair i))] with n hn
  exact fun {_ _} => hn _ _

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.exists_roots_of_simple_limit
#print axioms ClosedSimilarity.CrossingResponse.exists_axis_roots
#print axioms ClosedSimilarity.CrossingResponse.eventually_injective_heights
