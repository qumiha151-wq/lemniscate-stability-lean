import SolitonClassification.SupportBounds
import SolitonClassification.FrozenStress

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Filter
open scoped NNReal Topology
open SolitonClassification.Rotating (exists_unique_global_bounded_flow interval_solutions_agree)

/-- An actual solution on every finite interval, with a radius independent of truncation. -/
theorem finite_solution (d : ℝ) (x : Phase) (T : ℝ≥0) :
    ∃ f : ℝ → Phase, f 0 = x ∧ ∀ t : ℝ, |t| ≤ (T : ℝ) →
      ‖f t‖ ≤ radius d T x ∧ HasDerivAt f (rhs d (f t)) t := by
  let R := radius d T x
  obtain ⟨g,K,M,hK,hM,hg⟩ := bounded_scaled_extension d R (radius_pos _ T.coe_nonneg _).le
  obtain ⟨f,⟨h0,hf⟩,_⟩ := exists_unique_global_bounded_flow hK hM x
  have hd (t : ℝ) : HasDerivAt f (weight R (f t) • rhs d (f t)) t := by
    rw [←hg]; exact hf t
  refine ⟨f,h0,fun t ht => ?_⟩
  have h := confinement T.coe_nonneg (fun u => by
    rw [abs_of_nonneg (weight_mem R (f u)).1]; exact (weight_mem R _).2) hd ht
  rw [h0] at h
  have hw : weight R (f t) = 1 := weight_one h
  exact ⟨h, by simpa only [hw,one_smul] using hd t⟩

lemma finite_agree {d : ℝ} {x : Phase} {A B : ℝ≥0} (hA : 0 < (A : ℝ)) (hB : 0 < (B : ℝ))
    {f g : ℝ → Phase} (h0 : f 0 = g 0)
    (hf : ∀ t : ℝ, |t| ≤ (A : ℝ) → ‖f t‖ ≤ radius d A x ∧ HasDerivAt f (rhs d (f t)) t)
    (hg : ∀ t : ℝ, |t| ≤ (B : ℝ) → ‖g t‖ ≤ radius d B x ∧ HasDerivAt g (rhs d (g t)) t)
    {t : ℝ} (htA : |t| < A) (htB : |t| < B) : f t = g t := by
  let S := max (radius d A x) (radius d B x)
  obtain ⟨G,K,_,hK,_,hG⟩ := bounded_scaled_extension d S
    ((radius_pos d A.coe_nonneg x).le.trans (le_max_left _ _))
  apply interval_solutions_agree hK hA hB (f := f) (h := g) _ _ h0 htA htB
  · intro u hu
    obtain ⟨hbound,hd⟩ := hf u (abs_lt.mpr hu).le
    have hw : weight S (f u) = 1 := weight_one (hbound.trans (le_max_left _ _))
    simpa only [hG,hw,one_smul] using hd
  · intro u hu
    obtain ⟨hbound,hd⟩ := hg u (abs_lt.mpr hu).le
    have hw : weight S (g u) = 1 := weight_one (hbound.trans (le_max_right _ _))
    simpa only [hG,hw,one_smul] using hd

/-- Two-sided global existence and uniqueness for the unmodified polynomial field,
for every initial state and every constant tangential driving rate. -/
theorem exists_unique_solution (d : ℝ) (x : Phase) :
    ∃! f : ℝ → Phase, f 0 = x ∧ ∀ t, HasDerivAt f (rhs d (f t)) t := by
  choose f h0 hd using finite_solution d x
  let A : ℝ → ℝ≥0 := fun t => ⟨|t|+1,by positivity⟩
  let φ := fun t => f (A t) t
  have hφ0 : φ 0 = x := h0 _
  have hφ (t : ℝ) : HasDerivAt φ (rhs d (φ t)) t := by
    let B : ℝ≥0 := ⟨|t|+2,by positivity⟩
    have hB : 0 < (B : ℝ) := by change 0 < |t|+2; positivity
    have htB : |t| < (B : ℝ) := by change |t| < |t|+2; linarith
    have heq : φ =ᶠ[𝓝 t] f B := by
      have hn := (continuous_abs.tendsto t).eventually (eventually_lt_nhds htB)
      filter_upwards [hn] with u hu
      exact finite_agree (by change 0 < |u|+1; positivity) hB
        ((h0 _).trans (h0 _).symm) (hd (A u)) (hd B) (by change |u| < |u|+1; linarith) hu
    have H := ((hd B t htB.le).2).congr_of_eventuallyEq heq
    simpa only [heq.eq_of_nhds] using H
  refine ⟨φ,⟨hφ0,hφ⟩,?_⟩
  intro g hg
  have aux {y : ℝ → Phase} (hy0 : y 0 = x) (hy : ∀ t, HasDerivAt y (rhs d (y t)) t)
      (B : ℝ≥0) (t : ℝ) (ht : |t| ≤ B) :
      ‖y t‖ ≤ radius d B x ∧ HasDerivAt y (rhs d (y t)) t := by
    refine ⟨?_,hy t⟩
    rw [←hy0]
    exact confinement (μ := fun _ => 1) B.coe_nonneg (by simp) (by simpa using hy) ht
  funext t
  have hA : 0 < (A t : ℝ) := by change 0 < |t|+1; positivity
  have htA : |t| < (A t : ℝ) := by change |t| < |t|+1; linarith
  exact finite_agree hA hA (hg.1.trans hφ0.symm) (aux hg.1 hg.2 _) (aux hφ0 hφ _) htA htA

/-- The seam used in the frozen endpoint theorem is realized by a unit-support
orbit on all of ℝ for each prescribed initial curvature. -/
theorem exists_frozen_seam (c : ℝ) :
    ∃ z : FrozenStress.Orbit, z.k 0 = c ∧ z.v 0 = 0 ∧ z.p 0 = 1 ∧ z.q 0 = 0 := by
  obtain ⟨f,⟨h0,hf⟩,_⟩ := exists_unique_solution 0 ![c,0,1,0]
  have dk (t : ℝ) : HasDerivAt (fun s => f s 0) (f t 1) t := hasDerivAt_pi.mp (hf t) 0
  have dv (t : ℝ) : HasDerivAt (fun s => f s 1) (-(f t 0)^3/2-f t 2) t :=
    hasDerivAt_pi.mp (hf t) 1
  have dp (t : ℝ) : HasDerivAt (fun s => f s 2) (-f t 0*f t 3) t := hasDerivAt_pi.mp (hf t) 2
  have dq (t : ℝ) : HasDerivAt (fun s => f s 3) (f t 0*f t 2) t := by
    simpa [rhs] using hasDerivAt_pi.mp (hf t) 3
  have unit (t : ℝ) : (f t 2)^2+(f t 3)^2 = 1 := by
    have hd (s : ℝ) : HasDerivAt (fun u => (f u 2)^2+(f u 3)^2) 0 s := by
      convert! ((dp s).pow 2).add ((dq s).pow 2) using 1
      ring
    have h := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simpa [h0] using h
  exact ⟨⟨_,_,_,_,dk,dv,dp,dq,unit⟩,by simp [h0]⟩

end ClosedSimilarity.GlobalSupport

#print axioms ClosedSimilarity.GlobalSupport.exists_unique_solution
#print axioms ClosedSimilarity.GlobalSupport.exists_frozen_seam
