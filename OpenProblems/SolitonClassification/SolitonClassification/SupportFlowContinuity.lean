import SolitonClassification.GlobalSupportFlow

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Metric Filter
open scoped NNReal Topology

/-- Adjoin the constant driving rate as a fifth state coordinate. -/
abbrev Data := ℝ × Phase

def solution (d : ℝ) (x : Phase) : ℝ → Phase := (exists_unique_solution d x).choose
lemma solution_zero (d : ℝ) (x : Phase) : solution d x 0 = x :=
  (exists_unique_solution d x).choose_spec.1.1
lemma solution_derivative (d : ℝ) (x : Phase) (t : ℝ) :
    HasDerivAt (solution d x) (rhs d (solution d x t)) t :=
  (exists_unique_solution d x).choose_spec.1.2 t

def velocity (a : Data) : Data := (0,rhs a.1 a.2)
def extended (a : Data) (t : ℝ) : Data := (a.1,solution a.1 a.2 t)

lemma velocity_smooth : ContDiff ℝ 1 velocity := by
  apply ContDiff.prodMk contDiff_const
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [rhs] <;> fun_prop

lemma extended_zero (a : Data) : extended a 0 = a := by simp [extended,solution_zero]
lemma extended_derivative (a : Data) (t : ℝ) :
    HasDerivAt (extended a) (velocity (extended a t)) t :=
  (hasDerivAt_const t a.1).prodMk (solution_derivative a.1 a.2 t)

lemma extended_confinement (a : Data) {t T : ℝ} (ht : |t| ≤ T) :
    ‖extended a t‖ ≤ max |a.1| (radius a.1 T a.2) := by
  have hd (s : ℝ) : HasDerivAt (solution a.1 a.2) ((1:ℝ) • rhs a.1 (solution a.1 a.2 s)) s := by
    simpa using solution_derivative a.1 a.2 s
  have h := confinement ((abs_nonneg t).trans ht) (by simp : ∀ _ : ℝ, |(1:ℝ)| ≤ 1) hd ht
  rw [solution_zero] at h
  exact max_le_max_left _ h

/-- Across a compact set of initial positions and driving rates, there is one
Lipschitz constant valid on the whole two-sided time slab. -/
theorem compact_initial_estimate {S : Set Data} (hS : IsCompact S) {T : ℝ} (_hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ S, ∀ b ∈ S, ∀ t : ℝ, |t| ≤ T →
      dist (extended a t) (extended b t) ≤ C * dist a b := by
  let B := fun a : Data => max |a.1| (radius a.1 T a.2)
  have hB : Continuous B := by unfold B radius positionSize stressSize; fun_prop
  obtain ⟨R,hR⟩ := hS.bddAbove_image hB.continuousOn
  let ball := closedBall (0 : Data) R
  have inside (a : Data) (ha : a ∈ S) {u : ℝ} (hu : |u| ≤ T) : extended a u ∈ ball := by
    rw [show ball = closedBall (0 : Data) R from rfl,mem_closedBall_iff_norm,sub_zero]
    exact (extended_confinement a hu).trans (hR (mem_image_of_mem B ha))
  obtain ⟨K,hK⟩ := velocity_smooth.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : Data) R) (isCompact_closedBall (0 : Data) R)
  refine ⟨Real.exp (K*T),Real.exp_pos _,?_⟩
  intro a ha b hb t ht
  let σ : ℝ := if t < 0 then -1 else 1
  have hσ : |σ| = 1 := by unfold σ; split <;> norm_num
  have htime : σ*|t| = t := by
    unfold σ; split_ifs with H
    · rw [abs_of_neg H]; ring
    · rw [abs_of_nonneg (le_of_not_gt H),one_mul]
  let V := fun x : Data => σ • velocity x
  let f := fun (x : Data) (s : ℝ) => extended x (σ*s)
  have hV : LipschitzOnWith K V ball := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x hx y hy
    simpa only [V,←smul_sub,norm_smul,Real.norm_eq_abs,hσ,one_mul] using
      (lipschitzOnWith_iff_norm_sub_le.mp hK hx hy)
  have D (x : Data) (s : ℝ) : HasDerivAt (f x) (V (f x s)) s := by
    have hs : HasDerivAt (fun r : ℝ => σ*r) σ s := by simpa using (hasDerivAt_id s).const_mul σ
    exact (extended_derivative x (σ*s)).scomp s hs
  have stay (x : Data) (hx : x ∈ S) (s : ℝ) (hs : s ∈ Ico 0 |t|) : f x s ∈ ball := by
    apply inside x hx
    rw [abs_mul,hσ,one_mul,abs_of_nonneg hs.1]
    exact hs.2.le.trans ht
  have hzero (x : Data) : f x 0 = x := by simp [f,extended_zero]
  have est := dist_le_of_trajectories_ODE_of_mem (v := fun _ => V) (s := fun _ => ball)
    (fun _ _ => hV) (fun s _ => (D a s).continuousAt.continuousWithinAt)
    (fun s _ => (D a s).hasDerivWithinAt) (stay a ha)
    (fun s _ => (D b s).continuousAt.continuousWithinAt)
    (fun s _ => (D b s).hasDerivWithinAt) (stay b hb)
    (by simp only [hzero]; exact le_rfl) |t| ⟨abs_nonneg _,le_rfl⟩
  simp only [f,htime,sub_zero] at est
  calc
    _ ≤ _ := est
    _ ≤ dist a b * Real.exp (K*T) := by
      apply mul_le_mul_of_nonneg_left _ (dist_nonneg)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht K.coe_nonneg)
    _ = _ := mul_comm _ _

/-- Joint continuity in real arclength, driving rate (including d = 0),
and all four initial support coordinates. -/
theorem continuous_solution :
    Continuous (fun w : ℝ × Data => solution w.2.1 w.2.2 w.1) := by
  suffices h : Continuous (fun w : ℝ × Data => extended w.2 w.1) from continuous_snd.comp h
  rw [continuous_iff_continuousAt]
  intro w
  let S := closedBall w.2 1
  let T := |w.1|+1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C,_,hC⟩ := compact_initial_estimate (S := S) (isCompact_closedBall _ _) hT
  have h0 : w.2 ∈ S := mem_closedBall_self zero_le_one
  have hs : ∀ᶠ u : ℝ × Data in 𝓝 w, u.2 ∈ S :=
    continuous_snd.continuousAt (closedBall_mem_nhds _ zero_lt_one)
  have hτ : ∀ᶠ u : ℝ × Data in 𝓝 w, |u.1| < T :=
    ((continuous_abs.comp continuous_fst).tendsto w).eventually
      (eventually_lt_nhds (by dsimp [T]; linarith))
  have hc : Tendsto (fun u : ℝ × Data => C*dist w.2 u.2) (𝓝 w) (𝓝 0) := by
    have h : Continuous (fun u : ℝ × Data => C*dist w.2 u.2) := by fun_prop
    simpa using h.tendsto w
  apply (((extended_derivative w.2 w.1).continuousAt.comp continuous_fst.continuousAt).tendsto).congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ hc
  filter_upwards [hs,hτ] with u hu hτ'
  exact hC _ h0 _ hu _ hτ'.le

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.compact_initial_estimate
#print axioms ClosedSimilarity.GlobalSupport.continuous_solution
