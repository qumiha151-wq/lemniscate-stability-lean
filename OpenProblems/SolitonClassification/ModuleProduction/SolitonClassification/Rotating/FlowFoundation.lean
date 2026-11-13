module

public import SolitonClassification.Rotating.BoundedODE
public import SolitonClassification.Rotating.ResidualODE

@[expose] public section

/-! Actual global flow of a bounded Lipschitz extension of the support field.
The extension equals the original polynomial on the outer tube. It is only
used to select an everywhere-defined flow; original-ODE claims explicitly
prove or require tube confinement. No flow regularity in initial data is
assumed. Both signs of integration are covered by the same construction. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Metric Real
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false

def clipScalar (r x : ℝ) : ℝ := min (max x (-r)) r

lemma clipScalar_lipschitz (r : ℝ) : LipschitzWith 1 (clipScalar r) :=
  (LipschitzWith.id.max_const (-r)).min_const r

lemma clipScalar_bound {r : ℝ} (hr : 0≤r) (x : ℝ) : |clipScalar r x|≤r := by
  rw [abs_le]
  exact ⟨le_min (le_max_right _ _) (by linarith),min_le_right _ _⟩

lemma clipScalar_eq_self {r x : ℝ} (h : |x|≤r) : clipScalar r x=x := by
  rcases abs_le.mp h with ⟨hl,hu⟩
  simp [clipScalar,max_eq_left hl,min_eq_left hu]

def clippingRadius : Fin 6 → ℝ := ![17/2,9/2,17/2,17/2,1/50,0]
def clipState (a : State) : State :=
  fun i => if i=5 then a i else clipScalar (clippingRadius i) (a i)

theorem clipState_mem (a : State) : clipState a∈outerTube := by
  exact ⟨clipScalar_bound (r:=17/2) (by norm_num) (a 0),
    clipScalar_bound (r:=9/2) (by norm_num) (a 1),
    clipScalar_bound (r:=17/2) (by norm_num) (a 2),
    clipScalar_bound (r:=17/2) (by norm_num) (a 3),
    clipScalar_bound (r:=1/50) (by norm_num) (a 4)⟩

theorem clipState_eq_self {a : State} (ha : a∈outerTube) : clipState a=a := by
  ext i
  fin_cases i
  · exact clipScalar_eq_self ha.1
  · exact clipScalar_eq_self ha.2.1
  · exact clipScalar_eq_self ha.2.2.1
  · exact clipScalar_eq_self ha.2.2.2.1
  · exact clipScalar_eq_self ha.2.2.2.2
  · rfl

theorem clipState_lipschitz : LipschitzWith 1 clipState := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  simp only [NNReal.coe_one,one_mul]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have hd : |a i-b i|≤‖a-b‖ := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_le_pi_norm (a-b) i
  simp only [Pi.sub_apply,Real.norm_eq_abs,clipState]
  by_cases hi : i=5
  · simpa only [if_pos hi] using hd
  · simp only [if_neg hi]
    have hl := (clipScalar_lipschitz (clippingRadius i)).dist_le_mul (a i) (b i)
    have he : |clipScalar (clippingRadius i) (a i)-clipScalar (clippingRadius i) (b i)|≤|a i-b i| := by
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hl
    exact he.trans hd

def clippedField (a : State) : State := field (clipState a)

theorem clippedField_bound (a : State) : ‖clippedField a‖≤75 := field_bound (clipState_mem a)

theorem clippedField_eq {a : State} (ha : a∈outerTube) : clippedField a=field a := by
  rw [clippedField,clipState_eq_self ha]

theorem clippedField_lipschitz : LipschitzWith 17 clippedField := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  have hf := lipschitzOnWith_iff_norm_sub_le.mp field_lipschitz_on
    (clipState_mem a) (clipState_mem b)
  have hc := lipschitzWith_iff_norm_sub_le.mp clipState_lipschitz a b
  simp only [NNReal.coe_one,one_mul] at hc
  exact hf.trans (mul_le_mul_of_nonneg_left hc (by positivity))

def signedClippedField (σ : ℝ) (a : State) : State := σ • clippedField a

theorem signedClippedField_lipschitz {σ : ℝ} (hσ : |σ|≤1) :
    LipschitzWith 17 (signedClippedField σ) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro a b
  simp only [signedClippedField,←smul_sub,norm_smul,Real.norm_eq_abs]
  have h := lipschitzWith_iff_norm_sub_le.mp clippedField_lipschitz a b
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans (by simpa using h)

theorem signedClippedField_bound {σ : ℝ} (hσ : |σ|≤1) (a : State) :
    ‖signedClippedField σ a‖≤75 := by
  rw [signedClippedField,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
    (by simpa using clippedField_bound a)

def supportFlow (σ : ℝ) (hσ : |σ|≤1) (t : ℝ) (a : State) : State :=
  (exists_unique_global_bounded_flow (signedClippedField_lipschitz hσ)
    (M:=75) (signedClippedField_bound hσ) a).exists.choose t

theorem supportFlow_zero (σ : ℝ) (hσ : |σ|≤1) (a : State) : supportFlow σ hσ 0 a=a :=
  (exists_unique_global_bounded_flow (signedClippedField_lipschitz hσ)
    (M:=75) (signedClippedField_bound hσ) a).exists.choose_spec.1

theorem supportFlow_derivative (σ : ℝ) (hσ : |σ|≤1) (a : State) (t : ℝ) :
    HasDerivAt (fun s => supportFlow σ hσ s a)
      (signedClippedField σ (supportFlow σ hσ t a)) t :=
  (exists_unique_global_bounded_flow (signedClippedField_lipschitz hσ)
    (M:=75) (signedClippedField_bound hσ) a).exists.choose_spec.2 t

theorem supportFlow_original_derivative (σ : ℝ) (hσ : |σ|≤1) (a : State) (t : ℝ)
    (htube : supportFlow σ hσ t a∈outerTube) :
    HasDerivAt (fun s => supportFlow σ hσ s a) (σ • field (supportFlow σ hσ t a)) t := by
  simpa only [signedClippedField,clippedField_eq htube] using supportFlow_derivative σ hσ a t

theorem supportFlow_unique (σ : ℝ) (hσ : |σ|≤1) {a : State} {x : ℝ → State}
    (h0 : x 0=a) (hx : ∀t,HasDerivAt x (signedClippedField σ (x t)) t) :
    x=fun t => supportFlow σ hσ t a :=
  (exists_unique_global_bounded_flow (signedClippedField_lipschitz hσ)
    (M:=75) (signedClippedField_bound hσ) a).unique ⟨h0,hx⟩
      ⟨supportFlow_zero σ hσ a,supportFlow_derivative σ hσ a⟩

theorem supportFlow_distance (σ : ℝ) (hσ : |σ|≤1) (a b : State)
    {t : ℝ} (ht : 0≤t) :
    dist (supportFlow σ hσ t a) (supportFlow σ hσ t b)≤dist a b*exp (17*t) := by
  have he := dist_le_of_trajectories_ODE
    (v:=fun _ => signedClippedField σ) (K:=17)
    (fun _ => signedClippedField_lipschitz hσ)
    (fun r _ => (supportFlow_derivative σ hσ a r).continuousAt.continuousWithinAt)
    (fun r _ => (supportFlow_derivative σ hσ a r).hasDerivWithinAt)
    (fun r _ => (supportFlow_derivative σ hσ b r).continuousAt.continuousWithinAt)
    (fun r _ => (supportFlow_derivative σ hσ b r).hasDerivWithinAt)
    (by simp only [supportFlow_zero]; exact le_rfl) t ⟨ht,le_rfl⟩
  simpa only [supportFlow_zero,sub_zero,NNReal.coe_ofNat] using he

theorem supportFlow_initial_lipschitz (σ : ℝ) (hσ : |σ|≤1) {t : ℝ} (ht : 0≤t) :
    LipschitzWith ⟨exp (17*t),(exp_pos _).le⟩ (supportFlow σ hσ t) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist _ _≤exp (17*t)*dist a b
  simpa only [mul_comm] using supportFlow_distance σ hσ a b ht

theorem supportFlow_time_lipschitz (σ : ℝ) (hσ : |σ|≤1) (a : State) :
    LipschitzWith 75 (fun t => supportFlow σ hσ t a) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (supportFlow_derivative σ hσ a t).differentiableAt
  · intro t
    rw [←NNReal.coe_le_coe,coe_nnnorm,(supportFlow_derivative σ hσ a t).deriv]
    exact signedClippedField_bound hσ _

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual-flow audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual-flow audit passed for {count} declarations."

end
