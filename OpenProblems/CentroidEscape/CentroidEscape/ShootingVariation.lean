import CentroidEscape.BallInterior
import CentroidEscape.WeightedDerivatives

/-!
# Actual finite-horizon shooting flow and its parameter neighborhood

The flow is selected from proved bounded-field existence, and its finite
horizon values are unique. Initial-value estimates are derived from the
actual ODE. Checked interior trajectories give an explicit open initial
neighborhood where the clipped flow solves the original polynomial ODE.
-/
namespace CentroidEscape
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

def shootingFlow (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (a : WeightedState) : WeightedState :=
  (exists_ode_on_finite_interval clippedField 8 2 a T hT
    clippedField_lipschitz clippedField_bound).choose t

lemma shootingFlow_zero (T : ℝ) (hT : 0 ≤ T) (a : WeightedState) :
    shootingFlow T hT 0 a = a :=
  (exists_ode_on_finite_interval clippedField 8 2 a T hT
    clippedField_lipschitz clippedField_bound).choose_spec.1

theorem shootingFlow_derivative (T : ℝ) (hT : 0 ≤ T) (a : WeightedState)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (fun r => shootingFlow T hT r a)
      (clippedField (shootingFlow T hT t a)) t :=
  (exists_ode_on_finite_interval clippedField 8 2 a T hT
    clippedField_lipschitz clippedField_bound).choose_spec.2 t ht

theorem shootingFlow_unique (T : ℝ) (hT : 0 ≤ T) {a : WeightedState}
    {z : ℝ → WeightedState} (hz0 : z 0=a)
    (hz : ∀ t ∈ Icc 0 T, HasDerivAt z (clippedField (z t)) t) :
    EqOn z (fun t => shootingFlow T hT t a) (Icc 0 T) :=
  clipped_step_unique hz (fun _ ht => shootingFlow_derivative T hT a ht)
    (hz0.trans (shootingFlow_zero T hT a).symm)

theorem shootingFlow_distance (T : ℝ) (hT : 0 ≤ T) (a b : WeightedState)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (shootingFlow T hT t a) (shootingFlow T hT t b) ≤ dist a b*exp (8*t) := by
  have he := approximate_step_error clippedField 8 0 t 0 ht.1 le_rfl
    (fun s => shootingFlow T hT s a) (fun s => shootingFlow T hT s b)
    (fun s => clippedField (shootingFlow T hT s b)) clippedField_lipschitz
    (fun r hr => (shootingFlow_derivative T hT a ⟨hr.1,hr.2.trans ht.2⟩).continuousAt.continuousWithinAt)
    (fun r hr => shootingFlow_derivative T hT a ⟨hr.1,hr.2.le.trans ht.2⟩)
    (fun r hr => (shootingFlow_derivative T hT b ⟨hr.1,hr.2.trans ht.2⟩).continuousAt.continuousWithinAt)
    (fun r hr => shootingFlow_derivative T hT b ⟨hr.1,hr.2.le.trans ht.2⟩)
    (fun r _ => by simp)
  simpa only [shootingFlow_zero, zero_mul, add_zero, sub_zero, NNReal.coe_ofNat] using he

theorem shootingFlow_initial_lipschitz (T : ℝ) (hT : 0 ≤ T)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    LipschitzWith ⟨exp (8*t), (exp_pos _).le⟩ (shootingFlow T hT t) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  change dist _ _ ≤ exp (8*t)*dist a b
  simpa only [mul_comm] using shootingFlow_distance T hT a b ht

theorem shootingFlow_time_lipschitz (T : ℝ) (hT : 0 ≤ T) (a : WeightedState) :
    LipschitzOnWith 2 (fun t => shootingFlow T hT t a) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (shootingFlow_derivative T hT a ht).hasDerivWithinAt)
  intro t _
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact clippedField_bound _

theorem shootingFlow_inner_of_checked_grid {S N : ℕ} (hS : 0<S) (hN : 0<N)
    {h : ℚ} (hh : 0 ≤ h) (hhmax : h ≤ 1/100) {b : BallVector}
    (hc : (computeBallGrid S h b N).checks = true) {a : WeightedState}
    (ha : ∀ i, (b i).Contains (a i)) :
    ∀ t ∈ Icc 0 ((N:ℝ)*(h:ℝ)),
      shootingFlow ((N:ℝ)*(h:ℝ)) (mul_nonneg (Nat.cast_nonneg N) (Rat.cast_nonneg.mpr hh)) t a
        ∈ innerWeightedTube := by
  apply checked_ball_grid_inner hS hN hh hhmax hc
  · simpa only [shootingFlow_zero] using ha
  · intro t ht
    exact shootingFlow_derivative _ _ a ht

def shootingNeighborhoodRadius (T : ℝ) : ℝ := (1/4000)*exp (-8*T)

lemma shootingNeighborhoodRadius_pos (T : ℝ) : 0 < shootingNeighborhoodRadius T := by
  unfold shootingNeighborhoodRadius
  positivity

theorem shootingFlow_near_reference (T : ℝ) (hT : 0 ≤ T) {a b : WeightedState}
    (hab : dist b a < shootingNeighborhoodRadius T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (shootingFlow T hT t b) (shootingFlow T hT t a) < 1/4000 := by
  calc
    dist (shootingFlow T hT t b) (shootingFlow T hT t a) ≤ dist b a*exp (8*t) :=
      shootingFlow_distance T hT b a ht
    _ ≤ dist b a*exp (8*T) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [ht.2])) dist_nonneg
    _ < shootingNeighborhoodRadius T*exp (8*T) :=
      mul_lt_mul_of_pos_right hab (exp_pos _)
    _ = 1/4000 := by
      rw [shootingNeighborhoodRadius, mul_assoc, ← exp_add]
      ring_nf
      simp

/-- Every nearby initial state follows the original polynomial field for
the whole horizon, from the checked reference's proved interior margin. -/
theorem shootingFlow_neighborhood_original (T : ℝ) (hT : 0 ≤ T) {a : WeightedState}
    (ha : ∀ t ∈ Icc 0 T, shootingFlow T hT t a ∈ innerWeightedTube)
    {b : WeightedState} (hb : dist b a < shootingNeighborhoodRadius T) :
    ∀ t ∈ Icc 0 T, HasDerivAt (fun r => shootingFlow T hT r b)
      (weightedField (shootingFlow T hT t b)) t := by
  intro t ht
  have hd := shootingFlow_near_reference T hT hb ht
  have he := clippedField_eq_on_inner_ball (ha t ht)
    (show shootingFlow T hT t b ∈ Metric.ball (shootingFlow T hT t a) (1/2000) by
      change dist _ _ < _
      linarith)
  simpa only [he] using shootingFlow_derivative T hT b ht

/-- Parameters are the original unweighted (a,b,L), and output is (y,u,v).
The factors 1/16, 4 and 64 implement the actual state weights. -/
def shootingInitial (p : Fin 3 → ℝ) : WeightedState := ![p 0,0,0,1/4,p 1/16,0,0]

def shootingProjection (z : WeightedState) : Fin 3 → ℝ := ![z 1,4*z 2,64*z 5]

def actualShootingMap (T : ℝ) (hT : 0 ≤ T) (p : Fin 3 → ℝ) : Fin 3 → ℝ :=
  shootingProjection (shootingFlow T hT (p 2) (shootingInitial p))

theorem shootingInitial_lipschitz : LipschitzWith 1 shootingInitial := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have hp0 := norm_le_pi_norm (p-q) 0
  have hp1 := norm_le_pi_norm (p-q) 1
  fin_cases i <;> norm_num [shootingInitial, Pi.sub_apply, ← sub_div, norm_div] at * <;>
    linarith [norm_nonneg (p-q)]

theorem shootingProjection_lipschitz : LipschitzWith 64 shootingProjection := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [NNReal.coe_ofNat, dist_eq_norm]
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  have h1 := weighted_coord_bound (a-b) 1
  have h2 := weighted_coord_bound (a-b) 2
  have h5 := weighted_coord_bound (a-b) 5
  simp only [Pi.sub_apply] at h1 h2 h5
  fin_cases i <;> norm_num [Pi.sub_apply, shootingProjection, ← mul_sub, Real.norm_eq_abs, abs_mul]
  all_goals nlinarith [norm_nonneg (a-b)]

/-- A useful sharp exponential forcing estimate. Augmenting by the exact
scalar majorant avoids replacing exp(16*t) by a horizon-wide constant and
therefore avoids an unnecessary exp(24*T) loss. -/
theorem norm_le_exp_forcing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {T C : ℝ} (hC : 0 ≤ C) (hf0 : f 0=0)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Icc 0 T, ‖f' t‖ ≤ 8*‖f t‖+C*exp (16*t)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ C/8*exp (16*t) := by
  let v : ℝ → ℝ := fun t => C/8*exp (16*t)
  let F : ℝ → E × ℝ := fun t => (f t,v t)
  let D : ℝ → E × ℝ := fun t => (f' t,2*C*exp (16*t))
  have hv : ∀ t, HasDerivAt v (2*C*exp (16*t)) t := by
    intro t
    convert! (((hasDerivAt_id t).const_mul 16).exp.const_mul (C/8)) using 1
    simp only [id_eq]
    ring
  have hF : ∀ t ∈ Icc 0 T, HasDerivAt F (D t) t :=
    fun t ht => (hf t ht).prodMk (hv t)
  have hB : ∀ t ∈ Icc 0 T, ‖D t‖ ≤ 16*‖F t‖ := by
    intro t ht
    have hvt : 0 ≤ v t := mul_nonneg (div_nonneg hC (by norm_num)) (exp_pos _).le
    have hx : ‖f t‖ ≤ max ‖f t‖ (v t) := le_max_left _ _
    have hy : v t ≤ max ‖f t‖ (v t) := le_max_right _ _
    dsimp [F, D]
    simp only [abs_of_nonneg hvt, abs_of_nonneg (by positivity : 0 ≤ 2*C*exp (16*t))]
    apply max_le
    · have hb := hbound t ht
      dsimp [v] at hy
      nlinarith
    · dsimp [v] at hy
      nlinarith
  intro t ht
  have hC8 : 0 ≤ C/8 := by positivity
  have hF0 : ‖F 0‖ ≤ C/8 := by
    simp [F, v, hf0, Prod.norm_def, abs_of_nonneg hC, hC8]
  have hn := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun r hr => (hF r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hF r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (δ := C/8) (K := 16) (ε := 0)
    hF0
    (fun r hr => by simpa only [add_zero] using hB r ⟨hr.1,hr.2.le⟩) t ht
  have hx : ‖f t‖ ≤ ‖F t‖ := by
    dsimp [F]
    exact le_max_left _ _
  exact hx.trans (by simpa only [gronwallBound_ε0, sub_zero] using hn)

def stateMidpoint (a b : WeightedState) : WeightedState := (1/2:ℝ) • (a+b)

lemma stateMidpoint_mem {a b : WeightedState} (ha : a ∈ weightedTube) (hb : b ∈ weightedTube) :
    stateMidpoint a b ∈ weightedTube := by
  intro i hi
  change |(1/2:ℝ)*(a i+b i)| ≤ tubeRadius i
  rw [abs_mul]
  norm_num
  have hh := abs_add_le (a i) (b i)
  linarith [ha i hi,hb i hi]

lemma weightedField_midpoint_defect {a b : WeightedState}
    (ha : a ∈ weightedTube) (hb : b ∈ weightedTube) :
    ‖(1/2:ℝ) • (weightedField a+weightedField b)-weightedField (stateMidpoint a b)‖ ≤
      (11/2:ℝ)*‖a-b‖^2 := by
  have he : (1/2:ℝ) • (weightedField a+weightedField b)-weightedField (stateMidpoint a b) =
      weightedBilinear (stateMidpoint a b) ((1/2:ℝ) • (a-b)) ((1/2:ℝ) • (a-b)) := by
    ext i
    fin_cases i <;> simp [stateMidpoint, weightedField, weightedBilinear] <;> ring
  rw [he]
  have hn := weightedBilinear_bound (stateMidpoint_mem ha hb)
    ((1/2:ℝ) • (a-b)) ((1/2:ℝ) • (a-b))
  norm_num [norm_smul, Real.norm_eq_abs] at hn
  nlinarith

/-- A second finite-difference bound for the ACTUAL flow, derived from the
polynomial midpoint residual. No derivative of the flow is assumed. -/
theorem shootingFlow_midpoint_quadratic (T : ℝ) (hT : 0 ≤ T) (a b : WeightedState)
    (ha : ∀ t ∈ Icc 0 T, shootingFlow T hT t a ∈ weightedTube)
    (hb : ∀ t ∈ Icc 0 T, shootingFlow T hT t b ∈ weightedTube) :
    ∀ t ∈ Icc 0 T,
      ‖stateMidpoint (shootingFlow T hT t a) (shootingFlow T hT t b) -
        shootingFlow T hT t (stateMidpoint a b)‖ ≤
        (11/16:ℝ)*exp (16*t)*dist a b^2 := by
  let p : ℝ → WeightedState := fun t =>
    stateMidpoint (shootingFlow T hT t a) (shootingFlow T hT t b)
  let pd : ℝ → WeightedState := fun t =>
    (1/2:ℝ) • (weightedField (shootingFlow T hT t a)+weightedField (shootingFlow T hT t b))
  let z : ℝ → WeightedState := fun t => shootingFlow T hT t (stateMidpoint a b)
  have hp : ∀ t ∈ Icc 0 T, HasDerivAt p (pd t) t := by
    intro t ht
    have hda := shootingFlow_derivative T hT a ht
    have hdb := shootingFlow_derivative T hT b ht
    rw [clippedField_eq (ha t ht)] at hda
    rw [clippedField_eq (hb t ht)] at hdb
    exact (hda.add hdb).const_smul (1/2:ℝ)
  have hz : ∀ t ∈ Icc 0 T, HasDerivAt z (clippedField (z t)) t :=
    fun t ht => shootingFlow_derivative T hT _ ht
  have hres : ∀ t ∈ Icc 0 T, ‖pd t-clippedField (p t)‖ ≤
      (11/2:ℝ)*dist a b^2*exp (16*t) := by
    intro t ht
    have hpt : p t ∈ weightedTube := stateMidpoint_mem (ha t ht) (hb t ht)
    rw [clippedField_eq hpt]
    have hd := weightedField_midpoint_defect (ha t ht) (hb t ht)
    have he := shootingFlow_distance T hT a b ht
    have hsq := (sq_le_sq₀ (dist_nonneg : 0 ≤ dist (shootingFlow T hT t a)
      (shootingFlow T hT t b)) (mul_nonneg dist_nonneg (exp_pos _).le)).mpr he
    have hE : exp (8*t)^2=exp (16*t) := by
      rw [pow_two,← exp_add]
      congr 1
      ring
    rw [mul_pow,hE] at hsq
    rw [dist_eq_norm] at hsq
    exact hd.trans (by nlinarith)
  have hnorm : ∀ t ∈ Icc 0 T,
      ‖pd t-clippedField (z t)‖ ≤ 8*‖p t-z t‖+(11/2:ℝ)*dist a b^2*exp (16*t) := by
    intro t ht
    have hn := norm_add_le (pd t-clippedField (p t)) (clippedField (p t)-clippedField (z t))
    rw [sub_add_sub_cancel] at hn
    have hl := clippedField_lipschitz.dist_le_mul (p t) (z t)
    simp only [dist_eq_norm, NNReal.coe_ofNat] at hl
    linarith [hres t ht]
  have hh := norm_le_exp_forcing (f := fun t => p t-z t)
    (f' := fun t => pd t-clippedField (z t))
    (C := (11/2:ℝ)*dist a b^2) (by positivity)
    (by simp [p,z,shootingFlow_zero])
    (fun t ht => (hp t ht).sub (hz t ht)) hnorm
  intro t ht
  convert! hh t ht using 1
  ring

lemma weightedTube_mem_of_near_inner {a b : WeightedState} (ha : a ∈ innerWeightedTube)
    (hb : dist b a < 1/2000) : b ∈ weightedTube := by
  intro i hi
  have hd : |b i-a i| ≤ dist b a := by
    simpa only [dist_eq_norm, Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (b-a) i
  have hs := abs_add_le (b i-a i) (a i)
  rw [sub_add_cancel] at hs
  linarith [ha i hi]

theorem shootingFlow_midpoint_quadratic_of_inner (T : ℝ) (hT : 0 ≤ T)
    {c : WeightedState} (hc : ∀ t ∈ Icc 0 T, shootingFlow T hT t c ∈ innerWeightedTube)
    {a b : WeightedState} (ha : dist a c < shootingNeighborhoodRadius T)
    (hb : dist b c < shootingNeighborhoodRadius T) :
    ∀ t ∈ Icc 0 T,
      ‖stateMidpoint (shootingFlow T hT t a) (shootingFlow T hT t b) -
        shootingFlow T hT t (stateMidpoint a b)‖ ≤
        (11/16:ℝ)*exp (16*t)*dist a b^2 := by
  apply shootingFlow_midpoint_quadratic T hT a b
  · intro t ht
    exact weightedTube_mem_of_near_inner (hc t ht)
      (lt_trans (shootingFlow_near_reference T hT ha ht) (by norm_num))
  · intro t ht
    exact weightedTube_mem_of_near_inner (hc t ht)
      (lt_trans (shootingFlow_near_reference T hT hb ht) (by norm_num))

theorem actualShootingState_distance (T : ℝ) (hT : 0 ≤ T) (p q : Fin 3 → ℝ)
    (hp : p 2 ∈ Icc 0 T) (hq : q 2 ∈ Icc 0 T) :
    dist (shootingFlow T hT (p 2) (shootingInitial p))
      (shootingFlow T hT (q 2) (shootingInitial q)) ≤ (exp (8*T)+2)*dist p q := by
  have hi : dist (shootingInitial p) (shootingInitial q) ≤ dist p q := by
    simpa using shootingInitial_lipschitz.dist_le_mul p q
  have ht : dist (p 2) (q 2) ≤ dist p q := by
    simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (p-q) 2
  have hfirst := shootingFlow_distance T hT (shootingInitial p) (shootingInitial q) hp
  have htime := (shootingFlow_time_lipschitz T hT (shootingInitial q)).dist_le_mul
    (p 2) hp (q 2) hq
  have he := exp_le_exp.mpr (show 8*p 2 ≤ 8*T by linarith [hp.2])
  have hprod : dist (shootingInitial p) (shootingInitial q)*exp (8*p 2) ≤
      dist p q*exp (8*T) := mul_le_mul hi he (exp_pos _).le dist_nonneg
  have htri := dist_triangle (shootingFlow T hT (p 2) (shootingInitial p))
    (shootingFlow T hT (p 2) (shootingInitial q))
    (shootingFlow T hT (q 2) (shootingInitial q))
  norm_num only [NNReal.coe_ofNat] at htime
  nlinarith

theorem actualShootingMap_distance (T : ℝ) (hT : 0 ≤ T) (p q : Fin 3 → ℝ)
    (hp : p 2 ∈ Icc 0 T) (hq : q 2 ∈ Icc 0 T) :
    dist (actualShootingMap T hT p) (actualShootingMap T hT q) ≤
      (64*(exp (8*T)+2))*dist p q := by
  have he := shootingProjection_lipschitz.dist_le_mul
    (shootingFlow T hT (p 2) (shootingInitial p))
    (shootingFlow T hT (q 2) (shootingInitial q))
  have hd := actualShootingState_distance T hT p q hp hq
  change dist (actualShootingMap T hT p) (actualShootingMap T hT q) ≤ 64*_
    at he
  nlinarith

end
end CentroidEscape

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Shooting-variation audit passed for {checked} declarations."
