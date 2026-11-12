import SolitonClassification.Rotating.FlowFoundation
import SolitonClassification.Rotating.DerivativeVariation

/-! Initial-state derivatives constructed from actual ODE midpoint estimates.
The only region premise is confinement of the selected actual flow. Neither
flow differentiability nor a variational equation is assumed. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Real Filter
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
theorem norm_le_exp_forcing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {T C : ℝ} (hC : 0 ≤ C) (hf0 : f 0=0)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Icc 0 T, ‖f' t‖ ≤ 17*‖f t‖+C*exp (34*t)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ C/17*exp (34*t) := by
  let v : ℝ → ℝ := fun t => C/17*exp (34*t)
  let F : ℝ → E × ℝ := fun t => (f t,v t)
  let D : ℝ → E × ℝ := fun t => (f' t,2*C*exp (34*t))
  have hv : ∀ t, HasDerivAt v (2*C*exp (34*t)) t := by
    intro t
    convert! (((hasDerivAt_id t).const_mul 34).exp.const_mul (C/17)) using 1
    simp only [id_eq]
    ring
  have hF : ∀ t ∈ Icc 0 T, HasDerivAt F (D t) t :=
    fun t ht => (hf t ht).prodMk (hv t)
  have hB : ∀ t ∈ Icc 0 T, ‖D t‖ ≤ 34*‖F t‖ := by
    intro t ht
    have hvt : 0 ≤ v t := mul_nonneg (div_nonneg hC (by norm_num)) (exp_pos _).le
    have hx : ‖f t‖ ≤ max ‖f t‖ (v t) := le_max_left _ _
    have hy : v t ≤ max ‖f t‖ (v t) := le_max_right _ _
    dsimp [F, D]
    simp only [abs_of_nonneg hvt, abs_of_nonneg (by positivity : 0 ≤ 2*C*exp (34*t))]
    apply max_le
    · have hb := hbound t ht
      dsimp [v] at hy
      nlinarith
    · dsimp [v] at hy
      nlinarith
  intro t ht
  have hC17 : 0 ≤ C/17 := by positivity
  have hF0 : ‖F 0‖ ≤ C/17 := by
    simp [F, v, hf0, Prod.norm_def, abs_of_nonneg hC, hC17]
  have hn := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun r hr => (hF r hr).continuousAt.continuousWithinAt)
    (fun r hr => (hF r ⟨hr.1,hr.2.le⟩).hasDerivWithinAt)
    (δ := C/17) (K := 34) (ε := 0)
    hF0
    (fun r hr => by simpa only [add_zero] using hB r ⟨hr.1,hr.2.le⟩) t ht
  have hx : ‖f t‖ ≤ ‖F t‖ := by
    dsimp [F]
    exact le_max_left _ _
  exact hx.trans (by simpa only [gronwallBound_ε0, sub_zero] using hn)

def stateMidpoint (a b : State) : State := (1/2:ℝ) • (a+b)

theorem stateMidpoint_mem {a b : State} (ha : a∈outerTube) (hb : b∈outerTube) :
    stateMidpoint a b∈outerTube := by
  have h := outerTube_convex ha hb (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+1/2=1)
  simpa only [stateMidpoint,smul_add] using h

theorem field_midpoint_defect {a b : State} (ha : a∈outerTube) (hb : b∈outerTube) :
    ‖(1/2:ℝ) • (field a+field b)-field (stateMidpoint a b)‖≤(1/2:ℝ)*‖a-b‖^2 := by
  have he : (1/2:ℝ) • (field a+field b)-field (stateMidpoint a b)=
      bilinear (stateMidpoint a b) ((1/2:ℝ) • (a-b)) ((1/2:ℝ) • (a-b)) := by
    ext i
    fin_cases i <;> simp [stateMidpoint,field,bilinear] <;> ring
  rw [he]
  have hn := bilinear_bound (stateMidpoint_mem ha hb) ((1/2:ℝ) • (a-b)) ((1/2:ℝ) • (a-b))
  norm_num [norm_smul,Real.norm_eq_abs] at hn
  nlinarith

/-- A quadratic second finite difference for the actual selected flow,
obtained by comparing its midpoint path with the midpoint initial solution. -/
theorem supportFlow_midpoint_quadratic (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} (a b : State)
    (ha : ∀t∈Icc 0 T,supportFlow σ hσ t a∈outerTube)
    (hb : ∀t∈Icc 0 T,supportFlow σ hσ t b∈outerTube) :
    ∀t∈Icc 0 T,
      ‖stateMidpoint (supportFlow σ hσ t a) (supportFlow σ hσ t b)-
        supportFlow σ hσ t (stateMidpoint a b)‖≤(1/34:ℝ)*exp (34*t)*dist a b^2 := by
  let p : ℝ → State := fun t => stateMidpoint (supportFlow σ hσ t a) (supportFlow σ hσ t b)
  let pd : ℝ → State := fun t =>
    (1/2:ℝ) • (σ • field (supportFlow σ hσ t a)+σ • field (supportFlow σ hσ t b))
  let z : ℝ → State := fun t => supportFlow σ hσ t (stateMidpoint a b)
  have hp : ∀t∈Icc 0 T,HasDerivAt p (pd t) t := by
    intro t ht
    exact ((supportFlow_original_derivative σ hσ a t (ha t ht)).add
      (supportFlow_original_derivative σ hσ b t (hb t ht))).const_smul (1/2:ℝ)
  have hz : ∀t,HasDerivAt z (signedClippedField σ (z t)) t :=
    supportFlow_derivative σ hσ (stateMidpoint a b)
  have hres : ∀t∈Icc 0 T,‖pd t-signedClippedField σ (p t)‖≤
      (1/2:ℝ)*dist a b^2*exp (34*t) := by
    intro t ht
    have hpt : p t∈outerTube := stateMidpoint_mem (ha t ht) (hb t ht)
    have heq : pd t-signedClippedField σ (p t)=
        σ • ((1/2:ℝ) • (field (supportFlow σ hσ t a)+field (supportFlow σ hσ t b))-field (p t)) := by
      rw [signedClippedField,clippedField_eq hpt]
      dsimp [pd]
      module
    rw [heq,norm_smul,Real.norm_eq_abs]
    have hd := field_midpoint_defect (ha t ht) (hb t ht)
    have he := supportFlow_distance σ hσ a b ht.1
    have hsq := (sq_le_sq₀ (dist_nonneg : 0≤dist (supportFlow σ hσ t a)
      (supportFlow σ hσ t b)) (mul_nonneg dist_nonneg (exp_pos _).le)).mpr he
    have hE : exp (17*t)^2=exp (34*t) := by
      rw [pow_two,←exp_add]
      congr 1
      ring
    rw [mul_pow,hE,dist_eq_norm] at hsq
    have hm := mul_le_mul_of_nonneg_right hσ
      (norm_nonneg ((1/2:ℝ) • (field (supportFlow σ hσ t a)+field (supportFlow σ hσ t b))-field (p t)))
    dsimp [p] at hm ⊢
    nlinarith
  have hnorm : ∀t∈Icc 0 T,‖pd t-signedClippedField σ (z t)‖≤
      17*‖p t-z t‖+(1/2:ℝ)*dist a b^2*exp (34*t) := by
    intro t ht
    have hn := norm_add_le (pd t-signedClippedField σ (p t))
      (signedClippedField σ (p t)-signedClippedField σ (z t))
    rw [sub_add_sub_cancel] at hn
    have hl := (signedClippedField_lipschitz hσ).dist_le_mul (p t) (z t)
    simp only [dist_eq_norm,NNReal.coe_ofNat] at hl
    linarith [hres t ht]
  have hh := norm_le_exp_forcing (f:=fun t => p t-z t)
    (f':=fun t => pd t-signedClippedField σ (z t))
    (C:=(1/2:ℝ)*dist a b^2) (by positivity)
    (by simp [p,z,stateMidpoint,supportFlow_zero])
    (fun t ht => (hp t ht).sub (hz t)) hnorm
  intro t ht
  convert! hh t ht using 1
  ring

/-- Confinement concerns actual chosen solutions for every initial point in
an open ball, and every time in the closed horizon. -/
def FlowTubeNeighborhood (σ : ℝ) (hσ : |σ|≤1) (T : ℝ) (c : State) (R : ℝ) : Prop :=
  ∀a∈Metric.ball c R,∀t∈Icc 0 T,supportFlow σ hσ t a∈outerTube

theorem supportFlow_local_midpoint (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ∀a∈Metric.ball c R,∀b∈Metric.ball c R,
      ‖supportFlow σ hσ t ((1/2:ℝ) • (a+b))-
        (1/2:ℝ) • (supportFlow σ hσ t a+supportFlow σ hσ t b)‖≤
        ((1/34:ℝ)*exp (34*t))*‖a-b‖^2 := by
  intro a ha b hb
  have hm := supportFlow_midpoint_quadratic σ hσ a b (hreg a ha) (hreg b hb) t ht
  rw [norm_sub_rev] at hm
  simpa only [stateMidpoint,dist_eq_norm] using hm

/-- Genuine initial-state differentiability is a conclusion from the ODE
and confinement, not an extra property of an assumed smooth flow. -/
theorem supportFlow_hasFDerivAt_initial (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T) :
    HasFDerivAt (supportFlow σ hσ t) (fderiv ℝ (supportFlow σ hσ t) a) a :=
  (quadraticMidpoint_fderiv_at (supportFlow_initial_lipschitz σ hσ ht.1)
    (by positivity) (supportFlow_local_midpoint σ hσ hreg ht) ha).1

theorem supportFlow_initial_quadratic_remainder (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a : State} (ha : a∈Metric.ball c R) {t : ℝ} (ht : t∈Icc 0 T)
    {u : State} (hu : ‖u‖<R-dist a c) :
    ‖supportFlow σ hσ t (a+u)-supportFlow σ hσ t a-fderiv ℝ (supportFlow σ hσ t) a u‖≤
      (2/17:ℝ)*exp (34*t)*‖u‖^2 := by
  have h := (quadraticMidpoint_fderiv_at (supportFlow_initial_lipschitz σ hσ ht.1)
    (by positivity) (supportFlow_local_midpoint σ hσ hreg ht) ha).2 u hu
  convert! h using 1
  ring

theorem supportFlow_fderiv_space_variation (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R : ℝ} (hR : 0<R) (hreg : FlowTubeNeighborhood σ hσ T c R)
    {a b : State} (ha : a∈Metric.ball c (R/4)) (hb : b∈Metric.ball c (R/4))
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖fderiv ℝ (supportFlow σ hσ t) a-fderiv ℝ (supportFlow σ hσ t) b‖≤
      (12/17:ℝ)*exp (34*T)*dist a b := by
  have hh := quadraticMidpoint_fderiv_variation (supportFlow_initial_lipschitz σ hσ ht.1)
    hR (by positivity) (supportFlow_local_midpoint σ hσ hreg ht) ha hb
  have he := mul_le_mul_of_nonneg_left
    (exp_le_exp.mpr (by linarith [ht.2] : 34*t≤34*T)) (dist_nonneg (x:=a) (y:=b))
  nlinarith

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual differentiability audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual differentiability audit passed for {count} declarations."


