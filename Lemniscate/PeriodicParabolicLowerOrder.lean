import Lemniscate.PeriodicParabolicInverse
import Lemniscate.PeriodicParabolicEstimates
import Mathlib.Analysis.SpecificLimits.Normed

/-! Bounded spatial H2-to-L2 perturbations of the principal parabolic
equation. The Neumann inverse acts on the forcing space after the actual
zero-initial inverse. Only zero-initial interpolation is used for smallness.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

private def lowerDataMap
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (initial : E →L[ℂ] F) (P BT : E →L[ℂ] G) : E →L[ℂ] (F × G) :=
  initial.prod (P-BT)

set_option maxHeartbeats 600000 in
private theorem lower_order_neumann_equiv
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (initial : E →L[ℂ] F) (P : E →L[ℂ] G) (e : E ≃L[ℂ] (F × G))
    (he : ∀ U : E, e U = (initial U,P U))
    (R0 : G →L[ℂ] E)
    (hRinitial : ∀ g : G, initial (R0 g) = 0) (hRrhs : ∀ g : G, P (R0 g) = g)
    (BT : E →L[ℂ] G) (hsmall : ∀ g : G, ‖BT (R0 g)‖ ≤ (1/2:ℝ)*‖g‖) :
    ∃ e' : E ≃L[ℂ] (F × G), e'.toContinuousLinearMap = lowerDataMap initial P BT := by
  let K : G →L[ℂ] G := BT.comp R0
  have hKnorm : ‖K‖ ≤ 1/2 := by
    apply ContinuousLinearMap.opNorm_le_bound K (by norm_num : (0:ℝ) ≤ 1/2)
    exact hsmall
  have hunit : IsUnit (1-K) := isUnit_one_sub_of_norm_lt_one
    (hKnorm.trans_lt (by norm_num : (1/2:ℝ) < 1))
  let J : G ≃L[ℂ] G := ContinuousLinearEquiv.unitsEquiv ℂ G hunit.unit
  have hJ (g : G) : J g = g-K g := by
    change (hunit.unit : G →L[ℂ] G) g = _
    rw [hunit.unit_spec]
    rfl
  have hdecomp (U : E) (hU : initial U = 0) : R0 (P U) = U := by
    apply e.injective
    rw [he,he,hRinitial,hRrhs,hU]
  let D : E →L[ℂ] (F × G) := lowerDataMap initial P BT
  have hkernel (U : E) (hU : D U = 0) : U = 0 := by
    have hi : initial U = 0 := congrArg Prod.fst hU
    have hp : P U-BT U = 0 := congrArg Prod.snd hU
    have hJU : J (P U) = 0 := by
      rw [hJ]
      change P U-BT (R0 (P U)) = 0
      rw [hdecomp U hi]
      exact hp
    have hPU : P U = 0 := J.injective (hJU.trans J.map_zero.symm)
    rw [← hdecomp U hi,hPU,map_zero]
  have hinj : Function.Injective D := by
    intro U V hUV
    apply sub_eq_zero.mp
    apply hkernel
    rw [map_sub,hUV,sub_self]
  have hsurj : Function.Surjective D := by
    rintro ⟨u0,f⟩
    let U0 : E := e.symm (u0,0)
    let g : G := J.symm (f+BT U0)
    have hdata0 : (initial U0,P U0) = (u0,0) :=
      (he U0).symm.trans (e.apply_symm_apply (u0,0))
    have hi : initial U0 = u0 := congrArg Prod.fst hdata0
    have hp : P U0 = 0 := congrArg Prod.snd hdata0
    have hg : g-BT (R0 g) = f+BT U0 :=
      (hJ g).symm.trans (J.apply_symm_apply (f+BT U0))
    refine ⟨U0+R0 g,?_⟩
    apply Prod.ext
    · change initial (U0+R0 g) = u0
      rw [map_add,hi,hRinitial,add_zero]
    · change P (U0+R0 g)-BT (U0+R0 g) = f
      rw [map_add,map_add,hp,hRrhs,zero_add]
      calc
        g-(BT U0+BT (R0 g)) = (g-BT (R0 g))-BT U0 := by abel
        _ = f := by rw [hg]; abel
  refine ⟨ContinuousLinearEquiv.ofBijective
    (𝕜 := ℂ) (𝕜' := ℂ) (σ := RingHom.id ℂ) (σ' := RingHom.id ℂ)
    (E := E) (F := F × G) D
    (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj),?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective D _ _

private theorem lower_interpolation_real
    (σ a b c u : ℝ) (hσ : 0 ≤ σ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hu : 0 ≤ u) (hbu : b ≤ u) (hcu : c ≤ u)
    (h : a^2 ≤ 3*σ^2*b*c) : a ≤ 2*σ*u := by
  have hbc : b*c ≤ u^2 := by simpa only [pow_two] using mul_le_mul hbu hcu hc hu
  have hs : a^2 ≤ (2*σ*u)^2 := by
    calc
      a^2 ≤ (3*σ^2)*(b*c) := by simpa only [mul_assoc] using h
      _ ≤ (3*σ^2)*u^2 := mul_le_mul_of_nonneg_left hbc (by positivity)
      _ ≤ (2*σ*u)^2 := by nlinarith only [sq_nonneg (σ*u)]
  exact (sq_le_sq₀ ha (by positivity : 0 ≤ 2*σ*u)).mp hs

private theorem lower_forcing_real_scale (σ b f : ℝ) :
    b*(2*σ*(10*f)) = (20*σ*b)*f := by ring

private theorem dependent_parameter_transfer {A : Type*}
    (p bound : A → Prop) (q : ∀ a : A, p a → Prop) (r : A → Prop)
    (h : ∃ a : A, ∃ ha : p a, bound a ∧ q a ha)
    (k : ∀ a : A, ∀ ha : p a, q a ha → r a) :
    ∃ a : A, p a ∧ bound a ∧ r a := by
  obtain ⟨a,ha,hb,hq⟩ := h
  exact ⟨a,ha,hb,k a ha hq⟩

variable (T : ℝ) [Fact (0 < T)]

/-- The actual time-L2 lower-order term, with its codomain fixed once. -/
def circleParabolicLowerTerm (τ : ℝ)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T) :
    CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T := by
  simpa only using!
    (B.compLpL 2 (volume : Measure unitInterval)).comp (circleParabolicH2Time T τ)

/-- Initial value and actual equation with a bounded spatial lower-order term. -/
def circleParabolicLowerOrderData (τ : ℝ)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T) :
    CircleParabolicSpace T τ →L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T) := by
  simpa only using! lowerDataMap
    (E := ↥(CircleParabolicSpace T τ)) (F := ↥(CircleSobolevSpace T 2))
    (G := ↥(CircleTimeL2 T))
    (circleParabolicInitialValue T τ) (circleParabolicPrincipalRHS T τ)
    (circleParabolicLowerTerm T τ B)

set_option maxHeartbeats 600000 in
private theorem lower_term_bound (τ : ℝ)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T) (U : CircleParabolicSpace T τ) :
    ‖circleParabolicLowerTerm T τ B U‖ ≤ ‖B‖*‖circleParabolicH2Time T τ U‖ := by
  let w : Lp (CircleSobolevSpace T 2) 2 (volume : Measure unitInterval) :=
    circleParabolicH2Time T τ U
  have h : ‖(B.compLpL 2 (volume : Measure unitInterval)) w‖ ≤ ‖B‖*‖w‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [B.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) w]
      with t ht
    have heq : ‖(B.compLpL 2 (volume : Measure unitInterval) w) t‖ = ‖B (w t)‖ :=
      congrArg (fun z : CircleL2 T => ‖z‖) ht
    exact heq.le.trans (B.le_opNorm (w t))
  simpa only [circleParabolicLowerTerm,ContinuousLinearMap.comp_apply,w] using! h

set_option maxHeartbeats 600000 in
private theorem lower_zero_h2_small (σ : ℝ) (hσ : 0 < σ)
    (U : CircleParabolicSpace T (σ^2))
    (hU : circleParabolicInitialValue T (σ^2) U = 0) :
    ‖circleParabolicH2Time T (σ^2) U‖ ≤ 2*σ*‖U‖ := by
  have hv : ‖circleParabolicTimeDerivative T (σ^2) U‖ ≤ ‖U‖ := by
    change ‖U.1.2.2‖ ≤ ‖U.1‖
    exact (norm_snd_le U.1.2).trans (norm_snd_le U.1)
  have hH : ‖circleParabolicH4 T (σ^2) U‖ ≤ ‖U‖ := by
    change ‖U.1.2.1‖ ≤ ‖U.1‖
    exact (norm_fst_le U.1.2).trans (norm_snd_le U.1)
  have hs : ‖circleParabolicH2Time T (σ^2) U‖^2 ≤
      3*σ^2*‖circleParabolicTimeDerivative T (σ^2) U‖*‖circleParabolicH4 T (σ^2) U‖ := by
    simpa only using! circle_parabolic_zero_initial_h2_time_interpolation T (σ^2)
      (sq_pos_of_pos hσ).le U hU
  exact lower_interpolation_real σ ‖circleParabolicH2Time T (σ^2) U‖
    ‖circleParabolicTimeDerivative T (σ^2) U‖ ‖circleParabolicH4 T (σ^2) U‖ ‖U‖
    hσ.le (norm_nonneg (circleParabolicH2Time T (σ^2) U))
    (norm_nonneg (circleParabolicH4 T (σ^2) U)) (norm_nonneg U) hv hH hs

set_option maxHeartbeats 600000 in
private theorem lower_order_small_time
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T) :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, τ ≤ 1 ∧ ∀ F : CircleTimeL2 T,
      ‖circleParabolicLowerTerm T τ B (circleParabolicZeroInitialInverse T τ hτ F)‖ ≤
        (1/2:ℝ)*‖F‖ := by
  let σ : ℝ := 1/(40*(‖B‖+1))
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hσeq : 40*(‖B‖+1)*σ = 1 := by
    dsimp only [σ]
    exact mul_one_div_cancel (by positivity : (40:ℝ)*(‖B‖+1) ≠ 0)
  have hσB : 20*σ*‖B‖ ≤ 1/2 := by nlinarith only [hσeq,hσ.le]
  have hσ1 : σ ≤ 1 := by
    have hp := mul_nonneg (norm_nonneg B) hσ.le
    nlinarith only [hσeq,hp]
  have hτ : 0 < σ^2 := sq_pos_of_pos hσ
  have hτ1 : σ^2 ≤ 1 := by
    simpa only [pow_two,one_mul] using
      mul_le_mul hσ1 hσ1 hσ.le (by norm_num : (0:ℝ) ≤ 1)
  refine ⟨σ^2,hτ,hτ1,?_⟩
  intro F
  let U : CircleParabolicSpace T (σ^2) := circleParabolicZeroInitialInverse T (σ^2) hτ F
  have hu0 : circleParabolicInitialValue T (σ^2) U = 0 :=
    circle_parabolic_zero_initial_inverse_initial T (σ^2) hτ F
  have huBound : ‖U‖ ≤ 10*‖F‖ :=
    circle_parabolic_zero_initial_inverse_bound T (σ^2) hτ hτ1 F
  have hH2 : ‖circleParabolicH2Time T (σ^2) U‖ ≤ 2*σ*‖U‖ :=
    lower_zero_h2_small T σ hσ U hu0
  calc
    ‖circleParabolicLowerTerm T (σ^2) B U‖ ≤ ‖B‖*‖circleParabolicH2Time T (σ^2) U‖ :=
      lower_term_bound T (σ^2) B U
    _ ≤ ‖B‖*(2*σ*‖U‖) := mul_le_mul_of_nonneg_left hH2 (norm_nonneg B)
    _ ≤ ‖B‖*(2*σ*(10*‖F‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left huBound (mul_nonneg (by norm_num) hσ.le)) (norm_nonneg B)
    _ = (20*σ*‖B‖)*‖F‖ := lower_forcing_real_scale σ ‖B‖ ‖F‖
    _ ≤ (1/2:ℝ)*‖F‖ := mul_le_mul_of_nonneg_right hσB (norm_nonneg F)

set_option maxHeartbeats 600000 in
private theorem lower_order_fixed_time (τ : ℝ) (hτ : 0 < τ)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hsmall : ∀ F : CircleTimeL2 T,
      ‖circleParabolicLowerTerm T τ B (circleParabolicZeroInitialInverse T τ hτ F)‖ ≤
        (1/2:ℝ)*‖F‖) :
    ∃ e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T),
      e.toContinuousLinearMap = circleParabolicLowerOrderData T τ B := by
  simpa only [circleParabolicLowerOrderData] using! lower_order_neumann_equiv
    (E := ↥(CircleParabolicSpace T τ)) (F := ↥(CircleSobolevSpace T 2))
    (G := ↥(CircleTimeL2 T))
    (circleParabolicInitialValue T τ) (circleParabolicPrincipalRHS T τ)
    (circleParabolicDataEquiv T τ hτ)
    (fun U => by simpa only using! circle_parabolic_data_equiv_apply T τ hτ U)
    (circleParabolicZeroInitialInverse T τ hτ)
    (fun F => by simpa only using! circle_parabolic_zero_initial_inverse_initial T τ hτ F)
    (fun F => by simpa only using! circle_parabolic_zero_initial_inverse_rhs T τ hτ F)
    (circleParabolicLowerTerm T τ B)
    (fun F => by simpa only [ContinuousLinearMap.comp_apply] using! hsmall F)

set_option maxHeartbeats 600000 in
/-- Every bounded H2-to-L2 spatial perturbation has an actual continuous
linear solution isomorphism on some positive time interval of length at
most one. Its forward map records exactly the initial trace and forcing. -/
theorem circle_parabolic_lower_order_isomorphism
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      ∃ e : CircleParabolicSpace T τ ≃L[ℂ]
          (CircleSobolevSpace T 2 × CircleTimeL2 T),
        e.toContinuousLinearMap = circleParabolicLowerOrderData T τ B := by
  exact dependent_parameter_transfer (fun τ : ℝ => 0 < τ) (fun τ => τ ≤ 1)
    (fun τ hτ => ∀ F : CircleTimeL2 T,
      ‖circleParabolicLowerTerm T τ B (circleParabolicZeroInitialInverse T τ hτ F)‖ ≤
        (1/2:ℝ)*‖F‖)
    (fun τ => ∃ e : CircleParabolicSpace T τ ≃L[ℂ]
        (CircleSobolevSpace T 2 × CircleTimeL2 T),
      e.toContinuousLinearMap = circleParabolicLowerOrderData T τ B)
    (lower_order_small_time T B) (fun τ hτ => lower_order_fixed_time T τ hτ B)

end Lemniscate
