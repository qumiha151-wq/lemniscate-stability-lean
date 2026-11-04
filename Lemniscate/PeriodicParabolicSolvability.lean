import Lemniscate.PeriodicParabolicDataApproximation
import Lemniscate.PeriodicParabolicEquation
import Lemniscate.PeriodicFiniteParabolicEstimates
import Lemniscate.PeriodicFiniteFourierExtension
import Lemniscate.BanachDenseSolvability
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose

/-! Existence for the actual fourth-order principal parabolic equation.

Finite Fourier solutions form a Cauchy sequence in the already complete
closed parabolic space. The initial condition and the equation pass to
the limit through continuous linear maps. Uniqueness is not used here.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

local instance parabolicSolverTimeSecondCountable :
    SecondCountableTopologyEither unitInterval (CircleL2 T) where
  out := Or.inl (inferInstance : SecondCountableTopology unitInterval)

set_option maxHeartbeats 1000000 in
private structure FiniteParabolicWitness (τ : ℝ) where
  modes : Finset ℤ
  coeff : modes → ℝ → ℂ
  velocityCoeff : modes → ℝ → ℂ
  forcingCoeff : modes → ℝ → ℂ
  forcingContinuous : ∀ n : modes, Continuous (forcingCoeff n)
  derivative : ∀ (n : modes) (r : ℝ), HasDerivAt (coeff n) (τ • velocityCoeff n r) r
  modeEquation : ∀ (n : modes) (r : ℝ), velocityCoeff n r+
    (1+4*‖circleFrequencyFactor T n‖^4) • coeff n r = forcingCoeff n r
  value : CircleParabolicSpace T τ
  curve : ∀ t : unitInterval, circleParabolicCurve T τ value t =
    circleSobolevFourierSynthesis T 2 modes (fun n => coeff n (t:ℝ))
  high : ∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ value t =
    circleSobolevFourierSynthesis T 4 modes (fun n => coeff n (t:ℝ))
  velocity : ∀ᵐ t : unitInterval ∂volume, circleParabolicTimeDerivative T τ value t =
    circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 modes
      (fun n => velocityCoeff n (t:ℝ)))
  equation : circleParabolicPrincipalRHS T τ value =
    circleFiniteFourierTimeForcing T modes forcingCoeff forcingContinuous

private theorem finite_forcing_ae (I : Finset ℤ) (G : I → ℝ → ℂ)
    (hG : ∀ n, Continuous (G n)) :
    (circleFiniteFourierTimeForcing T I G hG : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleSobolevCoordinate T 4 0
        (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))) :=
  ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
    ⟨fun t => circleSobolevCoordinate T 4 0
      (circleSobolevFourierSynthesis T 4 I (fun n => G n (t:ℝ))),
      (circleSobolevCoordinate T 4 0).continuous.comp
        ((circleSobolevFourierSynthesis T 4 I).continuous.comp
          ((continuous_pi hG).comp continuous_subtype_val))⟩

set_option maxHeartbeats 1000000 in
private theorem finite_witness_bound (τ : ℝ) (hτ : 0 < τ)
    (d : FiniteParabolicWitness T τ) :
    ‖d.value‖^2 ≤ 40*((1+τ)*‖circleParabolicPrincipalRHS T τ d.value‖^2+
      (1+τ⁻¹)*‖circleParabolicInitialValue T τ d.value‖^2) := by
  have hres (n : d.modes) (r : ℝ) :
      d.forcingCoeff n r-(1+4*‖circleFrequencyFactor T n‖^4) • d.coeff n r =
        d.velocityCoeff n r := by
    rw [← d.modeEquation n r,add_sub_cancel_right]
  have hd := d.derivative
  have hv := d.velocity
  simp only [← hres] at hd hv
  have h := circle_finite_parabolic_estimate T τ hτ d.modes
    d.forcingCoeff d.forcingContinuous d.coeff hd d.value d.curve d.high hv
  rw [← d.equation] at h
  exact h

set_option maxHeartbeats 1200000 in
private theorem finite_witness_difference_bound (τ : ℝ) (hτ : 0 < τ)
    (d e : FiniteParabolicWitness T τ) :
    ‖d.value-e.value‖^2 ≤
      40*((1+τ)*‖circleParabolicPrincipalRHS T τ d.value-
          circleParabolicPrincipalRHS T τ e.value‖^2+
        (1+τ⁻¹)*‖circleParabolicInitialValue T τ d.value-
          circleParabolicInitialValue T τ e.value‖^2) := by
  let J := d.modes ∪ e.modes
  let u : J → ℝ → ℂ := fun n r =>
    finiteFourierZeroExtend d.modes J (fun i => d.coeff i r) n-
      finiteFourierZeroExtend e.modes J (fun i => e.coeff i r) n
  let v : J → ℝ → ℂ := fun n r =>
    finiteFourierZeroExtend d.modes J (fun i => d.velocityCoeff i r) n-
      finiteFourierZeroExtend e.modes J (fun i => e.velocityCoeff i r) n
  let G : J → ℝ → ℂ := fun n r =>
    finiteFourierZeroExtend d.modes J (fun i => d.forcingCoeff i r) n-
      finiteFourierZeroExtend e.modes J (fun i => e.forcingCoeff i r) n
  have hG (n : J) : Continuous (G n) := by
    by_cases hd : (n:ℤ) ∈ d.modes <;> by_cases he : (n:ℤ) ∈ e.modes
    · simpa only [G,finiteFourierZeroExtend,dif_pos hd,dif_pos he,Pi.sub_apply] using!
        (d.forcingContinuous ⟨n,hd⟩).sub (e.forcingContinuous ⟨n,he⟩)
    · simpa only [G,finiteFourierZeroExtend,dif_pos hd,dif_neg he,sub_zero] using
        d.forcingContinuous ⟨n,hd⟩
    · simpa only [G,finiteFourierZeroExtend,dif_neg hd,dif_pos he,zero_sub,Pi.neg_apply] using!
        (e.forcingContinuous ⟨n,he⟩).neg
    · simp only [G,finiteFourierZeroExtend,dif_neg hd,dif_neg he,sub_zero]
      exact continuous_const
  have hdExtend (w : FiniteParabolicWitness T τ) (n : J) (r : ℝ) :
      HasDerivAt
        (fun s => finiteFourierZeroExtend w.modes J (fun i => w.coeff i s) n)
        (τ • finiteFourierZeroExtend w.modes J (fun i => w.velocityCoeff i r) n) r := by
    by_cases hn : (n:ℤ) ∈ w.modes
    · simpa only [finiteFourierZeroExtend,dif_pos hn] using w.derivative ⟨n,hn⟩ r
    · simp only [finiteFourierZeroExtend,dif_neg hn,smul_zero]
      exact hasDerivAt_const r 0
  have hmodeExtend (w : FiniteParabolicWitness T τ) (n : J) (r : ℝ) :
      finiteFourierZeroExtend w.modes J (fun i => w.velocityCoeff i r) n+
        (1+4*‖circleFrequencyFactor T n‖^4) •
          finiteFourierZeroExtend w.modes J (fun i => w.coeff i r) n =
      finiteFourierZeroExtend w.modes J (fun i => w.forcingCoeff i r) n := by
    by_cases hn : (n:ℤ) ∈ w.modes
    · simpa only [finiteFourierZeroExtend,dif_pos hn] using w.modeEquation ⟨n,hn⟩ r
    · simp only [finiteFourierZeroExtend,dif_neg hn,smul_zero,add_zero]
  have hd (n : J) (r : ℝ) : HasDerivAt (u n) (τ • v n r) r := by
    simpa only [u,v,smul_sub,Pi.sub_apply] using! (hdExtend d n r).sub (hdExtend e n r)
  have hmode (n : J) (r : ℝ) :
      v n r+(1+4*‖circleFrequencyFactor T n‖^4) • u n r = G n r := by
    dsimp only [u,v,G]
    rw [smul_sub]
    calc
      _ = (finiteFourierZeroExtend d.modes J (fun i => d.velocityCoeff i r) n+
          (1+4*‖circleFrequencyFactor T n‖^4) •
            finiteFourierZeroExtend d.modes J (fun i => d.coeff i r) n)-
        (finiteFourierZeroExtend e.modes J (fun i => e.velocityCoeff i r) n+
          (1+4*‖circleFrequencyFactor T n‖^4) •
            finiteFourierZeroExtend e.modes J (fun i => e.coeff i r) n) := by abel
      _ = _ := by rw [hmodeExtend d n r,hmodeExtend e n r]
  have hres (n : J) (r : ℝ) :
      G n r-(1+4*‖circleFrequencyFactor T n‖^4) • u n r = v n r := by
    rw [← hmode n r,add_sub_cancel_right]
  have hcurve (t : unitInterval) : circleParabolicCurve T τ (d.value-e.value) t =
      circleSobolevFourierSynthesis T 2 J (fun n => u n (t:ℝ)) := by
    have hsub : circleParabolicCurve T τ (d.value-e.value) t =
        circleParabolicCurve T τ d.value t-circleParabolicCurve T τ e.value t := by
      simpa only [ContinuousMap.sub_apply] using!
        congrArg (fun q : C(unitInterval,CircleSobolevSpace T 2) => q t)
          ((circleParabolicCurve T τ).map_sub d.value e.value)
    exact hsub.trans ((congrArg₂ (fun x y : CircleSobolevSpace T 2 => x-y)
      (d.curve t) (e.curve t)).trans
        (circle_sobolev_fourier_synthesis_sub_common_set T 2 d.modes e.modes _ _))
  have hhigh : ∀ᵐ t : unitInterval ∂volume, circleParabolicH4 T τ (d.value-e.value) t =
      circleSobolevFourierSynthesis T 4 J (fun n => u n (t:ℝ)) := by
    have hmap : circleParabolicH4 T τ (d.value-e.value) =
        circleParabolicH4 T τ d.value-circleParabolicH4 T τ e.value := by
      simpa only using! (circleParabolicH4 T τ).map_sub d.value e.value
    filter_upwards [d.high,e.high,Lp.coeFn_sub
      (circleParabolicH4 T τ d.value) (circleParabolicH4 T τ e.value)] with t hd he hs
    have hsub : circleParabolicH4 T τ (d.value-e.value) t =
        circleParabolicH4 T τ d.value t-circleParabolicH4 T τ e.value t := by
      have hEval := congrArg (fun q : CircleTimeH4 T => q t) hmap
      exact hEval.trans (by simpa only [Pi.sub_apply] using! hs)
    exact hsub.trans ((congrArg₂ (fun x y : CircleSobolevSpace T 4 => x-y) hd he).trans
      (circle_sobolev_fourier_synthesis_sub_common_set T 4 d.modes e.modes _ _))
  have hvelocity : ∀ᵐ t : unitInterval ∂volume,
      circleParabolicTimeDerivative T τ (d.value-e.value) t =
        circleSobolevCoordinate T 4 0 (circleSobolevFourierSynthesis T 4 J
          (fun n => v n (t:ℝ))) := by
    have hmap : circleParabolicTimeDerivative T τ (d.value-e.value) =
        circleParabolicTimeDerivative T τ d.value-circleParabolicTimeDerivative T τ e.value := by
      simpa only using! (circleParabolicTimeDerivative T τ).map_sub d.value e.value
    filter_upwards [d.velocity,e.velocity,Lp.coeFn_sub
      (circleParabolicTimeDerivative T τ d.value)
      (circleParabolicTimeDerivative T τ e.value)] with t hd he hs
    have hsub : circleParabolicTimeDerivative T τ (d.value-e.value) t =
        circleParabolicTimeDerivative T τ d.value t-circleParabolicTimeDerivative T τ e.value t := by
      have hEval := congrArg (fun q : CircleTimeL2 T => q t) hmap
      exact hEval.trans (by simpa only [Pi.sub_apply] using! hs)
    have hrepr := congrArg₂ (fun x y : CircleL2 T => x-y) hd he
    have htransport := congrArg (circleSobolevCoordinate T 4 0)
      (circle_sobolev_fourier_synthesis_sub_common_set T 4 d.modes e.modes
        (fun n => d.velocityCoeff n (t:ℝ)) (fun n => e.velocityCoeff n (t:ℝ)))
    have hcoord := (circleSobolevCoordinate T 4 0).map_sub
      (circleSobolevFourierSynthesis T 4 d.modes (fun n => d.velocityCoeff n (t:ℝ)))
      (circleSobolevFourierSynthesis T 4 e.modes (fun n => e.velocityCoeff n (t:ℝ)))
    exact hsub.trans (hrepr.trans (hcoord.symm.trans htransport))
  have hforcing : circleFiniteFourierTimeForcing T J G hG =
      circleFiniteFourierTimeForcing T d.modes d.forcingCoeff d.forcingContinuous-
        circleFiniteFourierTimeForcing T e.modes e.forcingCoeff e.forcingContinuous := by
    apply Lp.ext
    filter_upwards [finite_forcing_ae T J G hG,
      finite_forcing_ae T d.modes d.forcingCoeff d.forcingContinuous,
      finite_forcing_ae T e.modes e.forcingCoeff e.forcingContinuous,
      Lp.coeFn_sub
        (circleFiniteFourierTimeForcing T d.modes d.forcingCoeff d.forcingContinuous)
        (circleFiniteFourierTimeForcing T e.modes e.forcingCoeff e.forcingContinuous)]
      with t hJ hd he hs
    have hsub : (circleFiniteFourierTimeForcing T d.modes d.forcingCoeff d.forcingContinuous-
        circleFiniteFourierTimeForcing T e.modes e.forcingCoeff e.forcingContinuous) t =
      circleFiniteFourierTimeForcing T d.modes d.forcingCoeff d.forcingContinuous t-
        circleFiniteFourierTimeForcing T e.modes e.forcingCoeff e.forcingContinuous t := by
      simpa only [Pi.sub_apply] using! hs
    have hrepr := congrArg₂ (fun x y : CircleL2 T => x-y) hd he
    have htransport := congrArg (circleSobolevCoordinate T 4 0)
      (circle_sobolev_fourier_synthesis_sub_common_set T 4 d.modes e.modes
        (fun n => d.forcingCoeff n (t:ℝ)) (fun n => e.forcingCoeff n (t:ℝ)))
    have hcoord := (circleSobolevCoordinate T 4 0).map_sub
      (circleSobolevFourierSynthesis T 4 d.modes (fun n => d.forcingCoeff n (t:ℝ)))
      (circleSobolevFourierSynthesis T 4 e.modes (fun n => e.forcingCoeff n (t:ℝ)))
    exact hJ.trans (htransport.symm.trans (hcoord.trans (hrepr.symm.trans hsub.symm)))
  have hd' := hd
  have hv' := hvelocity
  simp only [← hres] at hd' hv'
  have h := circle_finite_parabolic_estimate T τ hτ J G hG u hd'
    (d.value-e.value) hcurve hhigh hv'
  have hforceEq : circleFiniteFourierTimeForcing T J G hG =
      circleParabolicPrincipalRHS T τ d.value-circleParabolicPrincipalRHS T τ e.value :=
    hforcing.trans (congrArg₂ (fun x y : CircleTimeL2 T => x-y) d.equation.symm e.equation.symm)
  have hinitEq : circleParabolicInitialValue T τ (d.value-e.value) =
      circleParabolicInitialValue T τ d.value-circleParabolicInitialValue T τ e.value := by
    simpa only using! (circleParabolicInitialValue T τ).map_sub d.value e.value
  simpa only [hforceEq,hinitEq] using! h

set_option maxHeartbeats 2000000 in
private theorem finite_witness_of_data (τ : ℝ) (hτ : 0 < τ)
    (I : Finset ℤ) (c0 : I → ℂ) (G : I → ℝ → ℂ) (hG : ∀ n, Continuous (G n)) :
    ∃ d : FiniteParabolicWitness T τ,
      circleParabolicInitialValue T τ d.value = circleSobolevFourierSynthesis T 2 I c0 ∧
      circleParabolicPrincipalRHS T τ d.value = circleFiniteFourierTimeForcing T I G hG := by
  obtain ⟨u,hu0,hd,hU⟩ := circle_finite_parabolic_solution T τ hτ I c0 G hG
  obtain ⟨U,hinit,hcurve,hhigh,hvelocity,hPDE⟩ := hU
  refine ⟨{
      modes := I
      coeff := u
      velocityCoeff := fun n r => G n r-(1+4*‖circleFrequencyFactor T n‖^4) • u n r
      forcingCoeff := G
      forcingContinuous := hG
      derivative := hd
      modeEquation := fun n r => sub_add_cancel _ _
      value := U
      curve := hcurve
      high := hhigh
      velocity := hvelocity
      equation := hPDE },hinit,?_⟩
  exact hPDE

private theorem transfer_approximation {D X Y : Type*}
    (i : D → X) (j : D → Y) (P : X → Y → Prop) (x : X) (y : Y)
    (h : ∃ d : D, i d = x ∧ j d = y) (hp : P x y) :
    ∃ d : D, P (i d) (j d) := by
  obtain ⟨d,hi,hj⟩ := h
  exact ⟨d,hi.symm ▸ hj.symm ▸ hp⟩

set_option maxHeartbeats 300000 in
private theorem finite_witness_of_approximation (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) (ε : ℝ)
    (hData : ∃ I : Finset ℤ, ∃ c0 : I → ℂ, ∃ G : I → ℝ → ℂ,
      ∃ hG : ∀ n, Continuous (G n),
        max ‖circleSobolevFourierSynthesis T 2 I c0-u0‖
          ‖circleFiniteFourierTimeForcing T I G hG-F‖ < ε) :
    ∃ d : FiniteParabolicWitness T τ,
      max ‖circleParabolicInitialValue T τ d.value-u0‖
        ‖circleParabolicPrincipalRHS T τ d.value-F‖ < ε := by
  obtain ⟨I,c0,G,hG,happrox⟩ := hData
  exact transfer_approximation
    (fun d : FiniteParabolicWitness T τ => circleParabolicInitialValue T τ d.value)
    (fun d : FiniteParabolicWitness T τ => circleParabolicPrincipalRHS T τ d.value)
    (fun x y => max ‖x-u0‖ ‖y-F‖ < ε)
    (circleSobolevFourierSynthesis T 2 I c0) (circleFiniteFourierTimeForcing T I G hG)
    (finite_witness_of_data T τ hτ I c0 G hG) happrox

set_option maxHeartbeats 1000000 in
private theorem finite_witness_approximation (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : FiniteParabolicWitness T τ,
      max ‖circleParabolicInitialValue T τ d.value-u0‖
        ‖circleParabolicPrincipalRHS T τ d.value-F‖ < ε := by
  apply finite_witness_of_approximation T τ hτ u0 F ε
  simpa only using! (circle_parabolic_finite_data_approximation T u0 F ε hε)

private theorem weighted_dense_solution
    {E F G D : Type*}
    [NormedAddCommGroup E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (J : E → F × G) (hJ : Continuous J) (v : D → E)
    (hdense : ∀ x : F × G, ∀ ε : ℝ, 0 < ε → ∃ d : D, ‖J (v d)-x‖ < ε)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ d : D, ‖v d‖^2 ≤ 40*(a*‖(J (v d)).2‖^2+b*‖(J (v d)).1‖^2))
    (hdiff : ∀ d e : D, ‖v d-v e‖^2 ≤
      40*(a*‖(J (v d)).2-(J (v e)).2‖^2+b*‖(J (v d)).1-(J (v e)).1‖^2))
    (x : F × G) :
    ∃ U : E, J U = x ∧ ‖U‖^2 ≤ 40*(a*‖x.2‖^2+b*‖x.1‖^2) := by
  let A : ℝ := Real.sqrt (40*(a+b))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A^2 = 40*(a+b) := Real.sq_sqrt (by positivity)
  have hLip (d e : D) : ‖v d-v e‖ ≤ A*‖J (v d)-J (v e)‖ := by
    let x : F × G := J (v d)
    let y : F × G := J (v e)
    have hi : ‖x.1-y.1‖ ≤ ‖x-y‖ := by
      simpa only [Prod.fst_sub] using norm_fst_le (x-y)
    have hf : ‖x.2-y.2‖ ≤ ‖x-y‖ := by
      simpa only [Prod.snd_sub] using norm_snd_le (x-y)
    have hi2 : ‖x.1-y.1‖^2 ≤ ‖x-y‖^2 :=
      (sq_le_sq₀ (norm_nonneg (x.1-y.1)) (norm_nonneg (x-y))).mpr hi
    have hf2 : ‖x.2-y.2‖^2 ≤ ‖x-y‖^2 :=
      (sq_le_sq₀ (norm_nonneg (x.2-y.2)) (norm_nonneg (x-y))).mpr hf
    have hs : ‖v d-v e‖^2 ≤ (A*‖x-y‖)^2 := by
      calc
        ‖v d-v e‖^2 ≤ 40*(a*‖x.2-y.2‖^2+b*‖x.1-y.1‖^2) := hdiff d e
        _ ≤ 40*(a*‖x-y‖^2+b*‖x-y‖^2) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_left hf2 ha)
              (mul_le_mul_of_nonneg_left hi2 hb)) (by norm_num : (0:ℝ) ≤ 40)
        _ = (A*‖x-y‖)^2 := by rw [mul_pow,hAsq]; ring
    exact (sq_le_sq₀ (norm_nonneg (v d-v e))
      (mul_nonneg hA (norm_nonneg (x-y)))).mp hs
  have hcontinuous : Continuous
      (fun y : F × G => 40*(a*‖y.2‖^2+b*‖y.1‖^2)) := by fun_prop
  exact banach_dense_solvability J hJ v hdense A hA hLip
    (fun y : F × G => 40*(a*‖y.2‖^2+b*‖y.1‖^2)) hcontinuous hbound x

private def parabolicSolvabilityData (τ : ℝ) :
    CircleParabolicSpace T τ →L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T) :=
  (circleParabolicInitialValue T τ).prod (circleParabolicPrincipalRHS T τ)

set_option maxHeartbeats 600000 in
private theorem finite_witness_data_dense (τ : ℝ) (hτ : 0 < τ)
    (x : CircleSobolevSpace T 2 × CircleTimeL2 T) (ε : ℝ) (hε : 0 < ε) :
    ∃ d : FiniteParabolicWitness T τ, ‖parabolicSolvabilityData T τ d.value-x‖ < ε := by
  obtain ⟨d,hd⟩ := finite_witness_approximation T τ hτ x.1 x.2 ε hε
  refine ⟨d,?_⟩
  simpa only [parabolicSolvabilityData, ContinuousLinearMap.prod_apply,
    Prod.norm_def, Prod.fst_sub, Prod.snd_sub] using! hd

set_option maxHeartbeats 600000 in
/-- Actual maximal-L2 existence for the principal fourth-order equation,
with the same finite-mode square-norm estimate. -/
theorem circle_parabolic_principal_solvability (τ : ℝ) (hτ : 0 < τ)
    (u0 : CircleSobolevSpace T 2) (F : CircleTimeL2 T) :
    ∃ U : CircleParabolicSpace T τ,
      circleParabolicInitialValue T τ U = u0 ∧
      circleParabolicPrincipalRHS T τ U = F ∧
      ‖U‖^2 ≤ 40*((1+τ)*‖F‖^2+(1+τ⁻¹)*‖u0‖^2) := by
  have hs : ∃ U : CircleParabolicSpace T τ,
      parabolicSolvabilityData T τ U = (u0,F) ∧
      ‖U‖^2 ≤ 40*((1+τ)*‖F‖^2+(1+τ⁻¹)*‖u0‖^2) := by
    simpa only using! (weighted_dense_solution
      (E := CircleParabolicSpace T τ) (F := CircleSobolevSpace T 2)
      (G := CircleTimeL2 T) (D := FiniteParabolicWitness T τ)
      (parabolicSolvabilityData T τ) (parabolicSolvabilityData T τ).continuous
      (fun d : FiniteParabolicWitness T τ => d.value)
      (finite_witness_data_dense T τ hτ)
      (1+τ) (1+τ⁻¹) (by positivity) (by positivity)
      (finite_witness_bound T τ hτ) (finite_witness_difference_bound T τ hτ) (u0,F))
  obtain ⟨U,hdata,hbound⟩ := hs
  have hi : circleParabolicInitialValue T τ U = u0 :=
    congrArg (fun z : CircleSobolevSpace T 2 × CircleTimeL2 T => z.1) hdata
  have hf : circleParabolicPrincipalRHS T τ U = F :=
    congrArg (fun z : CircleSobolevSpace T 2 × CircleTimeL2 T => z.2) hdata
  exact ⟨U,hi,hf,hbound⟩

end Lemniscate
