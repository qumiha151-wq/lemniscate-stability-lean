import Lemniscate.ShortPolynomialNorm
import Lemniscate.PeriodicSobolevFourierProjection
import Lemniscate.PeriodicSobolevH4Jet

/-! Transfer the finite-polynomial exact Bernstein estimate to every even
H4 function.  Continuity uses all five actual L2 derivative coordinates,
not the inherited L2 topology on the unbounded operator domain. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped ComplexConjugate Topology
variable (T : ℝ) [Fact (0 < T)]

private def JetContinuous {X : Type*} [TopologicalSpace X]
    (F : X → circleH4Domain T) : Prop :=
  Continuous (fun x => (F x : CircleL2 T)) ∧
    ∀ k : Fin 4, Continuous (fun x => circleH4Derivative T k (F x))

private theorem jet_const {X : Type*} [TopologicalSpace X] (f : circleH4Domain T) :
    JetContinuous T (fun _ : X => f) :=
  ⟨continuous_const,fun _ => continuous_const⟩

private theorem jet_sub {X : Type*} [TopologicalSpace X]
    {F G : X → circleH4Domain T} (hF : JetContinuous T F) (hG : JetContinuous T G) :
    JetContinuous T (fun x => F x-G x) := by
  constructor
  · simpa only [Submodule.coe_sub, Pi.sub_apply] using! hF.1.sub hG.1
  · intro k
    simpa only [map_sub, Pi.sub_apply] using! (hF.2 k).sub (hG.2 k)

private theorem jet_smul {X : Type*} [TopologicalSpace X]
    {c : X → ℂ} {F : X → circleH4Domain T}
    (hc : Continuous c) (hF : JetContinuous T F) :
    JetContinuous T (fun x => c x • F x) := by
  constructor
  · simpa only [Submodule.coe_smul_of_tower, Pi.smul_apply] using! hc.smul hF.1
  · intro k
    simpa only [map_smul, RingHom.id_apply, Pi.smul_apply] using! hc.smul (hF.2 k)

private theorem jet_householder {X : Type*} [TopologicalSpace X]
    (e a : circleH4Domain T) {F : X → circleH4Domain T} (hF : JetContinuous T F) :
    JetContinuous T (fun x => neutralHouseholderDomain e a (F x)) := by
  have hc : Continuous (fun x => (1+inner ℂ (e : CircleL2 T) (a : CircleL2 T))⁻¹*
      inner ℂ ((e : CircleL2 T)+(a : CircleL2 T)) (F x : CircleL2 T)) :=
    continuous_const.mul (continuous_const.inner hF.1)
  exact jet_sub T hF (jet_smul T hc (jet_const T (e+a)))

private theorem jet_neutral_inverse {X : Type*} [TopologicalSpace X]
    (e : circleH4Domain T) (ψ : CircleL2 T)
    {F : X → circleH4Domain T} (hF : JetContinuous T F) :
    JetContinuous T (fun x => neutralTransformInvDomain e ψ (F x)) :=
  jet_sub T hF (jet_smul T (continuous_const.inner hF.1) (jet_const T e))

private theorem jet_fixed_projection {X : Type*} [TopologicalSpace X]
    {F : X → circleH4Domain T} (hF : JetContinuous T F) :
    JetContinuous T (fun x => circleFixedProjectionH4 T (F x)) :=
  jet_smul T (continuous_const.inner hF.1) (jet_const T (circleHouseholderAnchorH4 T))

private theorem symmetric_continuous {X : Type*} [TopologicalSpace X]
    (h h₁ h₂ : C(AddCircle T, ℂ)) {F : X → circleH4Domain T}
    (hF : JetContinuous T F) :
    Continuous (fun x => circleH4SymmetricOperator T h h₁ h₂ (F x)) := by
  have h0 := hF.1
  have h1 := hF.2 0
  have h2 := hF.2 1
  have h4 := hF.2 3
  simp only [circleH4SymmetricOperator,LinearMap.sub_apply,LinearMap.add_apply,
    LinearMap.smul_apply,LinearMap.comp_apply,ContinuousLinearMap.coe_coe,
    Submodule.subtype_apply]
  fun_prop

private theorem operator_continuous {X : Type*} [TopologicalSpace X]
    (h h₁ h₂ : C(AddCircle T, ℂ)) {F : X → circleH4Domain T}
    (hF : JetContinuous T F) :
    Continuous (fun x => circleH4Operator T h h₁ h₂ (F x)) := by
  have h0 := hF.1
  have h1 := hF.2 0
  have hs := symmetric_continuous T h h₁ h₂ hF
  simp only [circleH4Operator,LinearMap.add_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,ContinuousLinearMap.coe_coe,Submodule.subtype_apply]
  fun_prop

private theorem bloch_continuous {X : Type*} [TopologicalSpace X]
    (h h₁ h₂ : C(AddCircle T, ℂ)) (j : Fin 5)
    {F : X → circleH4Domain T} (hF : JetContinuous T F) :
    Continuous (fun x => circleBlochCoefficient T h h₁ h₂ j (F x)) := by
  have h0 := hF.1
  have h1 := hF.2 0
  have h2 := hF.2 1
  have h3 := hF.2 2
  have hA := operator_continuous T h h₁ h₂ hF
  fin_cases j <;>
    simp only [circleBlochCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
      LinearMap.sub_apply,LinearMap.add_apply,LinearMap.smul_apply,
      LinearMap.comp_apply,ContinuousLinearMap.coe_coe,Submodule.subtype_apply] <;>
    fun_prop

private theorem centered_continuous {X : Type*} [TopologicalSpace X]
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (ψ : CircleL2 T) (j : Fin 5)
    {F : X → circleH4Domain T} (hF : JetContinuous T F) :
    Continuous (fun x => circleCenteredBlochCoefficient T q p hq hp ψ j (F x)) := by
  have hU := jet_householder T ((-I) • circleUnitRotationH4 T q p hq hp)
    (circleHouseholderAnchorH4 T) hF
  have hV := jet_neutral_inverse T (circleUnitRotationH4 T q p hq hp) ψ hU
  have hA := bloch_continuous T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j hV
  exact (circleRotationHouseholder T q p).continuous.comp
    ((neutralTransform (circleUnitRotationH4 T q p hq hp) ψ).continuous.comp hA)

private theorem exact_symmetric_continuous {X : Type*} [TopologicalSpace X]
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (ψ : circleH4Domain T) (j : Fin 5)
    {F G : X → circleH4Domain T} (hF : JetContinuous T F) (hG : JetContinuous T G) :
    Continuous (fun x => circleExactSymmetricCoefficient T q p hq hp ψ j (F x) (G x)) := by
  by_cases hj : j=0
  · simp only [circleExactSymmetricCoefficient,if_pos hj]
    have hU := jet_householder T ((-I) • circleUnitRotationH4 T q p hq hp)
      (circleHouseholderAnchorH4 T) hF
    have hV := jet_householder T ((-I) • circleUnitRotationH4 T q p hq hp)
      (circleHouseholderAnchorH4 T) hG
    exact hU.1.inner (symmetric_continuous T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) hV)
  · simp only [circleExactSymmetricCoefficient,if_neg hj]
    exact continuous_const.mul
      ((hF.1.inner (centered_continuous T q p hq hp _ j hG)).add
        ((centered_continuous T q p hq hp _ j hF).inner hG.1))

private theorem bernstein_continuous {X : Type*} [TopologicalSpace X]
    (H : Fin 5 → circleH4Domain T → circleH4Domain T → ℂ)
    (hH : ∀ (j : Fin 5) (F G : X → circleH4Domain T),
      JetContinuous T F → JetContinuous T G → Continuous (fun x => H j (F x) (G x)))
    (j : Fin 5) {F G : X → circleH4Domain T}
    (hF : JetContinuous T F) (hG : JetContinuous T G) :
    Continuous (fun x => circleShiftedBernsteinPairing T H j (F x) (G x)) := by
  let F₀ := fun x => circleFixedProjectionH4 T (F x)
  let G₀ := fun x => circleFixedProjectionH4 T (G x)
  let F₁ := fun x => F x-F₀ x
  let G₁ := fun x => G x-G₀ x
  have hF₀ := jet_fixed_projection T hF
  have hG₀ := jet_fixed_projection T hG
  have hF₁ := jet_sub T hF hF₀
  have hG₁ := jet_sub T hG hG₀
  have h01 := hH 0 F₁ G₁ hF₁ hG₁
  have h10 := hH 1 F₀ G₁ hF₀ hG₁
  have h11 := hH 1 F₁ G₀ hF₁ hG₀
  have h12 := hH 1 F₁ G₁ hF₁ hG₁
  have h20 := hH 2 F₀ G₀ hF₀ hG₀
  have h21 := hH 2 F₀ G₁ hF₀ hG₁
  have h22 := hH 2 F₁ G₀ hF₁ hG₀
  have h23 := hH 2 F₁ G₁ hF₁ hG₁
  have h30 := hH 3 F₀ G₁ hF₀ hG₁
  have h31 := hH 3 F₁ G₀ hF₁ hG₀
  have h32 := hH 3 F₁ G₁ hF₁ hG₁
  have hr (k : Fin 5) : Continuous (fun x => circleReducedShiftedCoefficient T
      H k (F x) (G x)) := by
    have hv : Continuous (fun x => inner ℂ (F x : CircleL2 T) (G x : CircleL2 T)) :=
      hF.1.inner hG.1
    have hv0 : Continuous (fun x => inner ℂ (F₀ x : CircleL2 T) (G₀ x : CircleL2 T)) :=
      hF₀.1.inner hG₀.1
    have hv1 : Continuous (fun x => inner ℂ (F₁ x : CircleL2 T) (G₁ x : CircleL2 T)) :=
      hF₁.1.inner hG₁.1
    fin_cases k
    · simpa only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',F₀,G₀,F₁,G₁,
        Pi.add_apply,Pi.mul_apply] using!
        (((h01.add h10).add h11).add h20).add
          ((continuous_const : Continuous (fun _ : X => (1/2:ℂ))).mul hv)
    · simpa only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
        F₀,G₀,F₁,G₁,Pi.add_apply] using! (h12.add h21).add h22
    · simpa only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
        F₀,G₀,F₁,G₁,Pi.add_apply,Pi.mul_apply] using!
        ((h23.add h30).add h31).add
          ((continuous_const : Continuous (fun _ : X => ((-4*(2*Real.pi/T)^4:ℝ):ℂ))).mul hv0)
    · simpa only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
        F₀,G₀,F₁,G₁] using! h32
    · simpa only [circleReducedShiftedCoefficient,Matrix.cons_val_zero',Matrix.cons_val_succ',
        F₀,G₀,F₁,G₁,Pi.mul_apply] using!
        (continuous_const : Continuous (fun _ : X => ((-4*(2*Real.pi/T)^4:ℝ):ℂ))).mul hv1
  apply continuous_finsetSum
  intro k _
  exact continuous_const.mul (hr k)

private theorem sobolev_jet_continuous :
    JetContinuous T (circleSobolevToH4Domain T) := by
  constructor
  · exact (circleSobolevCoordinate T 4 0).continuous
  · intro k
    fin_cases k
    · change Continuous (fun x => (circleH4Jet T (circleSobolevToH4Domain T x)).first)
      simpa only [circle_sobolev_h4_jet] using! (circleSobolevCoordinate T 4 1).continuous
    · change Continuous (fun x => (circleH4Jet T (circleSobolevToH4Domain T x)).second)
      simpa only [circle_sobolev_h4_jet] using! (circleSobolevCoordinate T 4 2).continuous
    · change Continuous (fun x => (circleH4Jet T (circleSobolevToH4Domain T x)).third)
      simpa only [circle_sobolev_h4_jet] using! (circleSobolevCoordinate T 4 3).continuous
    · change Continuous (fun x => (circleH4Jet T (circleSobolevToH4Domain T x)).fourth)
      simpa only [circle_sobolev_h4_jet] using! (circleSobolevCoordinate T 4 4).continuous

/-- An exact Bernstein estimate checked on all finite even Fourier
polynomials holds on the complete actual even H4 domain. -/
theorem short_exact_bernstein_nonpositive_of_polynomials
    (q p : C(AddCircle T, ℂ)) (hq : HasCircleDeriv T q p)
    (hp : HasCircleDeriv T p (-(q^3))) (ψ : circleH4Domain T) (j : Fin 5)
    (hpoly : ∀ (I : Finset ℤ) (a : ℤ → ℂ),
      (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j
        (∑ n∈I,a n • circleFourierH4 T (2*n))
        (∑ n∈I,a n • circleFourierH4 T (2*n))).re ≤ 0)
    (f : circleH4Domain T) (hf : ∀ n : ℤ, Odd n → fourierCoeff (f : CircleL2 T) n=0) :
    (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j f f).re ≤ 0 := by
  obtain ⟨u,hu⟩ := (circle_sobolev_four_range T (f : CircleL2 T)).mpr f.property
  have huf : circleSobolevToH4Domain T u=f := Subtype.ext hu
  let F := fun I : Finset ℤ => circleSobolevToH4Domain T (circleSobolevFourierProjection T 4 I u)
  let B : circleH4Domain T → ℝ := fun v =>
    (circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j v v).re
  have hlimit : Tendsto (fun I : Finset ℤ => B (F I)) atTop (𝓝 (B f)) := by
    have hc : Continuous (fun v : CircleSobolevSpace T 4 => B (circleSobolevToH4Domain T v)) :=
      Complex.continuous_re.comp (bernstein_continuous T
        (circleExactSymmetricCoefficient T q p hq hp ψ)
        (fun j F G hF hG => exact_symmetric_continuous T q p hq hp ψ j hF hG) j
        (sobolev_jet_continuous T) (sobolev_jet_continuous T))
    have ht := hc.continuousAt.tendsto.comp (circle_sobolev_fourier_projection_tendsto T 4 u)
    have heq : B (circleSobolevToH4Domain T u) = B f := congrArg B huf
    exact heq ▸ ht
  change B f ≤ 0
  apply le_of_tendsto hlimit
  apply Filter.Eventually.of_forall
  intro I
  let J := I.preimage (fun n : ℤ => 2*n)
    (mul_right_injective₀ (by norm_num : (2:ℤ) ≠ 0)).injOn
  have hshape : F I = ∑ n∈J,fourierCoeff (f : CircleL2 T) (2*n) • circleFourierH4 T (2*n) := by
    apply Subtype.ext
    have hvalue : (F I : CircleL2 T)=circleFourierProjection T I (f : CircleL2 T) := by
      change circleFourierProjection T I (circleSobolevCoordinate T 4 0 u)=_
      rw [hu]
    rw [hvalue]
    apply circle_fourier_ext T
    intro k
    rw [circle_fourier_projection_fourier]
    by_cases hk : Odd k
    · rw [hf k hk,circle_short_polynomial_even T J _ k hk]
      split_ifs <;> rfl
    · have heven : Even k := (Int.even_or_odd k).resolve_right hk
      rcases heven with ⟨n,hn⟩
      have hk2 : k=2*n := by omega
      rw [hk2,circle_short_polynomial_fourier_at]
      simp only [J,Finset.mem_preimage]
  rw [hshape]
  exact hpoly J _

end Lemniscate
