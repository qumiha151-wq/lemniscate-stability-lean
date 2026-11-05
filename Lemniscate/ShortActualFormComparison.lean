import Lemniscate.ShortActualFormIdentity
import Lemniscate.ShortActualNeutralBounds
import Lemniscate.ShortActualEvenVectors
import Lemniscate.ShortAdjointVectorBounds
import Lemniscate.ShortAnchorNorm
import Lemniscate.ShortPeriodicFormBounds
import Lemniscate.ShortFormComparison
import Lemniscate.ShortActualHouseholderNorm

/-! The new residual and vector certificates control the actual differential
forms on the even Fourier domain.  No old adjoint trial is used. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

private theorem short_symmetrized_difference (x x₇ y y₇ : ℂ) (c : ℝ)
    (hx : ‖x-x₇‖ ≤ c) (hy : ‖y-y₇‖ ≤ c) :
    ‖(1/2:ℂ)*(x+conj y)-(1/2:ℂ)*(x₇+conj y₇)‖ ≤ c := by
  rw [show (1/2:ℂ)*(x+conj y)-(1/2:ℂ)*(x₇+conj y₇) =
    (1/2:ℂ)*((x-x₇)+conj (y-y₇)) by rw [map_sub]; ring]
  rw [norm_mul]
  have ht := norm_add_le (x-x₇) (conj (y-y₇))
  rw [norm_conj] at ht
  norm_num only [norm_div,norm_one,norm_ofNat]
  linarith only [ht,hx,hy]

theorem short_actual_component_form_errors
    (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0) :
    ∀ (j : Fin 4) (f g : circleH4Domain T),
      f ∈ shortEvenDomain T → g ∈ shortEvenDomain T →
      ‖circleExactSymmetricCoefficient T q p hq hp ψ j.castSucc f g-
        circleShortSymmetricCoefficient T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) j.castSucc f g‖ ≤
        shortAdjointComponentError j*shortVNorm T f*shortVNorm T g := by
  have hψsector := paper_single_period_adjoint_vector_sector T q p hq hp he hqreal hpreal
    hs hc ho hr ψ hψnorm hψzero
  have hmem := short_actual_neutral_vectors_mem_even T q p hq hp ho ψ hψsector
  have hmem7 := short_neutral_vectors_mem_even T
  let e : shortEvenDomain T := ⟨circleShortRotationVector T q p hq hp,hmem.1⟩
  let e₇ : shortEvenDomain T := ⟨circleShortRotationApproximation T,hmem7.1⟩
  let φ : shortEvenDomain T := ⟨circleShortAdjointVector T ψ,hmem.2⟩
  let φ₇ : shortEvenDomain T := ⟨circleShortAdjointApproximation T,hmem7.2.1⟩
  let a : shortEvenDomain T := ⟨circleHouseholderAnchorH4 T,hmem7.2.2⟩
  let V := shortEvenVSeminorm T
  let W := shortEvenH1Seminorm T
  let U := neutralHouseholder e a
  let U₇ := neutralHouseholder e₇ a
  let R := fun x => shortRightInput e φ (U x)
  let L := fun x => shortLeftInput e φ (U x)
  let Rm := fun x => shortRightInput e φ₇ (U x)
  let Lm := fun x => shortLeftInput e φ₇ (U x)
  let R₇ := fun x => shortRightInput e₇ φ₇ (U₇ x)
  let L₇ := fun x => shortLeftInput e₇ φ₇ (U₇ x)
  have hfinite := short_actual_finite_vector_bounds T
  have hrot := short_actual_rotation_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
  have hφ := short_actual_adjoint_approximation_error T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hψsector
  have hvec := short_actual_adjoint_vector_bounds T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hψsector
  have hhouse := short_actual_householder_operator_bounds T q p hq hp he hqreal hpreal hs hc ho hr
  have hsym7 := short_finite_householder_symmetries T
  have he₀ : ‖e‖ ≤ 1 := by
    have hn := short_positive_rotation_norm T q p hq hp he hqreal hpreal hs hc ho hr
    change ‖(-I) • circleUnitRotation T q p‖ ≤ 1
    simpa only [norm_smul,norm_neg,Complex.norm_I,one_mul] using! hn.le
  have he₇₀ : ‖e₇‖ ≤ 1 := by simpa only [short_even_norm] using! hfinite.1.le
  have ha₀ : ‖a‖ ≤ 1 := by
    rw [short_even_norm]
    change ‖circleHouseholderAnchor T‖ ≤ 1
    have h := (circle_even_sine_orthonormal T).norm_eq_one 0
    rw [← circle_householder_anchor_h4_coe,short_anchor_eq_I_sine]
    change ‖I • (circleSineH4 T 0:CircleL2 T)‖ ≤ 1
    simpa only [norm_smul,Complex.norm_I,one_mul] using! h.le
  have hdom (x : shortEvenDomain T) : ‖x‖ ≤ V x := (short_v_controls T (x:circleH4Domain T)).1
  have hWV (x : shortEvenDomain T) : W x ≤ V x := short_even_h1_le_v T _ x.property
  have hV₀ (x : shortEvenDomain T) : V (U x) ≤ (3/2:ℝ)*V x := by
    change shortVNorm T ((U x:shortEvenDomain T):circleH4Domain T) ≤ _
    rw [short_even_householder_coe]
    exact (hhouse.2.2 (x:circleH4Domain T)).1
  have hV₇ (x : shortEvenDomain T) : V (U₇ x) ≤ (3/2:ℝ)*V x := by
    change shortVNorm T ((U₇ x:shortEvenDomain T):circleH4Domain T) ≤ _
    rw [short_even_householder_coe]
    exact (hhouse.2.2 (x:circleH4Domain T)).2.2.1
  have hW₀ (x : shortEvenDomain T) : W (U x) ≤ (6/5:ℝ)*W x := by
    change shortH1Norm T ((U x:shortEvenDomain T):circleH4Domain T) ≤ _
    rw [short_even_householder_coe]
    exact (hhouse.2.2 (x:circleH4Domain T)).2.1
  have hW₇ (x : shortEvenDomain T) : W (U₇ x) ≤ (6/5:ℝ)*W x := by
    change shortH1Norm T ((U₇ x:shortEvenDomain T):circleH4Domain T) ≤ _
    rw [short_even_householder_coe]
    exact (hhouse.2.2 (x:circleH4Domain T)).2.2.2
  have hU₀ (x : shortEvenDomain T) : ‖U x‖ ≤ V x := by
    rw [short_even_norm,short_even_householder_coe]
    change ‖(circleRotationHouseholderH4 T q p hq hp (x:circleH4Domain T):CircleL2 T)‖ ≤ _
    rw [circle_rotation_householder_h4_coe,
      paper_householder_norm T q p hq hp he hqreal hpreal hs hc ho hr]
    exact hdom x
  have hU₇₀ (x : shortEvenDomain T) : ‖U₇ x‖ ≤ V x := by
    rw [short_even_norm,short_even_householder_coe,neutral_householder_domain_coe]
    change ‖neutralHouseholder (circleShortRotationApproximation T:CircleL2 T)
      (circleHouseholderAnchor T) ((x:circleH4Domain T):CircleL2 T)‖ ≤ V x
    rw [hsym7.2.1]
    exact hdom x
  have hd : (19/10:ℝ) ≤ ‖1+inner ℂ e a‖ :=
    hhouse.1.trans (Complex.re_le_norm _)
  have hd₇ : (19/10:ℝ) ≤ ‖1+inner ℂ e₇ a‖ :=
    hhouse.2.1.trans (Complex.re_le_norm _)
  have htelescope := short_neutral_telescope_bounds V W e e₇ φ φ₇ a
    shortKernelError shortAdjointError (by norm_num [shortKernelError])
    (by norm_num [shortAdjointError]) hdom hWV he₀ he₇₀ ha₀ hvec.1 hfinite.2.2.1.le
    (by simpa only [short_even_v_apply] using! (short_anchor_norms T).1.le)
    (short_anchor_norms T).2.2 hvec.2.2 hfinite.2.2.2.2.2.1.le hfinite.2.2.2.2.2.2.le
    hrot.1.le hrot.2.1.le hrot.2.2.le hφ.1.le hφ.2.le (by norm_num [shortKernelError])
    hd hd₇ hU₀ hU₇₀ hV₀ hV₇ hW₀ hW₇
  let B₀ (x y : shortEvenDomain T) := inner ℂ ((y:circleH4Domain T):CircleL2 T)
    (circleH4SymmetricOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      (x:circleH4Domain T))
  have hzero (x y : shortEvenDomain T) :
      ‖B₀ (U x) (U y)-B₀ (U₇ x) (U₇ y)‖ ≤
        198*shortKernelError*V x*V y := by
    apply short_symmetric_form_comparison V B₀
      (by intros; simp only [B₀,Submodule.coe_sub,map_sub,inner_sub_right])
      (by intros; simp only [B₀,Submodule.coe_sub,inner_sub_left])
      (fun x y => short_periodic_symmetric_form_bound T q p hq he hqreal hpreal hr
        (x:circleH4Domain T) (y:circleH4Domain T) x.property y.property)
      U U₇ shortKernelError (by norm_num [shortKernelError]) hV₀ hV₇
      (fun x => (htelescope x).1)
  have hpositive (k : Fin 3) (x y : shortEvenDomain T) :
      ‖inner ℂ ((L y:shortEvenDomain T):CircleL2 T)
          (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
            k.succ.castSucc (R x:circleH4Domain T))-
        inner ℂ ((L₇ y:shortEvenDomain T):CircleL2 T)
          (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
            k.succ.castSucc (R₇ x:circleH4Domain T))‖ ≤
        (![70,45,5] k:ℝ)*((7/3:ℝ)*shortKernelError+4*shortAdjointError)*V x*V y := by
    let B (v w : shortEvenDomain T) := inner ℂ ((w:circleH4Domain T):CircleL2 T)
      (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        k.succ.castSucc (v:circleH4Domain T))
    have hB (v w : shortEvenDomain T) : ‖B v w‖ ≤ (![70,45,5] k:ℝ)*V v*W w := by
      have h := short_periodic_positive_form_bounds T q p he hqreal hpreal hr
        (v:circleH4Domain T) (w:circleH4Domain T) v.property
      fin_cases k
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    exact short_positive_form_comparison V W B _ (by fin_cases k <;> norm_num)
      (by intros; simp only [B,Submodule.coe_sub,map_sub,inner_sub_right])
      (by intros; simp only [B,Submodule.coe_sub,inner_sub_left]) hB
      R L Rm Lm R₇ L₇ shortKernelError shortAdjointError
      (by norm_num [shortKernelError]) (by norm_num [shortAdjointError])
      (fun x => (htelescope x).2.1) (fun x => (htelescope x).2.2.1)
      (fun x => (htelescope x).2.2.2.1) (fun x => (htelescope x).2.2.2.2.1)
      (fun x => (htelescope x).2.2.2.2.2.1) (fun x => (htelescope x).2.2.2.2.2.2.1)
      (fun x => (htelescope x).2.2.2.2.2.2.2.1)
      (fun x => (htelescope x).2.2.2.2.2.2.2.2) x y
  intro j f g hf hg
  let F : shortEvenDomain T := ⟨f,hf⟩
  let G : shortEvenDomain T := ⟨g,hg⟩
  have hidU (x : shortEvenDomain T) : (U x:circleH4Domain T) =
      circleRotationHouseholderH4 T q p hq hp (x:circleH4Domain T) :=
    short_even_householder_coe T e a x
  have hidU₇ (x : shortEvenDomain T) : (U₇ x:circleH4Domain T) =
      circleShortHouseholderH4 T (x:circleH4Domain T) :=
    short_even_householder_coe T e₇ a x
  have hexact (k : Fin 5) (x y : shortEvenDomain T) :
      inner ℂ ((x:circleH4Domain T):CircleL2 T)
        (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) k (y:circleH4Domain T)) =
      inner ℂ ((L x:shortEvenDomain T):CircleL2 T)
        (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) k
          (R y:circleH4Domain T)) := by
    have h := short_exact_positive_pairing T q p hq hp he hqreal hpreal hs hc ho hr ψ k
      (x:circleH4Domain T) (y:circleH4Domain T)
    change _ = inner ℂ (shortLeftInput (e:circleH4Domain T) (φ:circleH4Domain T)
      (U x:circleH4Domain T):CircleL2 T)
      (circleBlochCoefficient T _ _ _ k
        (shortRightInput (e:circleH4Domain T) (φ:circleH4Domain T) (U y:circleH4Domain T)))
    rw [hidU,hidU]
    exact h
  have hfinitepair (k : Fin 5) (x y : shortEvenDomain T) :
      inner ℂ ((x:circleH4Domain T):CircleL2 T)
        (circleShortTransformedCoefficient T (q^2) ((2:ℂ) • (q*p))
          (1-(3:ℂ) • (q^4)) k (y:circleH4Domain T)) =
      inner ℂ ((L₇ x:shortEvenDomain T):CircleL2 T)
        (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) k
          (R₇ y:circleH4Domain T)) := by
    have h := short_finite_positive_pairing T (q^2) ((2:ℂ) • (q*p))
      (1-(3:ℂ) • (q^4)) hsym7.1 k
      (x:circleH4Domain T) (y:circleH4Domain T)
    change _ = inner ℂ (shortLeftInput (e₇:circleH4Domain T) (φ₇:circleH4Domain T)
      (U₇ x:circleH4Domain T):CircleL2 T)
      (circleBlochCoefficient T _ _ _ k
        (shortRightInput (e₇:circleH4Domain T) (φ₇:circleH4Domain T) (U₇ y:circleH4Domain T)))
    rw [hidU₇,hidU₇]
    exact h
  have hexactrev (k : Fin 5) (x y : shortEvenDomain T) :
      inner ℂ (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) k
        (x:circleH4Domain T)) ((y:circleH4Domain T):CircleL2 T) =
      conj (inner ℂ ((L y:shortEvenDomain T):CircleL2 T)
        (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) k
          (R x:circleH4Domain T))) := by
    calc
      _ = conj (inner ℂ ((y:circleH4Domain T):CircleL2 T)
          (circleCenteredBlochCoefficient T q p hq hp (ψ:CircleL2 T) k
            (x:circleH4Domain T))) := (inner_conj_symm _ _).symm
      _ = _ := congrArg conj (hexact k y x)
  have hfiniterev (k : Fin 5) (x y : shortEvenDomain T) :
      inner ℂ (circleShortTransformedCoefficient T (q^2) ((2:ℂ) • (q*p))
        (1-(3:ℂ) • (q^4)) k (x:circleH4Domain T)) ((y:circleH4Domain T):CircleL2 T) =
      conj (inner ℂ ((L₇ y:shortEvenDomain T):CircleL2 T)
        (circleBlochCoefficient T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) k
          (R₇ x:circleH4Domain T))) := by
    calc
      _ = conj (inner ℂ ((y:circleH4Domain T):CircleL2 T)
          (circleShortTransformedCoefficient T (q^2) ((2:ℂ) • (q*p))
            (1-(3:ℂ) • (q^4)) k (x:circleH4Domain T))) := (inner_conj_symm _ _).symm
      _ = _ := congrArg conj (hfinitepair k y x)
  cases j using Fin.cases with
  | zero =>
    change ‖inner ℂ (circleRotationHouseholderH4 T q p hq hp f:CircleL2 T)
      (circleH4SymmetricOperator T _ _ _ (circleRotationHouseholderH4 T q p hq hp g))-
        inner ℂ (circleShortHouseholderH4 T f:CircleL2 T)
          (circleH4SymmetricOperator T _ _ _ (circleShortHouseholderH4 T g))‖ ≤
      198*shortKernelError*shortVNorm T f*shortVNorm T g
    simpa only [V,F,G,B₀,hidU,hidU₇,short_even_v_apply,mul_comm,mul_left_comm,mul_assoc]
      using! hzero G F
  | succ k =>
    have hfg := hpositive k G F
    have hgf := hpositive k F G
    have hk0 : k.succ.castSucc ≠ (0:Fin 5) := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_zero] at hval
      omega
    rw [circleExactSymmetricCoefficient,circleShortSymmetricCoefficient,
      if_neg hk0,if_neg hk0]
    rw [show f = (F:circleH4Domain T) from rfl,show g = (G:circleH4Domain T) from rfl]
    rw [hexact,hfinitepair,hexactrev,hfiniterev]
    have hc : shortAdjointComponentError k.succ =
        (![70,45,5] k:ℝ)*((7/3:ℝ)*shortKernelError+4*shortAdjointError) := by
      fin_cases k <;> rfl
    change _ ≤ shortAdjointComponentError k.succ*V F*V G
    apply short_symmetrized_difference
    · rw [hc]
      convert hfg using 1 <;> ring
    · rw [hc]
      exact hgf

end Lemniscate
