import Lemniscate.NormalGraphProjection
import Lemniscate.NormalGraphCurvatureEstimate
import Lemniscate.PeriodicIntegralComposition
import Lemniscate.BernoulliCircleProfile
import Lemniscate.PeriodicSobolevConjugation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-! The normal projection gives an actual periodic H2 height. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Set
open scoped ContDiff ComplexConjugate

private theorem periodic_deriv_entry {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (T : ℝ) (hp : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro s
  have heq : (fun u => f (u+T)) = f := funext hp
  have hd := congrArg (fun F => deriv F s) heq
  simpa only [deriv_comp_add_const] using hd

private theorem reference_curvature_periodic
    (β t : ℝ → ℂ) (k : ℝ → ℝ) (T : ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t (I*(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖ = 1) (hp : Function.Periodic β T) :
    Function.Periodic k T := by
  have hdt : deriv β = t := funext fun s => (hβ s).deriv
  have htp : Function.Periodic t T := by
    rw [← hdt]
    exact periodic_deriv_entry β T hp
  have htdp := periodic_deriv_entry t T htp
  intro s
  have heq : I*(k (s+T):ℂ)*t s = I*(k s:ℂ)*t s := by
    simpa only [(ht (s+T)).deriv,(ht s).deriv,htp s] using htdp s
  have htne : t s ≠ 0 := by
    intro hz
    have hn := hu s
    rw [hz,norm_zero] at hn
    norm_num at hn
  have hc : (k (s+T):ℂ) = (k s:ℂ) :=
    mul_left_cancel₀ Complex.I_ne_zero (mul_right_cancel₀ htne heq)
  exact Complex.ofReal_injective hc

private abbrev realPeriodicCircle (T : ℝ) (f : ℝ → ℝ)
    (hp : Function.Periodic f T) (hc : Continuous f) : C(AddCircle T,ℂ) :=
  periodicCircleFunction T (fun s => (f s:ℂ))
    (fun s => congrArg Complex.ofReal (hp s)) (Complex.continuous_ofReal.comp hc)

private theorem real_periodic_circle_real (T : ℝ) (f : ℝ → ℝ)
    (hp : Function.Periodic f T) (hc : Continuous f) (x : AddCircle T) :
    conj (realPeriodicCircle T f hp hc x) = realPeriodicCircle T f hp hc x := by
  induction x using QuotientAddGroup.induction_on
  exact Complex.conj_ofReal _

private theorem real_periodic_l2_norm_sq (T : ℝ) [Fact (0<T)]
    (f : ℝ → ℝ) (hp : Function.Periodic f T) (hc : Continuous f) :
    ‖circleContinuousL2 T (realPeriodicCircle T f hp hc)‖^2 =
      T⁻¹*(∫ s in (0:ℝ)..T, (f s)^2) := by
  let F := realPeriodicCircle T f hp hc
  let v := circleContinuousL2 T F
  have hn : ‖v‖^2 = ∫ x : AddCircle T, ‖F x‖^2 ∂AddCircle.haarAddCircle := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ) v v)]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) AddCircle.haarAddCircle
      (𝕜 := ℂ) F] with x hx
    change (inner ℂ (v x) (v x)).re = ‖F x‖^2
    change v x = F x at hx
    rw [hx]
    simpa only using! (norm_sq_eq_re_inner (𝕜 := ℂ) (F x)).symm
  rw [hn,AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage T 0 (fun x : AddCircle T => ‖F x‖^2)]
  simp only [zero_add,smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change ‖(f s:ℂ)‖^2 = (f s)^2
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]

private theorem periodic_height_sobolev (T : ℝ) [Fact (0<T)]
    (h : ℝ → ℝ) (hh : ContDiff ℝ ∞ h) (hp : Function.Periodic h T) :
    ∃ H : CircleSobolevSpace T 2,
      circleSobolevConjugation T 2 H = H ∧
      circleSobolevCoordinate T 2 0 H =
        circleContinuousL2 T (realPeriodicCircle T h hp hh.continuous) ∧
      ‖H‖^2 = T⁻¹*((∫ s in (0:ℝ)..T, (h s)^2)+
        (∫ s in (0:ℝ)..T, (deriv h s)^2)+
        (∫ s in (0:ℝ)..T, (deriv (deriv h) s)^2)) := by
  have hh₁ : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hh₂ : ContDiff ℝ ∞ (deriv (deriv h)) :=
    (contDiff_infty_iff_deriv.mp hh₁).2
  have hp₁ := periodic_deriv_entry h T hp
  have hp₂ := periodic_deriv_entry (deriv h) T hp₁
  let F₀ := realPeriodicCircle T h hp hh.continuous
  let F₁ := realPeriodicCircle T (deriv h) hp₁ hh₁.continuous
  let F₂ := realPeriodicCircle T (deriv (deriv h)) hp₂ hh₂.continuous
  have hd₀ : HasCircleDeriv T F₀ F₁ := by
    intro s
    exact ((hh.differentiable (by simp) s).hasDerivAt).ofReal_comp
  have hd₁ : HasCircleDeriv T F₁ F₂ := by
    intro s
    exact ((hh₁.differentiable (by simp) s).hasDerivAt).ofReal_comp
  let J : PiLp 2 (fun _ : Fin 3 => CircleL2 T) :=
    WithLp.toLp 2 ![circleContinuousL2 T F₀,circleContinuousL2 T F₁,
      circleContinuousL2 T F₂]
  have hJ : J ∈ circleSobolevJetSubmodule T 2 := by
    apply (circle_sobolev_jet_mem_iff T 2 J).mpr
    intro j
    fin_cases j
    · exact circle_classical_weak_deriv T F₀ F₁ hd₀
    · exact circle_classical_weak_deriv T F₁ F₂ hd₁
  let H : CircleSobolevSpace T 2 := ⟨J,hJ⟩
  refine ⟨H,?_,rfl,?_⟩
  · apply circle_sobolev_value_injective T 2
    change circleConjugate T (circleContinuousL2 T F₀) = circleContinuousL2 T F₀
    exact circle_conjugate_continuous_real T F₀
      (real_periodic_circle_real T h hp hh.continuous)
  · rw [circle_sobolev_norm_sq,Fin.sum_univ_three]
    change ‖circleContinuousL2 T F₀‖^2+‖circleContinuousL2 T F₁‖^2+
      ‖circleContinuousL2 T F₂‖^2 = _
    rw [real_periodic_l2_norm_sq T h hp hh.continuous,
      real_periodic_l2_norm_sq T (deriv h) hp₁ hh₁.continuous,
      real_periodic_l2_norm_sq T (deriv (deriv h)) hp₂ hh₂.continuous]
    ring

private theorem integral_square_of_uniform_bound (T a : ℝ) (hT : 0 ≤ T)
    (f : ℝ → ℝ) (hf : Continuous f) (hbound : ∀ s, |f s| ≤ a) :
    (∫ s in (0:ℝ)..T, (f s)^2) ≤ T*a^2 := by
  calc
    _ ≤ ∫ _ in (0:ℝ)..T, a^2 := by
      apply intervalIntegral.integral_mono_on hT ((hf.pow 2).intervalIntegrable 0 T)
        (continuous_const.intervalIntegrable 0 T)
      intro s _
      exact sq_le_sq' (abs_le.mp (hbound s)).1 (abs_le.mp (hbound s)).2
    _ = _ := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]

private theorem norm_from_two_squares (n a b δ y : ℝ)
    (hn : 0 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 ≤ δ) (hy : 0 ≤ y)
    (hbound : n^2 ≤ a*δ^2+b*y^2) : n ≤ (a+b+1)*(δ+y) := by
  have hδy : 0 ≤ δ*y := mul_nonneg hδ hy
  have hδsq : δ^2 ≤ (δ+y)^2 := by nlinarith only [hδy,sq_nonneg y]
  have hysq : y^2 ≤ (δ+y)^2 := by nlinarith only [hδy,sq_nonneg δ]
  have hs : a*δ^2+b*y^2 ≤ (a+b)*(δ+y)^2 := by
    calc
      _ ≤ a*(δ+y)^2+b*(δ+y)^2 := add_le_add
        (mul_le_mul_of_nonneg_left hδsq ha) (mul_le_mul_of_nonneg_left hysq hb)
      _ = _ := by ring
  have hc : a+b ≤ (a+b+1)^2 := by nlinarith only [sq_nonneg (a+b),ha,hb]
  have hs₂ := mul_le_mul_of_nonneg_right hc (sq_nonneg (δ+y))
  have hn₂ : n^2 ≤ ((a+b+1)*(δ+y))^2 := by
    calc
      _ ≤ (a+b)*(δ+y)^2 := hbound.trans hs
      _ ≤ (a+b+1)^2*(δ+y)^2 := hs₂
      _ = _ := by ring
  exact (sq_le_sq₀ hn (by positivity)).mp hn₂

/-- A nearby periodic unit-speed curve has a real normal height in the
complete H2 space. Its norm is controlled by the projection error and
the curvature difference on one period. -/
theorem periodic_normal_graph_h2_entry
    (T : ℝ) [Fact (0<T)] (β Tβ : ℝ → ℂ) (k ks : ℝ → ℝ)
    (hβsmooth : ContDiff ℝ ∞ β) (hβper : Function.Periodic β T)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s) (huβ : ∀ s, ‖Tβ s‖ = 1)
    (K K₁ : ℝ) (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hcurvature : ∀ s, |k s| ≤ K) (hcurvatureDerivative : ∀ s, |ks s| ≤ K₁) :
    ∃ δ₀ > 0, ∃ C > 0, ∀ (γ Tγ : ℝ → ℂ) (kγ : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ ∞ γ → Function.Periodic γ T →
      (∀ s, HasDerivAt γ (Tγ s) s) →
      (∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s) →
      (∀ s, ‖Tγ s‖ = 1) → Continuous kγ → Function.Periodic kγ T →
      0 ≤ δ → δ < δ₀ → (∀ s, ‖γ s-β s‖ ≤ δ) →
      (∀ s, ‖Tγ s-Tβ s‖ ≤ δ) →
      ∃ χ h : ℝ → ℝ, ∃ hh : ContDiff ℝ ∞ h, ∃ hp : Function.Periodic h T,
        ContDiff ℝ ∞ χ ∧ Function.Periodic (fun s => χ s-s) T ∧
        (∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s ∧
          |χ s-s| ≤ 2*δ ∧ |h s| ≤ 3*δ ∧
          |deriv h s| ≤ 4*(δ+2*K*δ) ∧
          (1/4:ℝ) ≤ deriv χ s ∧ deriv χ s ≤ 4) ∧
        ∃ H : CircleSobolevSpace T 2,
          circleSobolevConjugation T 2 H = H ∧
          circleSobolevCoordinate T 2 0 H = circleContinuousL2 T
            (periodicCircleFunction T (fun s => (h s:ℂ))
              (fun s => congrArg Complex.ofReal (hp s))
              (Complex.continuous_ofReal.comp hh.continuous)) ∧
          ‖H‖ ≤ C*(δ+Real.sqrt (T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2))) := by
  have hT : 0<T := Fact.out
  obtain ⟨D,hD,hsecond⟩ := normal_graph_curvature_estimate β Tβ k ks
    hβ hTβ hk huβ K K₁ hK hK₁ hcurvature hcurvatureDerivative
  let B := 4*(1+2*K)
  let a := 9+B^2+2*D^2
  let b := 8*D^2/T^2
  let C := a+b+1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  let δ₀ := (1/4:ℝ)/(1+2*K)
  have hδ₀ : 0<δ₀ := by dsimp only [δ₀]; positivity
  refine ⟨δ₀,hδ₀,C,hC,?_⟩
  intro γ Tγ kγ δ hγsmooth hγper hγ hTγ huγ hkγ hkγper hδ hδsmall hposition htangent
  have hsmall : δ+2*K*δ < 1/2 := by
    dsimp only [δ₀] at hδsmall
    have hm : δ*(1+2*K) < 1/4 :=
      (lt_div_iff₀ (by positivity : (0:ℝ)<1+2*K)).mp hδsmall
    nlinarith only [hm]
  have hproj : ∃ χ h : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ ContDiff ℝ ∞ h ∧
      Function.Periodic (fun s => χ s-s) T ∧ Function.Periodic h T ∧
      ∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s ∧
        |χ s-s| ≤ 2*δ ∧ |h s| ≤ 3*δ ∧
        |deriv h s| ≤ 4*(δ+2*K*δ) ∧
        (1/4:ℝ) ≤ deriv χ s ∧ deriv χ s ≤ 4 := by
    by_cases hz : δ=0
    · have hγeq (s : ℝ) : γ s = β s := by
        apply sub_eq_zero.mp
        apply norm_le_zero_iff.mp
        simpa only [hz] using hposition s
      refine ⟨id,fun _ => 0,contDiff_id,contDiff_const,?_,?_,?_⟩
      · intro s; simp
      · intro s; rfl
      · intro s
        simp only [id_eq,hγeq,Complex.ofReal_zero,mul_zero,zero_mul,add_zero,
          sub_self,abs_zero,hz,deriv_const,deriv_id'',mul_zero,zero_add]
        norm_num
    · obtain ⟨χ,h,hχ,hh,hχper,hper,hd⟩ := periodic_normal_graph_projection
        γ β Tγ Tβ k T δ K hγsmooth hβsmooth hγ hβ hTβ huγ huβ
        hγper hβper (lt_of_le_of_ne hδ (Ne.symm hz)) hK hsmall hposition htangent hcurvature
      exact ⟨χ,h,hχ,hh,hχper,hper,fun s =>
        ⟨(hd s).1,(hd s).2.1,(hd s).2.2.1,(hd s).2.2.2.1,
          (hd s).2.2.2.2.2.1,(hd s).2.2.2.2.2.2⟩⟩
  obtain ⟨χ,h,hχ,hh,hχper,hper,hd⟩ := hproj
  have hh₁ : ContDiff ℝ ∞ (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hh₂ : Continuous (deriv (deriv h)) :=
    (contDiff_infty_iff_deriv.mp hh₁).2.continuous
  have hhsmall (s : ℝ) : |h s| ≤ 3*δ := (hd s).2.2.1
  have hh₁small (s : ℝ) : |deriv h s| ≤ B*δ := by
    exact ((hd s).2.2.2.1).trans_eq (by dsimp only [B]; ring)
  have hh₂small (s : ℝ) : |deriv (deriv h) s| ≤ D*(|kγ (χ s)-k (χ s)|+δ) := by
    by_cases hz : δ=0
    · have heq : h = fun _ => (0:ℝ) := by
        funext u
        have hu := hhsmall u
        rw [hz,mul_zero] at hu
        exact abs_eq_zero.mp (le_antisymm hu (abs_nonneg _))
      simpa only [heq,deriv_const',deriv_const,abs_zero] using
        (mul_nonneg hD.le (add_nonneg (abs_nonneg (kγ (χ s)-k (χ s))) hδ))
    · exact hsecond γ Tγ kγ χ h δ hγ hTγ huγ
        ((contDiff_infty.mp hχ) 2) ((contDiff_infty.mp hh) 2) (fun u => (hd u).1)
        (lt_of_le_of_ne hδ (Ne.symm hz)) hsmall hhsmall
        (fun u => (hd u).2.2.2.1) (fun u => (hd u).2.1)
        (fun u => (hd u).2.2.2.2) s
  have hkcont : Continuous k := continuous_iff_continuousAt.mpr fun s => (hk s).continuousAt
  have hkper := reference_curvature_periodic β Tβ k T hβ hTβ huβ hβper
  let f : ℝ → ℝ := fun s => kγ s-k s
  have hf : Continuous f := hkγ.sub hkcont
  have hfper : Function.Periodic f T := by intro s; simp only [f,hkγper s,hkper s]
  have hχend : χ T = χ 0+T := by
    have hp := hχper 0
    simp only [zero_add,sub_zero] at hp
    linarith
  have hcomp := periodic_integral_comp_square_le T hT f χ hf hfper
    (hχ.of_le (by simp)) hχend (fun s _ => (hd s).2.2.2.2.1)
  let I := ∫ s in (0:ℝ)..T, (f s)^2
  have hI : 0 ≤ I := intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
  have hI₀ := integral_square_of_uniform_bound T (3*δ) hT.le h hh.continuous hhsmall
  have hI₁ := integral_square_of_uniform_bound T (B*δ) hT.le
    (deriv h) hh₁.continuous hh₁small
  have hI₂ : (∫ s in (0:ℝ)..T, (deriv (deriv h) s)^2) ≤
      2*D^2*(4*I+T*δ^2) := by
    have hs (s : ℝ) : (deriv (deriv h) s)^2 ≤
        2*D^2*((f (χ s))^2+δ^2) := by
      have hd := hh₂small s
      change |deriv (deriv h) s| ≤ D*(|f (χ s)|+δ) at hd
      have hsq := sq_le_sq' (abs_le.mp hd).1 (abs_le.mp hd).2
      have hrem := mul_nonneg (sq_nonneg D) (sq_nonneg (|f (χ s)|-δ))
      nlinarith only [hsq,hrem,sq_abs (f (χ s))]
    calc
      _ ≤ ∫ s in (0:ℝ)..T, 2*D^2*((f (χ s))^2+δ^2) := by
        apply intervalIntegral.integral_mono_on hT.le ((hh₂.pow 2).intervalIntegrable 0 T)
          (((hf.comp hχ.continuous).pow 2).add continuous_const |>.const_mul (2*D^2)
            |>.intervalIntegrable 0 T)
        intro s _
        change (deriv (deriv h) s)^2 ≤ 2*D^2*((f (χ s))^2+δ^2)
        exact hs s
      _ = 2*D^2*((∫ s in (0:ℝ)..T, (f (χ s))^2)+T*δ^2) := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add (f := fun s => (f (χ s))^2)
            (g := fun _ => δ^2) (((hf.comp hχ.continuous).pow 2).intervalIntegrable 0 T)
            (continuous_const.intervalIntegrable 0 T)]
        simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hcomp le_rfl) (by positivity)
  obtain ⟨H,hHreal,hHvalue,hHnorm⟩ := periodic_height_sobolev T h hh hper
  have hsum := add_le_add (add_le_add hI₀ hI₁) hI₂
  have hHnorm₂ : ‖H‖^2 ≤ a*δ^2+b*(Real.sqrt (T*I))^2 := by
    have hi := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hT.le)
    rw [← hHnorm] at hi
    calc
      _ ≤ T⁻¹*(T*(3*δ)^2+T*(B*δ)^2+2*D^2*(4*I+T*δ^2)) := hi
      _ = _ := by
        rw [Real.sq_sqrt (mul_nonneg hT.le hI)]
        dsimp only [a,b]
        field_simp [ne_of_gt hT]
        <;> ring
  refine ⟨χ,h,hh,hper,hχ,hχper,hd,H,hHreal,hHvalue,?_⟩
  exact norm_from_two_squares ‖H‖ a b δ (Real.sqrt (T*I))
    (norm_nonneg _) ha hb hδ (Real.sqrt_nonneg _) hHnorm₂

end Lemniscate
