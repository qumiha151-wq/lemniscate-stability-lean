import Lemniscate.BernoulliCoverModulation
import Lemniscate.PeriodicCoverStableEnergy
import Lemniscate.PeriodicSobolevPrincipalEstimate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Pointwise absorption for the actual covered modulated equation.
The principal energy controls the complete H4 norm up to an L2 error.
The proved cover metric absorbs that error, and H2 smallness absorbs the
genuine nonlinear remainder. No time differentiation is asserted here. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

private theorem principal_lower_absorption (a h n p b E r μ : ℝ)
    (hμ : 0 ≤ μ) (hr : r ≤ -p^2+p*b*h) (hE : E ≤ 4*h^2)
    (hh : h^2 ≤ 30*a*p) (hn : n^2 ≤ 100*p^2) :
    r+μ*E ≤ -(n^2/200)+(30*(b^2+4*μ))^2*a^2 := by
  let D := 30*(b^2+4*μ)
  have hY : p*b*h ≤ p^2/4+b^2*h^2 := by
    nlinarith only [sq_nonneg (p/2-b*h)]
  have hY' : D*a*p ≤ p^2/4+D^2*a^2 := by
    nlinarith only [sq_nonneg (p/2-D*a)]
  calc
    r+μ*E ≤ (-p^2+p*b*h)+μ*(4*h^2) :=
      add_le_add hr (mul_le_mul_of_nonneg_left hE hμ)
    _ ≤ (-p^2+(p^2/4+b^2*h^2))+μ*(4*h^2) :=
      add_le_add (add_le_add le_rfl hY) le_rfl
    _ = -(3/4:ℝ)*p^2+(b^2+4*μ)*h^2 := by ring
    _ ≤ -(3/4:ℝ)*p^2+(b^2+4*μ)*(30*a*p) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ b^2+4*μ))
    _ = -(3/4:ℝ)*p^2+D*a*p := by dsimp only [D]; ring
    _ ≤ -(3/4:ℝ)*p^2+(p^2/4+D^2*a^2) := add_le_add le_rfl hY'
    _ = -(p^2/2)+D^2*a^2 := by ring
    _ ≤ -(n^2/200)+D^2*a^2 := by linarith only [hn]

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

set_option maxHeartbeats 1000000 in
/-- Any rate below the proved full-cover gap is obtained by combining the
principal H2 energy and the actual stable L2 metric. The normalized adjoint
vector can be the same witness used in the local-solution theorem. -/
theorem bernoulli_cover_combined_energy_estimate
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let E := circlePeriodicExtension T S M hS
    let Q := E q
    let P := E p
    let K := circleBernoulliBackground S Q P
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM (ψ:CircleL2 T) hnorm
    let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
    ∀ μ : ℝ, 0 < μ → μ < gM →
      ∃ κ > 0, ∃ δ > 0, ∃ c > 0, ∀ f : CircleSobolevSpace S 4,
        inner ℂ (Ψ:CircleL2 S) (circleSobolevCoordinate S 4 0 f) = 0 →
        ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ →
        (inner ℂ (circleSobolevPrincipalOperator S f)
          (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) f)).re+
          κ*(inner ℂ (V (circleSobolevCoordinate S 4 0 f))
            (V (circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) f))).re ≤
          -μ*(‖circleSobolevCoordinate S 4 0 f‖^2+
            4*‖circleSobolevCoordinate S 4 2 f‖^2+
            κ*‖V (circleSobolevCoordinate S 4 0 f)‖^2)-c*‖f‖^2 := by
  let E := circlePeriodicExtension T S M hS
  let Q := E q
  let P := E p
  let K := circleBernoulliBackground S Q P
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let V := circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
    M hM (ψ:CircleL2 T) hnorm
  let F := circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
  let D := circleNormalGraphDerivative S K (15/2)
  let R : CircleSobolevSpace S 4 → CircleL2 S := fun f => F f-D f
  let B : CircleSobolevSpace S 2 →L[ℂ] CircleL2 S :=
    circleSobolevCoordinate S 2 0+
      circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
  let H (f : CircleSobolevSpace S 4) :=
    circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)
  let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
  obtain ⟨ψ',hnorm',hzero',_,hd',_,_,_,hFzero',_,δ₀,hδ₀,C₀,hC₀,_,htame'⟩ :=
    paper_periodic_cover_modulated_tame T S q p hq hp he hqreal hpreal hs hc ho hr M hM hS
  obtain ⟨ψ₀,_,hunique⟩ :=
    paper_single_period_adjoint_vector T q p hq hp he hqreal hpreal hs hc ho hr
  have hψ : ψ' = ψ := (hunique ψ' ⟨hnorm',hzero'⟩).trans
    (hunique ψ ⟨hnorm,hψzero⟩).symm
  subst ψ'
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  have hD : D = circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
    (circle_normal_graph_hasFDerivAt S K (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE).2
  have henergy : ∀ f : CircleSobolevSpace S 4,
      inner ℂ (Ψ:CircleL2 S) (circleSobolevCoordinate S 4 0 f) = 0 →
      (inner ℂ (V (circleSobolevCoordinate S 4 0 f)) (V (D f))).re ≤
        -gM*‖V (circleSobolevCoordinate S 4 0 f)‖^2 := by
    intro f hf
    have h := paper_periodic_cover_stable_energy T S q p hq hp he hqreal hpreal hs hc ho hr
      ψ hnorm hψzero hd' M hM hS (circleSobolevToH4Domain S f) hf
    change (inner ℂ (V (circleSobolevCoordinate S 4 0 f))
      (V (circleH4Operator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
        (circleSobolevToH4Domain S f)))).re ≤
      -gM*‖V (circleSobolevCoordinate S 4 0 f)‖^2 at h
    rw [← circle_sobolev_operator_eq_h4,← hD] at h
    exact h
  have hDexpr (f : CircleSobolevSpace S 4) :
      D f = -(circleSobolevPrincipalOperator S f)+B (H f) := by
    rw [hD,circle_sobolev_operator_lower_order]
    have hvalue : circleSobolevCoordinate S 2 0 (H f) = circleSobolevCoordinate S 4 0 f := rfl
    simp only [circleSobolevPrincipalOperator,B,ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply,hvalue]
    module
  obtain ⟨CV,hCV,hV⟩ := circle_cover_stable_metric_bounds T S q p hq hp he hqreal hpreal
    hs hc ho hr M hM (ψ:CircleL2 T) hnorm
  let C : ℝ := 2*C₀
  have hC : 0 < C := mul_pos (by norm_num) hC₀
  dsimp only
  intro μ hμ hμg
  let Clinear : ℝ := (30*(‖B‖^2+4*μ))^2
  let κ : ℝ := (Clinear*CV^2+1)/(gM-μ)
  have hgap : 0 < gM-μ := sub_pos.mpr hμg
  have hκ : 0 < κ := by dsimp only [κ,Clinear]; positivity
  have hκid : κ*(gM-μ) = Clinear*CV^2+1 := div_mul_cancel₀ _ hgap.ne'
  let A : ℝ := C*(5+κ*CV^2)
  have hA : 0 < A := by dsimp only [A]; positivity
  let δ : ℝ := min δ₀ (1/(400*A))
  have hδ : 0 < δ := lt_min hδ₀ (one_div_pos.mpr (by positivity))
  have hδold : δ ≤ δ₀ := min_le_left _ _
  have hδbound : A*δ ≤ 1/400 := by
    have ht := (le_div_iff₀ (by positivity : (0:ℝ) < 400*A)).mp
      (min_le_right δ₀ (1/(400*A)))
    change δ*(400*A) ≤ 1 at ht
    calc
      A*δ = (δ*(400*A))/400 := by ring
      _ ≤ 1/400 := div_le_div_of_nonneg_right ht (by norm_num)
  refine ⟨κ,hκ,δ,hδ,(1/400:ℝ),by norm_num,?_⟩
  intro f hphase hf
  let u := circleSobolevCoordinate S 4 0 f
  let Z := circleSobolevPrincipalOperator S f
  let n := ‖f‖
  let a := ‖u‖
  let h := ‖H f‖
  let p₀ := ‖Z‖
  let E₁ := a^2+4*‖circleSobolevCoordinate S 4 2 f‖^2
  let E₀ := ‖V u‖^2
  have hn : 0 ≤ n := norm_nonneg f
  have ha : 0 ≤ a := norm_nonneg u
  have hp₀ : 0 ≤ p₀ := norm_nonneg Z
  have hcoord (j : Fin 5) : ‖circleSobolevCoordinate S 4 j f‖ ≤ n := by
    simpa only [n,one_mul] using
      (circleSobolevCoordinate S 4 j).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le S 4 j) f
  have hprincipal : n ≤ 10*p₀ := circle_sobolev_principal_estimate S f
  have hn2 : n^2 ≤ 100*p₀^2 := by
    have hs := (sq_le_sq₀ hn (by positivity : 0 ≤ 10*p₀)).mpr hprincipal
    nlinarith only [hs]
  have hh : h^2 ≤ 30*a*p₀ :=
    (circle_sobolev_h2_interpolation S f).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hprincipal ha])
  have hE₁ : E₁ ≤ 4*h^2 := by
    change ‖circleSobolevCoordinate S 4 0 f‖^2+4*‖circleSobolevCoordinate S 4 2 f‖^2 ≤
      4*‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖^2
    rw [circle_sobolev_h2_inclusion_norm_sq]
    nlinarith only [sq_nonneg ‖circleSobolevCoordinate S 4 0 f‖,
      sq_nonneg ‖circleSobolevCoordinate S 4 1 f‖]
  have hlin : (inner ℂ Z (D f)).re+μ*E₁ ≤ -(n^2/200)+Clinear*a^2 := by
    have hlow : (inner ℂ Z (B (H f))).re ≤ p₀*‖B‖*h := by
      calc
        (inner ℂ Z (B (H f))).re ≤ ‖Z‖*‖B (H f)‖ :=
          (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
        _ ≤ p₀*(‖B‖*h) := mul_le_mul_of_nonneg_left (B.le_opNorm _) hp₀
        _ = p₀*‖B‖*h := by ring
    have hraw : (inner ℂ Z (D f)).re ≤ -p₀^2+p₀*‖B‖*h := by
      have hZRe : (inner ℂ Z Z).re = p₀^2 := by
        change (inner ℂ Z Z).re = ‖Z‖^2
        simpa only using! (norm_sq_eq_re_inner (𝕜 := ℂ) Z).symm
      rw [hDexpr,inner_add_right,Complex.add_re,inner_neg_right,Complex.neg_re,hZRe]
      exact add_le_add le_rfl hlow
    exact principal_lower_absorption a h n p₀ ‖B‖ E₁ _ μ hμ.le hraw hE₁ hh hn2
  have hmetric : (inner ℂ (V u) (V (D f))).re ≤ -gM*E₀ := henergy f hphase
  have hav : a^2 ≤ CV^2*E₀ := by
    have h := (sq_le_sq₀ ha (by positivity : 0 ≤ CV*‖V u‖)).mpr (hV u).1
    simpa only [mul_pow] using h
  have hcancel : Clinear*a^2-κ*(gM-μ)*E₀ ≤ 0 := by
    calc
      Clinear*a^2-κ*(gM-μ)*E₀ ≤ Clinear*(CV^2*E₀)-κ*(gM-μ)*E₀ :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hav
          (by dsimp only [Clinear]; positivity : 0 ≤ Clinear)) _
      _ = -E₀ := by rw [hκid]; ring
      _ ≤ 0 := neg_nonpos.mpr (sq_nonneg _)
  have hlinear : (inner ℂ Z (D f)).re+κ*(inner ℂ (V u) (V (D f))).re+
      μ*(E₁+κ*E₀) ≤ -(n^2/200) := by
    calc
      _ = ((inner ℂ Z (D f)).re+μ*E₁)+
          κ*((inner ℂ (V u) (V (D f))).re+μ*E₀) := by ring
      _ ≤ (-(n^2/200)+Clinear*a^2)+κ*(-gM*E₀+μ*E₀) :=
        add_le_add hlin (mul_le_mul_of_nonneg_left (add_le_add hmetric le_rfl) hκ.le)
      _ = -(n^2/200)+(Clinear*a^2-κ*(gM-μ)*E₀) := by ring
      _ ≤ -(n^2/200) := by linarith only [hcancel]
  have hrem : ‖R f‖ ≤ C*δ*n := by
    have hTame0 := htame' f 0 (hf.trans_le hδold) (by simpa only [map_zero,norm_zero] using hδ₀)
    have hN : ‖R f‖ ≤ C₀*(h*n+n*h) := by
      simpa only [hFzero',map_zero,norm_zero,sub_zero,add_zero] using hTame0
    calc
      ‖R f‖ ≤ C₀*(h*n+n*h) := hN
      _ = C*h*n := by dsimp only [C]; ring
      _ ≤ C*δ*n := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hf.le hC.le) hn
  have hZ : p₀ ≤ 5*n := by
    calc
      p₀ ≤ ‖u‖+4*‖circleSobolevCoordinate S 4 4 f‖ := by
        change ‖u+(4:ℂ) • circleSobolevCoordinate S 4 4 f‖ ≤ _
        have h := norm_add_le u ((4:ℂ) • circleSobolevCoordinate S 4 4 f)
        rw [norm_smul] at h
        norm_num at h
        exact h
      _ ≤ n+4*n := add_le_add (hcoord 0)
        (mul_le_mul_of_nonneg_left (hcoord 4) (by norm_num))
      _ = 5*n := by ring
  have hnonlinear : (inner ℂ Z (R f)).re+κ*(inner ℂ (V u) (V (R f))).re ≤ n^2/400 := by
    have hhigh : (inner ℂ Z (R f)).re ≤ (5*n)*(C*δ*n) :=
      ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _)).trans
        (mul_le_mul hZ hrem (norm_nonneg _) (by positivity : 0 ≤ 5*n))
    have hlow : (inner ℂ (V u) (V (R f))).re ≤ (CV*n)*(CV*(C*δ*n)) := by
      have hvu : ‖V u‖ ≤ CV*n := (hV u).2.trans
        (mul_le_mul_of_nonneg_left (hcoord 0) hCV.le)
      have hvr : ‖V (R f)‖ ≤ CV*(C*δ*n) := (hV (R f)).2.trans
        (mul_le_mul_of_nonneg_left hrem hCV.le)
      exact ((Complex.re_le_norm _).trans (norm_inner_le_norm _ _)).trans
        (mul_le_mul hvu hvr (norm_nonneg _) (by positivity : 0 ≤ CV*n))
    calc
      _ ≤ (5*n)*(C*δ*n)+κ*((CV*n)*(CV*(C*δ*n))) :=
        add_le_add hhigh (mul_le_mul_of_nonneg_left hlow hκ.le)
      _ = (A*δ)*n^2 := by dsimp only [A]; ring
      _ ≤ (1/400)*n^2 := mul_le_mul_of_nonneg_right hδbound (sq_nonneg n)
      _ = n^2/400 := by ring
  have hsplit : F f = D f+R f := by dsimp only [R]; abel
  have htotal : (inner ℂ Z (F f)).re+κ*(inner ℂ (V u) (V (F f))).re+
      μ*(E₁+κ*E₀) ≤ -(n^2/400) := by
    calc
      _ = ((inner ℂ Z (D f)).re+κ*(inner ℂ (V u) (V (D f))).re+μ*(E₁+κ*E₀))+
          ((inner ℂ Z (R f)).re+κ*(inner ℂ (V u) (V (R f))).re) := by
        simp only [hsplit,map_add,inner_add_right,Complex.add_re]
        ring
      _ ≤ -(n^2/200)+n^2/400 := add_le_add hlinear hnonlinear
      _ = -(n^2/400) := by ring
  change (inner ℂ Z (F f)).re+κ*(inner ℂ (V u) (V (F f))).re ≤
    -μ*(E₁+κ*E₀)-(1/400)*n^2
  linarith only [htotal]

end Profile
end Lemniscate
