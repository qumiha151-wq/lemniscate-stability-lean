import Lemniscate.NormalGraphSobolevCoefficientBounds
import Lemniscate.PeriodicSobolevProductDifferences
import Lemniscate.NormalGraphSobolevPolynomial
import Lemniscate.NormalGraphSobolevLinearization
import Lemniscate.PeriodicProfileBounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-! The H2-small, H4-to-L2 two-point remainder estimate for the full rational
normal-graph equation. Coefficients use only the true H2 inclusion. The linear
part is identified with the already proved Frechet derivative by uniqueness,
after the mixed estimate proves that it is a derivative at zero.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped BigOperators Topology

variable (T : ℝ) [Fact (0 < T)]

private def normalGraphRemainderProjection
    (p : C(AddCircle T, ℂ) × (Fin 6 → C(AddCircle T, ℂ))) :
    Fin 6 → C(AddCircle T, ℂ) :=
  ![p.1,p.2 1,p.2 2,p.2 3,p.2 4,p.2 5]

private theorem normal_graph_remainder_projection_zero :
    normalGraphRemainderProjection T
      (0 : C(AddCircle T, ℂ) × (Fin 6 → C(AddCircle T, ℂ))) = 0 := by
  funext i
  fin_cases i <;> rfl

private theorem normal_graph_remainder_projection_norm
    (p q : C(AddCircle T, ℂ) × (Fin 6 → C(AddCircle T, ℂ))) (i : Fin 6) :
    ‖normalGraphRemainderProjection T p i-normalGraphRemainderProjection T q i‖ ≤
      ‖p-q‖ := by
  fin_cases i
  · simpa [normalGraphRemainderProjection] using norm_fst_le (p-q)
  · simpa [normalGraphRemainderProjection] using
      (norm_le_pi_norm (p-q).2 1).trans (norm_snd_le (p-q))
  · simpa [normalGraphRemainderProjection] using
      (norm_le_pi_norm (p-q).2 2).trans (norm_snd_le (p-q))
  · simpa [normalGraphRemainderProjection] using
      (norm_le_pi_norm (p-q).2 3).trans (norm_snd_le (p-q))
  · simpa [normalGraphRemainderProjection] using
      (norm_le_pi_norm (p-q).2 4).trans (norm_snd_le (p-q))
  · simpa [normalGraphRemainderProjection] using
      (norm_le_pi_norm (p-q).2 5).trans (norm_snd_le (p-q))

private def normalGraphRemainderProducts (f : CircleSobolevSpace T 4) :
    Fin 6 → CircleL2 T :=
  ![circleSobolevCoordinate T 4 4 f,
    circleSobolevCoordinate T 4 2 f,
    circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
      (circleSobolevCoordinate T 4 2 f),
    circleMultiplyL2 T ((circleSobolevContinuousJet T f 2)^2)
      (circleSobolevCoordinate T 4 2 f),
    circleSobolevCoordinate T 4 3 f,
    circleMultiplyL2 T (circleSobolevContinuousJet T f 2)
      (circleSobolevCoordinate T 4 3 f)]

private def normalGraphRemainderLinears :
    Fin 6 → (CircleSobolevSpace T 4 →L[ℂ] CircleL2 T) :=
  ![circleSobolevCoordinate T 4 4,circleSobolevCoordinate T 4 2,0,0,
    circleSobolevCoordinate T 4 3,0]

private def normalGraphRemainderWeights : Fin 6 → ℂ :=
  ![4,2,4,8,((2*Real.sqrt 2:ℝ):ℂ),(2:ℂ)*((2*Real.sqrt 2:ℝ):ℂ)]



private theorem normal_graph_scaled_product
    (a v : C(AddCircle T, ℂ)) (V : CircleL2 T) (α β : ℂ) :
    circleMultiplyL2 T (a*(α • v)) (β • V) =
      (α*β) • circleMultiplyL2 T a (circleMultiplyL2 T v V) := by
  rw [mul_smul_comm,circle_multiply_l2_smul_coefficient,map_smul,
    smul_smul,circle_multiply_l2_mul]

set_option maxHeartbeats 800000 in
private theorem normal_graph_remainder_algebra
    (A : C(AddCircle T, ℂ)) (B : Fin 6 → C(AddCircle T, ℂ))
    (v : C(AddCircle T, ℂ)) (V W X : CircleL2 T) :
    circleCoefficientMultiplyL2 T A ((4:ℂ) • X)+
        circleContinuousL2 T (B 0)+
        circleMultiplyL2 T (B 1) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 2*((2:ℂ) • v)) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 3*((2:ℂ) • v)^2) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 4) (((2*Real.sqrt 2:ℝ):ℂ) • W)+
        circleMultiplyL2 T (B 5*((2:ℂ) • v)) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      circleContinuousL2 T (B 0)+
        ∑ i : Fin 6, normalGraphRemainderWeights i •
          circleMultiplyL2 T (normalGraphRemainderProjection T (A,B) i)
            (![X,V,circleMultiplyL2 T v V,circleMultiplyL2 T (v^2) V,
              W,circleMultiplyL2 T v W] i) := by
  have hlead : circleCoefficientMultiplyL2 T A ((4:ℂ) • X) =
      (4:ℂ) • circleMultiplyL2 T A X := by
    exact (circleMultiplyL2 T A).map_smul (4:ℂ) X
  have hlinear : circleMultiplyL2 T (B 1) ((2:ℂ) • V) =
      (2:ℂ) • circleMultiplyL2 T (B 1) V :=
    (circleMultiplyL2 T (B 1)).map_smul (2:ℂ) V
  have h22 : (2:ℂ)*2 = 4 := by norm_num
  have hquadratic : circleMultiplyL2 T (B 2*((2:ℂ) • v)) ((2:ℂ) • V) =
      (4:ℂ) • circleMultiplyL2 T (B 2) (circleMultiplyL2 T v V) := by
    simpa only [h22] using normal_graph_scaled_product T (B 2) v V 2 2
  have hcubic : circleMultiplyL2 T (B 3*((2:ℂ) • v)^2) ((2:ℂ) • V) =
      (8:ℂ) • circleMultiplyL2 T (B 3) (circleMultiplyL2 T (v^2) V) := by
    rw [smul_pow,normal_graph_scaled_product]
    norm_num
  have hthird : circleMultiplyL2 T (B 4) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      ((2*Real.sqrt 2:ℝ):ℂ) • circleMultiplyL2 T (B 4) W :=
    (circleMultiplyL2 T (B 4)).map_smul ((2*Real.sqrt 2:ℝ):ℂ) W
  have hmixed : circleMultiplyL2 T (B 5*((2:ℂ) • v)) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      ((2:ℂ)*((2*Real.sqrt 2:ℝ):ℂ)) •
        circleMultiplyL2 T (B 5) (circleMultiplyL2 T v W) :=
    normal_graph_scaled_product T (B 5) v W 2 ((2*Real.sqrt 2:ℝ):ℂ)
  rw [hlead,hlinear,hquadratic,hcubic,hthird,hmixed]
  simp only [normalGraphRemainderProjection,normalGraphRemainderWeights,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val,
    Matrix.head_cons,Matrix.tail_cons,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,add_zero]
  ac_rfl

set_option maxHeartbeats 800000 in
private theorem normal_graph_flow_remainder_sum
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 4) (hf : f ∈ circleNormalGraphDomain T K) :
    let u := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
    let J := circleNormalGraphSobolevCoefficients T K c u
    circleNormalGraphFlow T K c f = circleContinuousL2 T (J.2 0)+
      ∑ i : Fin 6, normalGraphRemainderWeights i •
        circleMultiplyL2 T (normalGraphRemainderProjection T J i)
          (normalGraphRemainderProducts T f i) := by
  let u := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
  let z := circleNormalGraphLowCoordinates T u
  have h₀ : circleNormalGraphCoordinates T f 0 = z 0 :=
    circle_normal_graph_coordinates_low T f 0
  have h₁ : circleNormalGraphCoordinates T f 1 = z 1 :=
    circle_normal_graph_coordinates_low T f 1
  have hA : normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f) =
      normalGraphPrincipalCoefficient T K ![z 0,z 1,0,0] := by
    change -((Ring.inverse
        ((1-K.k*(circleNormalGraphCoordinates T f 0))^2+
          (circleNormalGraphCoordinates T f 1)^2))^2) =
      -((Ring.inverse ((1-K.k*z 0)^2+(z 1)^2))^2)
    rw [h₀,h₁]
  have hp := circle_normal_graph_flow_polynomial T K c f hf
  have ha := normal_graph_remainder_algebra T
    (normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f))
    (normalGraphLowerCoefficientMap T K c z)
    (circleSobolevContinuousJet T f 2)
    (circleSobolevCoordinate T 4 2 f)
    (circleSobolevCoordinate T 4 3 f)
    (circleSobolevCoordinate T 4 4 f)
  dsimp only at hp
  dsimp only [u,z] at ha
  have hfull := hp.trans ha
  rw [hA] at hfull
  simpa only [circleNormalGraphSobolevCoefficients,normalGraphRemainderProducts,u,z] using! hfull

set_option maxHeartbeats 2000000 in
/-- Smallness of the true H2 norm gives the full mixed H2-H4 two-point
remainder estimate, with the genuine derivative of the normal-graph flow. -/
theorem circle_normal_graph_sobolev_tame_remainder
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    ∃ δ > 0, ∃ C > 0, ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖circleNormalGraphFlow T K c f-circleNormalGraphFlow T K c g-
          circleNormalGraphDerivative T K c (f-g)‖ ≤
        C*((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
              ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖) := by
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let H₂ : CircleSobolevSpace T 4 → ℝ := fun u => ‖S u‖
  let E : C(AddCircle T, ℂ) →L[ℂ] CircleL2 T :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  let M := circleCoefficientMultiplyL2 T
  let J := circleNormalGraphSobolevCoefficients T K c
  let B0 : CircleSobolevSpace T 2 → C(AddCircle T, ℂ) := fun u => (J u).2 0
  let a (u : CircleSobolevSpace T 4) : Fin 6 → C(AddCircle T, ℂ) :=
    normalGraphRemainderProjection T (J (S u))
  let t := normalGraphRemainderProducts T
  let l := normalGraphRemainderLinears T
  let w := normalGraphRemainderWeights
  let L : CircleSobolevSpace T 4 →L[ℝ] CircleL2 T :=
    (E.restrictScalars ℝ).comp
        ((fderiv ℝ B0 0).comp (S.restrictScalars ℝ))+
      ∑ i : Fin 6, w i • (((M (a 0 i)).comp (l i)).restrictScalars ℝ)
  have hS (u : CircleSobolevSpace T 4) : H₂ u ≤ ‖u‖ := by
    have h₃ : ‖circleSobolevInclusion T 3 u‖ ≤ ‖u‖ := by
      simpa only [one_mul] using (circleSobolevInclusion T 3).le_of_opNorm_le
        (circle_sobolev_inclusion_norm_le T 3) u
    have h₂ : ‖S u‖ ≤ ‖circleSobolevInclusion T 3 u‖ := by
      simpa only [one_mul,S,ContinuousLinearMap.comp_apply] using!
        (circleSobolevInclusion T 2).le_of_opNorm_le
        (circle_sobolev_inclusion_norm_le T 2) (circleSobolevInclusion T 3 u)
    exact h₂.trans h₃
  have hH₂ (u : CircleSobolevSpace T 4) : 0 ≤ H₂ u := norm_nonneg _
  obtain ⟨r,hr,A,hA,hdomain,hcoeff⟩ :=
    circle_normal_graph_sobolev_coefficient_bounds T K c
  obtain ⟨P,hP,hproducts⟩ := circle_sobolev_second_product_bounds T
  obtain ⟨D,hD,hdifferences⟩ := circle_sobolev_product_difference_bounds T
  let δ : ℝ := min r 1
  have hδ : 0 < δ := lt_min hr zero_lt_one
  have hsmall {u : CircleSobolevSpace T 4} (hu : H₂ u < δ) :
      H₂ u < r ∧ H₂ u ≤ 1 := ⟨lt_of_lt_of_le hu (min_le_left _ _),
        le_of_lt (lt_of_lt_of_le hu (min_le_right _ _))⟩
  have hdom {u : CircleSobolevSpace T 4} (hu : H₂ u < δ) :
      u ∈ circleNormalGraphDomain T K :=
    (circle_normal_graph_domain_iff_low T K u).mpr (hdomain (S u) (hsmall hu).1)
  have hzero : H₂ (0 : CircleSobolevSpace T 4) < δ := by
    simpa only [H₂,map_zero,norm_zero] using hδ
  have hLip (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖J (S f)-J (S g)‖ ≤ A*H₂ (f-g) := by
    simpa only [H₂,map_sub] using
      (hcoeff (S f) (hsmall hf).1 (S g) (hsmall hg).1).1
  have haLip (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ)
      (i : Fin 6) : ‖a f i-a g i‖ ≤ A*H₂ (f-g) :=
    (normal_graph_remainder_projection_norm T _ _ i).trans (hLip f g hf hg)
  let N : ℝ := ‖J 0‖+A+1
  have hN : 0 < N := by dsimp only [N]; positivity
  have haBound (u : CircleSobolevSpace T 4) (hu : H₂ u < δ) (i : Fin 6) :
      ‖a u i‖ ≤ N := by
    have h₀ : ‖a 0 i‖ ≤ ‖J 0‖ := by
      have h := normal_graph_remainder_projection_norm T (J 0) 0 i
      simpa only [a,map_zero,normal_graph_remainder_projection_zero,
        Pi.zero_apply,sub_zero] using h
    have h₁ : ‖a u i-a 0 i‖ ≤ A*H₂ u := by
      simpa only [sub_zero] using haLip u 0 hu hzero i
    have h₂ : A*H₂ u ≤ A := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hsmall hu).2 hA.le
    calc
      ‖a u i‖ = ‖(a u i-a 0 i)+a 0 i‖ := by rw [sub_add_cancel]
      _ ≤ ‖a u i-a 0 i‖+‖a 0 i‖ := norm_add_le _ _
      _ ≤ A*H₂ u+‖J 0‖ := add_le_add h₁ h₀
      _ ≤ A+‖J 0‖ := add_le_add h₂ le_rfl
      _ ≤ N := by dsimp only [N]; linarith
  let Q : ℝ := max A (N*(2*D)+A*(2*P))
  have hQ : 0 < Q := lt_of_lt_of_le hA (le_max_left _ _)
  have hAQ : A ≤ Q := le_max_left _ _
  have hNQ : N*(2*D)+A*(2*P) ≤ Q := le_max_right _ _
  have hcoord (j : Fin 5) (u : CircleSobolevSpace T 4) :
      ‖circleSobolevCoordinate T 4 j u‖ ≤ ‖u‖ := by
    simpa only [one_mul] using (circleSobolevCoordinate T 4 j).le_of_opNorm_le
      (circle_sobolev_coordinate_norm_le T 4 j) u
  have hlinear (p : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
      (hp : ∀ u, ‖p u‖ ≤ ‖u‖)
      (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ)
      (i : Fin 6) :
      ‖M (a f i) (p f)-M (a g i) (p g)-M (a 0 i) (p (f-g))‖ ≤
        A*((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
    let d := f-g
    have heq : M (a f i) (p f)-M (a g i) (p g)-M (a 0 i) (p d) =
        M (a f i-a 0 i) (p d)+M (a f i-a g i) (p g) := by
      dsimp only [d]
      simp only [map_sub,ContinuousLinearMap.sub_apply]
      abel
    have haf : ‖a f i-a 0 i‖ ≤ A*H₂ f := by
      simpa only [sub_zero] using haLip f 0 hf hzero i
    calc
      ‖M (a f i) (p f)-M (a g i) (p g)-M (a 0 i) (p (f-g))‖ =
          ‖M (a f i-a 0 i) (p d)+M (a f i-a g i) (p g)‖ := congrArg norm heq
      _ ≤ ‖M (a f i-a 0 i) (p d)‖+‖M (a f i-a g i) (p g)‖ := norm_add_le _ _
      _ ≤ ‖a f i-a 0 i‖*‖p d‖+‖a f i-a g i‖*‖p g‖ :=
        add_le_add (circle_multiply_l2_norm_le T _ _) (circle_multiply_l2_norm_le T _ _)
      _ ≤ (A*H₂ f)*‖d‖+(A*H₂ d)*‖g‖ :=
        add_le_add (mul_le_mul haf (hp d) (norm_nonneg _) (by positivity))
          (mul_le_mul (haLip f g hf hg i) (hp g) (norm_nonneg _) (by positivity))
      _ ≤ A*((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
        have hrem : 0 ≤ A*(H₂ g*‖d‖+‖f‖*H₂ d) := by positivity
        dsimp only [d] at *
        linear_combination hrem
  have hvalue (i : Fin 6) (hi : i = 2 ∨ i = 3 ∨ i = 5)
      (u : CircleSobolevSpace T 4) (hu : H₂ u < δ) : ‖t u i‖ ≤ (2*P)*‖u‖ := by
    have hh : H₂ u ≤ 1 := (hsmall hu).2
    have hh₂ : (H₂ u)^2 ≤ 1 := by
      simpa only [one_pow] using (sq_le_sq₀ (hH₂ u) (by norm_num : (0:ℝ) ≤ 1)).mpr hh
    rcases hi with rfl | rfl | rfl
    · have h := (hproducts u u u).1
      change ‖circleMultiplyL2 T (circleSobolevContinuousJet T u 2)
        (circleSobolevCoordinate T 4 2 u)‖ ≤ _
      have hs : P*‖u‖*H₂ u ≤ (2*P)*‖u‖ := by
        have hrem : 0 ≤ P*‖u‖*(1-H₂ u) := by positivity
        have hrem' : 0 ≤ P*‖u‖ := by positivity
        linear_combination hrem+hrem'
      exact h.trans hs
    · have h := (hproducts u u u).2.1
      simp only [← pow_two] at h
      change ‖circleMultiplyL2 T ((circleSobolevContinuousJet T u 2)^2)
        (circleSobolevCoordinate T 4 2 u)‖ ≤ _
      have hs : P*(H₂ u*‖u‖+H₂ u*‖u‖)*H₂ u ≤ (2*P)*‖u‖ := by
        have hrem : 0 ≤ (2*P)*‖u‖*(1-(H₂ u)^2) := by positivity
        linear_combination hrem
      exact h.trans hs
    · have h := (hproducts u u u).2.2
      change ‖circleMultiplyL2 T (circleSobolevContinuousJet T u 2)
        (circleSobolevCoordinate T 4 3 u)‖ ≤ _
      have hs : P*(H₂ u*‖u‖+H₂ u*‖u‖) ≤ (2*P)*‖u‖ := by
        have hrem : 0 ≤ (2*P)*‖u‖*(1-H₂ u) := by positivity
        linear_combination hrem
      exact h.trans hs
  have hdiff (i : Fin 6) (hi : i = 2 ∨ i = 3 ∨ i = 5)
      (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖t f i-t g i‖ ≤ (2*D)*
        ((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
    let R := (H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have h := hdifferences f g
    have hsum : H₂ f+H₂ g ≤ 2 := by linarith [(hsmall hf).2,(hsmall hg).2]
    rcases hi with rfl | rfl | rfl
    · exact h.1.trans (by
        change D*R ≤ (2*D)*R
        linear_combination (mul_nonneg hD.le hR))
    · exact h.2.1.trans (by
        change D*(H₂ f+H₂ g)*R ≤ (2*D)*R
        simpa only [mul_comm D 2] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum hD.le) hR)
    · exact h.2.2.trans (by
        change D*R ≤ (2*D)*R
        linear_combination (mul_nonneg hD.le hR))
  have hnonlinear (i : Fin 6) (hi : i = 2 ∨ i = 3 ∨ i = 5)
      (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖M (a f i) (t f i)-M (a g i) (t g i)‖ ≤
        (N*(2*D)+A*(2*P))*
          ((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
    let R := (H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have heq : M (a f i) (t f i)-M (a g i) (t g i) =
        M (a f i) (t f i-t g i)+M (a f i-a g i) (t g i) := by
      simp only [map_sub,ContinuousLinearMap.sub_apply]
      abel
    calc
      ‖M (a f i) (t f i)-M (a g i) (t g i)‖ =
          ‖M (a f i) (t f i-t g i)+M (a f i-a g i) (t g i)‖ := congrArg norm heq
      _ ≤ ‖M (a f i) (t f i-t g i)‖+‖M (a f i-a g i) (t g i)‖ := norm_add_le _ _
      _ ≤ ‖a f i‖*‖t f i-t g i‖+‖a f i-a g i‖*‖t g i‖ :=
        add_le_add (circle_multiply_l2_norm_le T _ _) (circle_multiply_l2_norm_le T _ _)
      _ ≤ N*((2*D)*R)+(A*H₂ (f-g))*((2*P)*‖g‖) :=
        add_le_add (mul_le_mul (haBound f hf i) (hdiff i hi f g hf hg)
          (norm_nonneg _) hN.le)
          (mul_le_mul (haLip f g hf hg i) (hvalue i hi g hg) (norm_nonneg _) (by positivity))
      _ ≤ (N*(2*D)+A*(2*P))*R := by
        have hrem : 0 ≤ A*(2*P)*(H₂ f*‖f-g‖+H₂ g*‖f-g‖+‖f‖*H₂ (f-g)) := by
          positivity
        dsimp only [R]
        linear_combination hrem
  have hterms (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ)
      (i : Fin 6) :
      ‖M (a f i) (t f i)-M (a g i) (t g i)-M (a 0 i) (l i (f-g))‖ ≤
        Q*((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
    let R := (H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have hlin (p : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
        (hp : ∀ u, ‖p u‖ ≤ ‖u‖) :=
      (hlinear p hp f g hf hg i).trans (mul_le_mul_of_nonneg_right hAQ hR)
    have hnl (hi : i = 2 ∨ i = 3 ∨ i = 5) :=
      (hnonlinear i hi f g hf hg).trans (mul_le_mul_of_nonneg_right hNQ hR)
    fin_cases i
    · exact hlin (circleSobolevCoordinate T 4 4) (hcoord 4)
    · exact hlin (circleSobolevCoordinate T 4 2) (hcoord 2)
    · simpa [l,normalGraphRemainderLinears] using hnl (Or.inl rfl)
    · simpa [l,normalGraphRemainderLinears] using hnl (Or.inr (Or.inl rfl))
    · exact hlin (circleSobolevCoordinate T 4 3) (hcoord 3)
    · simpa [l,normalGraphRemainderLinears] using hnl (Or.inr (Or.inr rfl))
  let W : ℝ := ∑ i : Fin 6, ‖w i‖
  let C : ℝ := ‖E‖*A+W*Q+1
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hLapply (z : CircleSobolevSpace T 4) :
      L z = E ((fderiv ℝ B0 0) (S z))+
        ∑ i : Fin 6, w i • M (a 0 i) (l i z) := by
    simp only [L,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_restrictScalars']
  have hflow (z : CircleSobolevSpace T 4) (hz : H₂ z < δ) :
      circleNormalGraphFlow T K c z = E (B0 (S z))+
        ∑ i : Fin 6, w i • M (a z i) (t z i) := by
    simpa only [S,ContinuousLinearMap.comp_apply,E,M,a,t,w,J,B0,
      circleContinuousL2,circle_coefficient_multiply_l2_apply] using!
      normal_graph_flow_remainder_sum T K c z (hdom hz)
  have hestimate (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖circleNormalGraphFlow T K c f-circleNormalGraphFlow T K c g-L (f-g)‖ ≤
        C*((H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)) := by
    let R := (H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)
    let b := B0 (S f)-B0 (S g)-(fderiv ℝ B0 0) (S (f-g))
    let e (i : Fin 6) := M (a f i) (t f i)-M (a g i) (t g i)-M (a 0 i) (l i (f-g))
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have hb : ‖E b‖ ≤ (‖E‖*A)*R := by
      have hTaylor : ‖b‖ ≤ A*(H₂ f+H₂ g)*H₂ (f-g) := by
        simpa only [b,H₂,map_sub] using
          (hcoeff (S f) (hsmall hf).1 (S g) (hsmall hg).1).2
      calc
        ‖E b‖ ≤ ‖E‖*‖b‖ := E.le_opNorm b
        _ ≤ ‖E‖*(A*(H₂ f+H₂ g)*H₂ (f-g)) :=
          mul_le_mul_of_nonneg_left hTaylor (norm_nonneg E)
        _ ≤ (‖E‖*A)*R := by
          have h₁ := mul_le_mul_of_nonneg_left (hS (f-g))
            (mul_nonneg (norm_nonneg E) (mul_nonneg hA.le (by positivity : 0 ≤ H₂ f+H₂ g)))
          have h₂ : 0 ≤ (‖E‖*A)*(‖f‖+‖g‖)*H₂ (f-g) := by positivity
          dsimp only [R]
          linear_combination h₁+h₂
    have he : ‖∑ i : Fin 6, w i • e i‖ ≤ (W*Q)*R := by
      calc
        ‖∑ i : Fin 6, w i • e i‖ ≤ ∑ i : Fin 6, ‖w i • e i‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 6, ‖w i‖*(Q*R) := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (hterms f g hf hg i) (norm_nonneg _)
        _ = (W*Q)*R := by dsimp only [W]; rw [← Finset.sum_mul]; ring
    have heq : circleNormalGraphFlow T K c f-circleNormalGraphFlow T K c g-L (f-g) =
        E b+∑ i : Fin 6, w i • e i := by
      rw [hflow f hf,hflow g hg,hLapply]
      dsimp only [b,e]
      simp only [map_sub,Finset.sum_sub_distrib,smul_sub]
      abel
    calc
      ‖circleNormalGraphFlow T K c f-circleNormalGraphFlow T K c g-L (f-g)‖ =
          ‖E b+∑ i : Fin 6, w i • e i‖ := congrArg norm heq
      _ ≤ ‖E b‖+‖∑ i : Fin 6, w i • e i‖ := norm_add_le _ _
      _ ≤ (‖E‖*A)*R+(W*Q)*R := add_le_add hb he
      _ ≤ C*R := by dsimp only [C]; linear_combination hR
  have hL : HasFDerivAt (circleNormalGraphFlow T K c) L 0 := by
    apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
    apply Asymptotics.isLittleO_iff.mpr
    intro ε hε
    have hrad : 0 < min δ (ε/(2*C)) := lt_min hδ (div_pos hε (by positivity))
    filter_upwards [Metric.ball_mem_nhds (0 : CircleSobolevSpace T 4) hrad] with u hu
    have hu' : ‖u‖ < min δ (ε/(2*C)) := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hu
    have huδ : H₂ u < δ := lt_of_le_of_lt (hS u) (lt_of_lt_of_le hu' (min_le_left _ _))
    have hh := hestimate u 0 huδ hzero
    simp only [map_zero,H₂,norm_zero,add_zero,sub_zero,zero_add] at hh
    have hrad' : (2*C)*‖u‖ ≤ ε := by
      simpa only [mul_comm] using
        (le_div_iff₀ (by positivity : 0 < 2*C)).mp
          (le_of_lt (lt_of_lt_of_le hu' (min_le_right _ _)))
    have hsu : ‖S u‖ ≤ ‖u‖ := hS u
    simp only [zero_add]
    calc
      ‖circleNormalGraphFlow T K c u-circleNormalGraphFlow T K c 0-L u‖ ≤
          C*(‖S u‖*‖u‖+‖u‖*‖S u‖) := hh
      _ ≤ ((2*C)*‖u‖)*‖u‖ := by
        have hrem : 0 ≤ (2*C)*‖u‖*(‖u‖-‖S u‖) := by positivity
        linear_combination hrem
      _ ≤ ε*‖u‖ := mul_le_mul_of_nonneg_right hrad' (norm_nonneg u)
  have hidentify : (circleNormalGraphDerivative T K c).restrictScalars ℝ = L :=
    ((circle_normal_graph_hasFDerivAt T K c).restrictScalars ℝ).unique hL
  refine ⟨δ,hδ,C,hC,fun f g hf hg => ?_⟩
  have h := hestimate f g hf hg
  rw [← hidentify] at h
  exact h

end Lemniscate
