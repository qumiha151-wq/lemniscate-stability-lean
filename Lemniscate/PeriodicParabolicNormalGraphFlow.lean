import Lemniscate.NormalGraphJointCoefficientAlgebra
import Lemniscate.PeriodicTimeCoefficientAlgebra
import Lemniscate.PeriodicParabolicProducts
import Lemniscate.NormalGraphSobolevPolynomial
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-! The unmodulated normal-graph equation on the actual maximal-regularity
space, jointly with its time-dependent background. The six multilinear
products and their physical derivative factors are those of the spatial
normal-graph equation. No H4 continuity in time is used.

-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal BigOperators Topology

private def timeGraphWeights : Fin 6 → ℂ :=
  ![4,2,4,8,((2*Real.sqrt 2:ℝ):ℂ),(2:ℂ)*((2*Real.sqrt 2:ℝ):ℂ)]

private def timeGraphCoefficient {R : Type*} (a : R × (Fin 6 → R)) : Fin 6 → R :=
  ![a.1,a.2 1,a.2 2,a.2 3,a.2 4,a.2 5]

section Assembly
variable {R E Y : Type*}
    [NormedAddCommGroup R] [NormedSpace ℂ R]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

private def timeGraphAssembly
    (M : R →L[ℂ] Y →L[ℂ] Y) (C : R →L[ℂ] Y)
    (a : R × (Fin 6 → R)) (v : Fin 6 → Y) : Y :=
  C (a.2 0)+∑ i : Fin 6, timeGraphWeights i • M (timeGraphCoefficient a i) (v i)

private theorem timeGraphAssembly_smooth
    (M : R →L[ℂ] Y →L[ℂ] Y) (C : R →L[ℂ] Y) :
    ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun p : (R × (Fin 6 → R)) × (Fin 6 → Y) =>
        timeGraphAssembly M C p.1 p.2) := by
  have hC : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun p : (R × (Fin 6 → R)) × (Fin 6 → Y) => C (p.1.2 0)) := by
    exact C.contDiff.comp ((show (Fin 6 → R) →L[ℂ] R from
      ContinuousLinearMap.proj (0 : Fin 6)).contDiff.comp
      (contDiff_snd.comp contDiff_fst))
  have hM := M.isBoundedBilinearMap.contDiff (n := (⊤ : WithTop ℕ∞))
  apply hC.add
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun p : (R × (Fin 6 → R)) × (Fin 6 → Y) => timeGraphCoefficient p.1 i) := by
    fin_cases i <;> simp only [timeGraphCoefficient,Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> fun_prop
  have hv : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun p : (R × (Fin 6 → R)) × (Fin 6 → Y) => p.2 i) :=
    (show (Fin 6 → Y) →L[ℂ] Y from ContinuousLinearMap.proj i).contDiff.comp contDiff_snd
  exact (hM.comp (ha.prodMk hv)).const_smul (timeGraphWeights i)

private def timeGraphProducts
    (d₄ d₂ d₃ : E →L[ℂ] Y)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y)
    (C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) Y)
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y) (u : E) : Fin 6 → Y :=
  ![d₄ u,d₂ u,B (fun _ => u),C (fun _ => u),d₃ u,D (fun _ => u)]

private theorem timeGraphProducts_smooth
    (d₄ d₂ d₃ : E →L[ℂ] Y)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y)
    (C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) Y)
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y) :
    ContDiff ℂ (⊤ : WithTop ℕ∞) (timeGraphProducts d₄ d₂ d₃ B C D) := by
  have hd₂ : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun u : E => fun _ : Fin 2 => u) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  have hd₃ : ContDiff ℂ (⊤ : WithTop ℕ∞) (fun u : E => fun _ : Fin 3 => u) :=
    contDiff_pi.mpr (fun _ => contDiff_id)
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact d₄.contDiff
  · exact d₂.contDiff
  · exact B.contDiff.comp hd₂
  · exact C.contDiff.comp hd₃
  · exact d₃.contDiff
  · exact D.contDiff.comp hd₂

end Assembly

/- Restriction of rational coefficients is legitimate only on their actual
unit domain. This purely algebraic step also applies to time slices. -/
section Restriction
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℝ R] [Algebra ℝ S]

/-- An algebra homomorphism preserves the inverse of an actual unit. -/
theorem algebra_map_ring_inverse
    (e : R →ₐ[ℝ] S) (a : R) (ha : IsUnit a) :
    e (Ring.inverse a) = Ring.inverse (e a) := by
  apply (ha.map e).mul_left_cancel
  rw [← map_mul,Ring.mul_inverse_cancel a ha,map_one,
    Ring.mul_inverse_cancel (e a) (ha.map e)]

/-- The rational normal-graph equation commutes with algebra homomorphisms
on its actual unit domain. This covers restriction and spatial translation. -/
theorem rational_flow_algebra_map
    (e : R →ₐ[ℝ] S) (K : BackgroundJetOver R) (c : ℝ) (h : HeightJetOver R)
    (hA : IsUnit (graphA K h)) (hH : IsUnit (graphMetricSquared K h)) :
    e (normalGraphRationalFlow K c h) = normalGraphRationalFlow
      ⟨e K.k,e K.ks,e K.kss,e K.ksss,e K.eta,e K.b⟩ c
      ⟨e h.h,e h.hs,e h.hss,e h.hsss,e h.hssss⟩ := by
  have hiA := algebra_map_ring_inverse e (graphA K h) hA
  have hiH := algebra_map_ring_inverse e (graphMetricSquared K h) hH
  simp only [normalGraphRationalFlow,map_neg,map_mul,map_sub,map_add,map_pow,map_smul,
    hiA,hiH]
  simp only [graphCurvatureNumeratorSS,graphCurvatureNumeratorS,
    graphCurvatureNumerator,graphMetricSquaredSS,graphMetricSquaredS,
    graphMetricSquared,graphSupportNumerator,graphAss,graphAs,graphA,
    map_neg,map_mul,map_sub,map_add,map_pow,map_one,map_ofNat]

private theorem joint_domain_algebra_map
    (e : R →ₐ[ℝ] S) (a : Fin 6 → R) (u : Fin 2 → R)
    (hu : (a,u) ∈ normalGraphJointCoefficientDomainOver R) :
    ((fun j => e (a j)),(fun j => e (u j))) ∈
      normalGraphJointCoefficientDomainOver S := by
  change IsUnit (graphA (normalGraphBackgroundFromCoordinates a)
      ⟨u 0,u 1,0,0,0⟩) ∧
    IsUnit (graphMetricSquared (normalGraphBackgroundFromCoordinates a)
      ⟨u 0,u 1,0,0,0⟩) at hu
  change IsUnit (1-e (a 0)*e (u 0)) ∧
    IsUnit ((1-e (a 0)*e (u 0))^2+(e (u 1))^2)
  constructor
  · simpa only [graphA,normalGraphBackgroundFromCoordinates,map_sub,map_one,map_mul]
      using hu.1.map e
  · simpa only [graphMetricSquared,graphA,normalGraphBackgroundFromCoordinates,
      map_add,map_pow,map_sub,map_one,map_mul] using hu.2.map e

set_option maxHeartbeats 600000 in
private theorem joint_coefficients_algebra_map
    (e : R →ₐ[ℝ] S) (a : Fin 6 → R) (u : Fin 2 → R) (c : ℝ)
    (hu : (a,u) ∈ normalGraphJointCoefficientDomainOver R) :
    normalGraphJointCoefficientMapOver S c
      ((fun j => e (a j)),(fun j => e (u j))) =
      (e (normalGraphJointCoefficientMapOver R c (a,u)).1,
        fun i => e ((normalGraphJointCoefficientMapOver R c (a,u)).2 i)) := by
  let K := normalGraphBackgroundFromCoordinates a
  have hA (v w : R) : IsUnit (graphA K ⟨u 0,u 1,v,w,0⟩) := hu.1
  have hH (v w : R) : IsUnit (graphMetricSquared K ⟨u 0,u 1,v,w,0⟩) := hu.2
  let L := normalGraphBackgroundFromCoordinates (fun j => e (a j))
  have hb (v w : R) : e (normalGraphRationalFlow K c ⟨u 0,u 1,v,w,0⟩) =
      normalGraphRationalFlow L c ⟨e (u 0),e (u 1),e v,e w,0⟩ := by
    have hK : (⟨e K.k,e K.ks,e K.kss,e K.ksss,e K.eta,e K.b⟩ : BackgroundJetOver S) = L := by
      dsimp only [K,L,normalGraphBackgroundFromCoordinates]
    simpa only [hK,map_zero] using rational_flow_algebra_map e K c
      ⟨u 0,u 1,v,w,0⟩ (hA v w) (hH v w)
  apply Prod.ext
  · have hi := algebra_map_ring_inverse e
      (graphMetricSquared K ⟨u 0,u 1,0,0,0⟩) (hH 0 0)
    change e (Ring.inverse ((1-a 0*u 0)^2+(u 1)^2)) =
      Ring.inverse (e ((1-a 0*u 0)^2+(u 1)^2)) at hi
    simp only [map_add,map_pow,map_sub,map_one,map_mul] at hi
    change -(Ring.inverse ((1-e (a 0)*e (u 0))^2+(e (u 1))^2))^2 =
      e (-(Ring.inverse ((1-a 0*u 0)^2+(u 1)^2))^2)
    rw [map_neg,map_pow,hi]
  · change normalGraphLowerCoefficients L c (e (u 0)) (e (u 1)) =
      (fun i => e (normalGraphLowerCoefficients K c (u 0) (u 1) i))
    funext i
    fin_cases i <;> simp only [normalGraphLowerCoefficients,
      Matrix.cons_val_zero',Matrix.cons_val_succ',map_sub,map_add,map_mul,
      map_smul,map_ofNat,map_one,map_zero,map_neg,hb]

end Restriction

section JointSmoothAssembly
variable {R E Y : Type*} [NormedCommRing R] [NormedAlgebra ℂ R]
    [CompleteSpace R] [Algebra ℝ R]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]

private def timeGraphInput (low : E →L[ℂ] (Fin 2 → R)) :
    ((Fin 6 → R) × E) →L[ℂ] ((Fin 6 → R) × (Fin 2 → R)) :=
  (ContinuousLinearMap.fst ℂ _ _).prod
    (low.comp (ContinuousLinearMap.snd ℂ _ _))

private theorem joint_time_graph_smooth (c : ℝ) (low : E →L[ℂ] (Fin 2 → R))
    (M : R →L[ℂ] Y →L[ℂ] Y) (C₀ : R →L[ℂ] Y)
    (d₄ d₂ d₃ : E →L[ℂ] Y)
    (B : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y)
    (C : ContinuousMultilinearMap ℂ (fun _ : Fin 3 => E) Y)
    (D : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => E) Y) :
    let input := timeGraphInput low
    let domain := input ⁻¹' normalGraphJointCoefficientDomainOver R
    let flow := fun z : (Fin 6 → R) × E =>
      timeGraphAssembly M C₀ (normalGraphJointCoefficientMapOver R c (input z))
        (timeGraphProducts d₄ d₂ d₃ B C D z.2)
    IsOpen domain ∧ (∀ a : Fin 6 → R, (a,(0 : E)) ∈ domain) ∧
      ContDiffOn ℂ (⊤ : WithTop ℕ∞) flow domain := by
  dsimp only
  obtain ⟨hopen,hzero,hjoint⟩ := normal_graph_joint_coefficients_smooth_over R c
  have hinput := (timeGraphInput low).contDiff (n := (⊤ : WithTop ℕ∞))
  have hcoeff : ContDiffOn ℂ (⊤ : WithTop ℕ∞)
      (fun z => normalGraphJointCoefficientMapOver R c (timeGraphInput low z))
      ((timeGraphInput low) ⁻¹' normalGraphJointCoefficientDomainOver R) :=
    hjoint.comp hinput.contDiffOn (fun _ hz => hz)
  have hhigh : ContDiff ℂ (⊤ : WithTop ℕ∞)
      (fun z : (Fin 6 → R) × E => timeGraphProducts d₄ d₂ d₃ B C D z.2) :=
    (timeGraphProducts_smooth d₄ d₂ d₃ B C D).comp contDiff_snd
  refine ⟨hopen.preimage (timeGraphInput low).continuous,?_,?_⟩
  · intro a
    change (a,low 0) ∈ normalGraphJointCoefficientDomainOver R
    simpa only [map_zero] using hzero a
  · exact (timeGraphAssembly_smooth M C₀).comp_contDiffOn
      (hcoeff.prodMk hhigh.contDiffOn)

end JointSmoothAssembly

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private def parabolicTimeCoordinate (j : Fin 5) :
    CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
  ((circleSobolevCoordinate T 4 j).compLpL 2 (volume : Measure unitInterval)).comp
    (circleParabolicH4 T τ)

private def parabolicGraphProducts : CircleParabolicSpace T τ →
    Fin 6 → CircleTimeL2 T :=
  timeGraphProducts (parabolicTimeCoordinate T τ 4) (parabolicTimeCoordinate T τ 2)
    (parabolicTimeCoordinate T τ 3) (circleParabolicSecondProduct T τ)
    (circleParabolicCubicSecondProduct T τ) (circleParabolicSecondThirdProduct T τ)

/-- A continuous function of time and position, viewed in the actual time-L2
space by multiplication with the constant spatial function one. -/
def circleTimeContinuousL2 : CircleTimeCoefficient T →L[ℂ] CircleTimeL2 T :=
  (circleTimeCoefficientMultiplyL2 T).flip
    (Lp.const 2 (volume : Measure unitInterval) (circleContinuousL2 T 1))

set_option maxHeartbeats 600000 in
private def parabolicGraphCoefficientInput :
    ((Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ) →L[ℂ]
      ((Fin 6 → CircleTimeCoefficient T) × (Fin 2 → CircleTimeCoefficient T)) :=
  by
    simpa only using! (timeGraphInput (R := CircleTimeCoefficient T)
      (E := ↥(CircleParabolicSpace T τ)) (circleParabolicLowCoordinates T τ))

/-- The actual A and squared-metric unit conditions in the joint continuous
time-space coefficient algebra. Only the first two height jets enter. -/
def circleParabolicNormalGraphDomain :
    Set ((Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ) :=
  (parabolicGraphCoefficientInput T τ) ⁻¹'
    normalGraphJointCoefficientDomainOver (CircleTimeCoefficient T)

/-- The full unmodulated normal-graph right-hand side in time L2, with
jointly variable continuous background fields. -/
def circleParabolicNormalGraphFlow (c : ℝ)
    (z : (Fin 6 → CircleTimeCoefficient T) × CircleParabolicSpace T τ) :
    CircleTimeL2 T :=
  timeGraphAssembly (circleTimeCoefficientMultiplyL2 T) (circleTimeContinuousL2 T)
    (normalGraphJointCoefficientMapOver (CircleTimeCoefficient T) c
      (parabolicGraphCoefficientInput T τ z))
    (parabolicGraphProducts T τ z.2)

set_option maxHeartbeats 800000 in
/-- Joint complex smoothness of the actual time normal-graph equation on
the open unit domain, which contains every zero height with any background. -/
theorem circle_parabolic_normal_graph_flow_smooth (c : ℝ) :
    IsOpen (circleParabolicNormalGraphDomain T τ) ∧
      (∀ a : Fin 6 → CircleTimeCoefficient T,
        (a,(0 : CircleParabolicSpace T τ)) ∈ circleParabolicNormalGraphDomain T τ) ∧
      ContDiffOn ℂ (⊤ : WithTop ℕ∞) (circleParabolicNormalGraphFlow T τ c)
        (circleParabolicNormalGraphDomain T τ) := by
  simpa only [circleParabolicNormalGraphDomain,circleParabolicNormalGraphFlow,
    parabolicGraphCoefficientInput,parabolicGraphProducts] using!
    (joint_time_graph_smooth (R := CircleTimeCoefficient T)
      (E := ↥(CircleParabolicSpace T τ)) (Y := ↥(CircleTimeL2 T)) c
      (circleParabolicLowCoordinates T τ) (circleTimeCoefficientMultiplyL2 T)
      (circleTimeContinuousL2 T) (parabolicTimeCoordinate T τ 4)
      (parabolicTimeCoordinate T τ 2) (parabolicTimeCoordinate T τ 3)
      (circleParabolicSecondProduct T τ) (circleParabolicCubicSecondProduct T τ)
      (circleParabolicSecondThirdProduct T τ))

/-- Restriction of continuous time-space coefficients to one time slice. -/
def circleTimeCoefficientRestriction (t : unitInterval) :
    CircleTimeCoefficient T →ₐ[ℝ] C(AddCircle T, ℂ) :=
  ContinuousMap.compRightAlgHom ℝ ℂ
    ⟨fun x => (t,x),continuous_const.prodMk continuous_id⟩

/-- Restricting a whole unit coefficient to a fixed time preserves its
ring inverse. Pointwise inverses are not assumed for nonunit functions. -/
theorem circle_time_coefficient_inverse_restrict
    (a : CircleTimeCoefficient T) (ha : IsUnit a) (t : unitInterval) :
    (Ring.inverse a).curry t = Ring.inverse (a.curry t) :=
  algebra_map_ring_inverse (circleTimeCoefficientRestriction T t) a ha

/-- The six background fields restricted to a fixed time. -/
def circleTimeNormalGraphBackground
    (a : Fin 6 → CircleTimeCoefficient T) (t : unitInterval) :
    BackgroundJetOver C(AddCircle T, ℂ) :=
  normalGraphBackgroundFromCoordinates (fun i => (a i).curry t)

private theorem time_coefficient_multiply_l2_ae
    (a : CircleTimeCoefficient T) (w : CircleTimeL2 T) :
    (circleTimeCoefficientMultiplyL2 T a w : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleMultiplyL2 T (a.curry t) (w t) := by
  filter_upwards [circle_time_coefficient_multiply_l2_ae T a w] with t ht
  apply Lp.ext
  filter_upwards [ht,circle_multiply_l2_ae T (a.curry t) (w t)] with x hleft hright
  exact hleft.trans hright.symm

theorem circle_time_continuous_l2_ae (a : CircleTimeCoefficient T) :
    (circleTimeContinuousL2 T a : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleContinuousL2 T (a.curry t) := by
  have hm := time_coefficient_multiply_l2_ae T a
    (Lp.const 2 (volume : Measure unitInterval) (circleContinuousL2 T 1))
  filter_upwards [hm,Lp.coeFn_const 2 (volume : Measure unitInterval)
    (circleContinuousL2 T 1)] with t ht hconst
  change circleTimeCoefficientMultiplyL2 T a _ t = _
  rw [ht,hconst]
  change circleMultiplyL2 T (a.curry t) (circleContinuousL2 T 1) = _
  rw [circle_multiply_l2_continuous,mul_one]

private theorem time_graph_assembly_ae
    (a : CircleTimeCoefficient T × (Fin 6 → CircleTimeCoefficient T))
    (v : Fin 6 → CircleTimeL2 T) :
    ((timeGraphAssembly (circleTimeCoefficientMultiplyL2 T) (circleTimeContinuousL2 T)
      a v : CircleTimeL2 T) : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => timeGraphAssembly (circleCoefficientMultiplyL2 T)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
        ((a.1).curry t,fun i => (a.2 i).curry t) (fun i => v i t) := by
  have hterms : ∀ᵐ t : unitInterval ∂volume, ∀ i : Fin 6,
      ((timeGraphWeights i) • circleTimeCoefficientMultiplyL2 T
        (timeGraphCoefficient a i) (v i)) t =
      timeGraphWeights i • circleMultiplyL2 T
        ((timeGraphCoefficient a i).curry t) (v i t) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (timeGraphWeights i)
      (circleTimeCoefficientMultiplyL2 T (timeGraphCoefficient a i) (v i)),
      time_coefficient_multiply_l2_ae T (timeGraphCoefficient a i) (v i)] with t hs hm
    exact hs.trans (congrArg (fun w : CircleL2 T => timeGraphWeights i • w) hm)
  filter_upwards [Lp.coeFn_add (circleTimeContinuousL2 T (a.2 0))
      (∑ i : Fin 6, timeGraphWeights i •
        circleTimeCoefficientMultiplyL2 T (timeGraphCoefficient a i) (v i)),
    circle_time_continuous_l2_ae T (a.2 0),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin 6 =>
      timeGraphWeights i • circleTimeCoefficientMultiplyL2 T (timeGraphCoefficient a i) (v i)),
    hterms] with t hadd hconst hsum hterm
  change (show CircleTimeL2 T from circleTimeContinuousL2 T (a.2 0)+
      ∑ i : Fin 6, timeGraphWeights i •
        circleTimeCoefficientMultiplyL2 T (timeGraphCoefficient a i) (v i)) t =
    circleContinuousL2 T ((a.2 0).curry t)+
      ∑ i : Fin 6, timeGraphWeights i •
        circleMultiplyL2 T
          (timeGraphCoefficient ((a.1).curry t,fun j => (a.2 j).curry t) i) (v i t)
  rw [hadd,Pi.add_apply,hconst,hsum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hterm i]
  congr 2
  fin_cases i <;> rfl

private def spatialGraphProducts (f : CircleSobolevSpace T 4) : Fin 6 → CircleL2 T :=
  ![circleSobolevCoordinate T 4 4 f,circleSobolevCoordinate T 4 2 f,
    circleMultiplyL2 T (circleSobolevContinuousJet T f 2) (circleSobolevCoordinate T 4 2 f),
    circleMultiplyL2 T ((circleSobolevContinuousJet T f 2)^2)
      (circleSobolevCoordinate T 4 2 f),
    circleSobolevCoordinate T 4 3 f,
    circleMultiplyL2 T (circleSobolevContinuousJet T f 2) (circleSobolevCoordinate T 4 3 f)]

private theorem circle_product_associative
    (a b : C(AddCircle T, ℂ)) (v : CircleL2 T) :
    circleMultiplyL2 T (a*b) v = circleMultiplyL2 T a (circleMultiplyL2 T b v) := by
  apply Lp.ext
  filter_upwards [circle_multiply_l2_ae T (a*b) v,
    circle_multiply_l2_ae T a (circleMultiplyL2 T b v),
    circle_multiply_l2_ae T b v] with x hab ha hb
  rw [hab,ha,hb]
  exact mul_assoc (a x) (b x) (v x)

private theorem circle_scaled_product
    (a b : C(AddCircle T, ℂ)) (v : CircleL2 T) (r s : ℂ) :
    circleMultiplyL2 T (a*(r • b)) (s • v) =
      (r*s) • circleMultiplyL2 T a (circleMultiplyL2 T b v) := by
  rw [mul_smul_comm]
  change circleCoefficientMultiplyL2 T (r • (a*b)) (s • v) = _
  rw [(circleCoefficientMultiplyL2 T).map_smul,smul_apply,map_smul,smul_smul]
  rw [circle_coefficient_multiply_l2_apply,circle_product_associative]

private theorem spatial_graph_assembly_algebra
    (A : C(AddCircle T, ℂ)) (B : Fin 6 → C(AddCircle T, ℂ))
    (v : C(AddCircle T, ℂ)) (V W X : CircleL2 T) :
    circleCoefficientMultiplyL2 T A ((4:ℂ) • X)+
        circleContinuousL2 T (B 0)+
        circleMultiplyL2 T (B 1) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 2*((2:ℂ) • v)) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 3*((2:ℂ) • v)^2) ((2:ℂ) • V)+
        circleMultiplyL2 T (B 4) (((2*Real.sqrt 2:ℝ):ℂ) • W)+
        circleMultiplyL2 T (B 5*((2:ℂ) • v)) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      timeGraphAssembly (circleCoefficientMultiplyL2 T)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) (A,B)
        ![X,V,circleMultiplyL2 T v V,circleMultiplyL2 T (v^2) V,
          W,circleMultiplyL2 T v W] := by
  have hlead : circleCoefficientMultiplyL2 T A ((4:ℂ) • X) =
      (4:ℂ) • circleMultiplyL2 T A X := (circleMultiplyL2 T A).map_smul 4 X
  have hlinear : circleMultiplyL2 T (B 1) ((2:ℂ) • V) =
      (2:ℂ) • circleMultiplyL2 T (B 1) V := (circleMultiplyL2 T (B 1)).map_smul 2 V
  have hquadratic : circleMultiplyL2 T (B 2*((2:ℂ) • v)) ((2:ℂ) • V) =
      (4:ℂ) • circleMultiplyL2 T (B 2) (circleMultiplyL2 T v V) := by
    simpa only [show (2:ℂ)*2=4 by norm_num] using circle_scaled_product T (B 2) v V 2 2
  have hcubic : circleMultiplyL2 T (B 3*((2:ℂ) • v)^2) ((2:ℂ) • V) =
      (8:ℂ) • circleMultiplyL2 T (B 3) (circleMultiplyL2 T (v^2) V) := by
    rw [smul_pow,circle_scaled_product]
    norm_num
  have hthird : circleMultiplyL2 T (B 4) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      ((2*Real.sqrt 2:ℝ):ℂ) • circleMultiplyL2 T (B 4) W :=
    (circleMultiplyL2 T (B 4)).map_smul ((2*Real.sqrt 2:ℝ):ℂ) W
  have hmixed : circleMultiplyL2 T (B 5*((2:ℂ) • v)) (((2*Real.sqrt 2:ℝ):ℂ) • W) =
      ((2:ℂ)*((2*Real.sqrt 2:ℝ):ℂ)) •
        circleMultiplyL2 T (B 5) (circleMultiplyL2 T v W) :=
    circle_scaled_product T (B 5) v W 2 ((2*Real.sqrt 2:ℝ):ℂ)
  rw [hlead,hlinear,hquadratic,hcubic,hthird,hmixed]
  simp only [timeGraphAssembly,timeGraphCoefficient,timeGraphWeights,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_zero',Matrix.cons_val_succ',Function.comp_apply,add_zero,
    circle_coefficient_multiply_l2_apply,circleContinuousL2]
  ac_rfl

private theorem transfer_spatial_representation {X Z Y : Type*}
    (p : X → Y) (q : X → Z → Y) (a b : X) (v w : Z) (y : Y)
    (hp : y=p a) (hab : a=b) (halg : p b=q b v) (hv : v=w) : y=q b w :=
  hp.trans ((congrArg p hab).trans (halg.trans (congrArg (q b) hv)))

set_option maxHeartbeats 600000 in
private theorem spatial_graph_assembly
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 4) (hf : f ∈ circleNormalGraphDomain T K) :
    let u := circleNormalGraphLowCoordinates T
      (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))
    circleNormalGraphFlow T K c f =
      timeGraphAssembly (circleCoefficientMultiplyL2 T)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
        (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0],
          normalGraphLowerCoefficientMap T K c u) (spatialGraphProducts T f) := by
  let u := circleNormalGraphLowCoordinates T
    (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))
  have hp := circle_normal_graph_flow_polynomial T K c f hf
  dsimp only at hp
  have h₀ : circleNormalGraphCoordinates T f 0 = u 0 :=
    circle_normal_graph_coordinates_low T f 0
  have h₁ : circleNormalGraphCoordinates T f 1 = u 1 :=
    circle_normal_graph_coordinates_low T f 1
  have hprincipal : normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f) =
      normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0] := by
    change -(Ring.inverse ((1-K.k*(circleNormalGraphCoordinates T f 0))^2+
      (circleNormalGraphCoordinates T f 1)^2))^2 =
      -(Ring.inverse ((1-K.k*u 0)^2+(u 1)^2))^2
    rw [h₀,h₁]
  let B := normalGraphLowerCoefficientMap T K c u
  let v := circleSobolevContinuousJet T f 2
  let V := circleSobolevCoordinate T 4 2 f
  let W := circleSobolevCoordinate T 4 3 f
  let X := circleSobolevCoordinate T 4 4 f
  let raw : C(AddCircle T, ℂ) → CircleL2 T := fun A =>
    circleCoefficientMultiplyL2 T A ((4:ℂ) • X)+circleContinuousL2 T (B 0)+
      circleMultiplyL2 T (B 1) ((2:ℂ) • V)+
      circleMultiplyL2 T (B 2*((2:ℂ) • v)) ((2:ℂ) • V)+
      circleMultiplyL2 T (B 3*((2:ℂ) • v)^2) ((2:ℂ) • V)+
      circleMultiplyL2 T (B 4) (((2*Real.sqrt 2:ℝ):ℂ) • W)+
      circleMultiplyL2 T (B 5*((2:ℂ) • v)) (((2*Real.sqrt 2:ℝ):ℂ) • W)
  let assembled : C(AddCircle T, ℂ) → (Fin 6 → CircleL2 T) → CircleL2 T :=
    fun A z => timeGraphAssembly (circleCoefficientMultiplyL2 T)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ) (A,B) z
  let products : Fin 6 → CircleL2 T :=
    ![X,V,circleMultiplyL2 T v V,circleMultiplyL2 T (v^2) V,
      W,circleMultiplyL2 T v W]
  have hpraw : circleNormalGraphFlow T K c f =
      raw (normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f)) := by
    dsimp only [raw,u,B,v,V,W,X]
    exact hp
  have ha : raw (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0]) =
      assembled (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0]) products :=
    spatial_graph_assembly_algebra T
      (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0]) B v V W X
  have hproducts : products = spatialGraphProducts T f := by
    dsimp only [products,spatialGraphProducts,v,V,W,X]
  change circleNormalGraphFlow T K c f =
    assembled (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0]) (spatialGraphProducts T f)
  exact transfer_spatial_representation raw assembled
    (normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f))
    (normalGraphPrincipalCoefficient T K ![u 0,u 1,0,0]) products
    (spatialGraphProducts T f) (circleNormalGraphFlow T K c f) hpraw hprincipal ha hproducts

set_option maxHeartbeats 800000 in
/-- Almost every time slice is the already defined spatial normal-graph
equation, with its genuine H4 representative and the restricted background. -/
theorem circle_parabolic_normal_graph_flow_ae (c : ℝ)
    (a : Fin 6 → CircleTimeCoefficient T) (U : CircleParabolicSpace T τ)
    (hU : (a,U) ∈ circleParabolicNormalGraphDomain T τ) :
    (circleParabolicNormalGraphFlow T τ c (a,U) : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => circleNormalGraphFlow T (circleTimeNormalGraphBackground T a t) c
        (circleParabolicH4 T τ U t) := by
  let low := circleParabolicLowCoordinates T τ U
  let J := normalGraphJointCoefficientMapOver (CircleTimeCoefficient T) c (a,low)
  have hunit : (a,low) ∈ normalGraphJointCoefficientDomainOver (CircleTimeCoefficient T) := by
    change (a,low) ∈ normalGraphJointCoefficientDomainOver (CircleTimeCoefficient T) at hU
    exact hU
  obtain ⟨_,_,hB,hC,hD,_⟩ := circle_parabolic_product_bounds T τ
  have hd₂ : (fun _ : Fin 2 => U) = ![U,U] := by funext i; fin_cases i <;> rfl
  have hd₃ : (fun _ : Fin 3 => U) = ![U,U,U] := by funext i; fin_cases i <;> rfl
  have h₄ := (circleSobolevCoordinate T 4 4).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have h₂ := (circleSobolevCoordinate T 4 2).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have h₃ := (circleSobolevCoordinate T 4 3).coeFn_compLpL
    (p := 2) (μ := (volume : Measure unitInterval)) (circleParabolicH4 T τ U)
  have hassembly := time_graph_assembly_ae T J (parabolicGraphProducts T τ U)
  filter_upwards [circle_parabolic_h2_h4_ae T τ U,h₄,h₂,h₃,hB U U,hC U U U,hD U U,
    hassembly] with t ht h4 h2 h3 hB' hC' hD' ha
  let f := circleParabolicH4 T τ U t
  let K := circleTimeNormalGraphBackground T a t
  let v : Fin 2 → C(AddCircle T, ℂ) := fun i => (low i).curry t
  have hv : v = circleNormalGraphLowCoordinates T
      (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) := by
    funext i
    apply ContinuousMap.ext
    intro x
    change circleParabolicLowCoordinates T τ U i (t,x) = _
    rw [circle_parabolic_low_coordinates_apply,ht]
  have hd := joint_domain_algebra_map (circleTimeCoefficientRestriction T t) a low hunit
  have hf : f ∈ circleNormalGraphDomain T K := by
    apply (circle_normal_graph_domain_iff_low T K f).mpr
    rw [← hv]
    exact hd
  have hJ := joint_coefficients_algebra_map (circleTimeCoefficientRestriction T t) a low c hunit
  have hJ' : (normalGraphPrincipalCoefficient T K ![v 0,v 1,0,0],
      normalGraphLowerCoefficientMap T K c v) =
      ((J.1).curry t,fun i => (J.2 i).curry t) := hJ
  have hprod : (fun i => parabolicGraphProducts T τ U i t) = spatialGraphProducts T f := by
    funext i
    fin_cases i
    · exact h4
    · exact h2
    · simpa only [parabolicGraphProducts,timeGraphProducts,spatialGraphProducts,hd₂,
        Matrix.cons_val_zero',Matrix.cons_val_succ'] using! hB'
    · simpa only [parabolicGraphProducts,timeGraphProducts,spatialGraphProducts,hd₃,
        Matrix.cons_val_zero',Matrix.cons_val_succ',pow_two] using! hC'
    · exact h3
    · simpa only [parabolicGraphProducts,timeGraphProducts,spatialGraphProducts,hd₂,
        Matrix.cons_val_zero',Matrix.cons_val_succ'] using! hD'
  have hsp := spatial_graph_assembly T K c f hf
  dsimp only at hsp
  rw [← hv,hJ'] at hsp
  change circleParabolicNormalGraphFlow T τ c (a,U) t = _
  exact ha.trans ((congrArg (fun w : Fin 6 → CircleL2 T =>
    timeGraphAssembly (circleCoefficientMultiplyL2 T)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
      ((J.1).curry t,fun i => (J.2 i).curry t) w) hprod).trans hsp.symm)

end Lemniscate
