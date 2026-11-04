import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicParabolicEstimates
import Lemniscate.PeriodicSobolevProducts
import Lemniscate.PeriodicCoefficientAlgebra
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Algebra.BigOperators.Pi

/-! Actual derivative products on the parabolic solution space. A private
finite multilinear lift handles all three products with the same measurable
H4 representatives. Mixed spatial H2-H4 estimates supply the time-L2 bound;
no continuity of the H4 component in time is required.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal BigOperators Topology

private theorem finite_lp_pi_measurable {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] {n : ℕ}
    (w : Fin n → Lp F 2 (volume : Measure unitInterval)) :
    AEStronglyMeasurable (fun t : unitInterval => fun i => w i t)
      (volume : Measure unitInterval) := by
  classical
  have hs := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
    (fun i _ =>
      (ContinuousLinearMap.single ℂ (fun _ : Fin n => F) i).continuous.comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable
        (w i)))
  apply hs.congr
  filter_upwards with t
  rw [Finset.sum_apply]
  exact Finset.univ_sum_single (fun i => w i t)

set_option maxHeartbeats 800000 in
private theorem lp_multilinear_mixed_mem_bound
    {E F Y G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (Q : E →L[ℂ] Lp F 2 (volume : Measure unitInterval))
    (cmap : E →L[ℂ] C(unitInterval,Y)) (S : F →L[ℂ] Y)
    (hcomponent : ∀ x : E, ‖cmap x‖ ≤ ‖x‖ ∧ ‖Q x‖ ≤ ‖x‖)
    (hinc : ∀ x : E, ∀ᵐ t ∂(volume : Measure unitInterval), cmap x t = S (Q x t))
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => F) G)
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i, ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖S (f j)‖)
    (U : Fin n → E) :
    ∃ hm : MemLp (fun t : unitInterval => P (fun i => Q (U i) t))
        2 (volume : Measure unitInterval),
      ‖hm.toLp (fun t => P (fun i => Q (U i) t))‖ ≤
        (K*n)*∏ i, ‖U i‖ := by
  classical
  let w : Fin n → Lp F 2 (volume : Measure unitInterval) := fun i => Q (U i)
  let c : Fin n → C(unitInterval, Y) :=
    fun i => cmap (U i)
  let a : Fin n → ℝ := fun i => K*∏ j ∈ Finset.univ.erase i, ‖c j‖
  let b : Fin n → unitInterval → ℝ := fun i t => a i*‖w i t‖
  have ha (i : Fin n) : 0 ≤ a i := by dsimp only [a]; positivity
  have hb (i : Fin n) : MemLp (b i) 2 (volume : Measure unitInterval) :=
    (Lp.memLp (w i)).norm.const_mul (a i)
  have hB : MemLp (fun t => ∑ i, b i t) 2 (volume : Measure unitInterval) :=
    memLp_finsetSum Finset.univ (fun i _ => hb i)
  have hinc : ∀ᵐ t ∂(volume : Measure unitInterval),
      ∀ i, c i t = S (w i t) :=
    ae_all_iff.mpr (fun i => hinc (U i))
  have hpoint : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖P (fun i => w i t)‖ ≤ ∑ i, b i t := by
    filter_upwards [hinc] with t ht
    have hlow (i : Fin n) : ‖S (w i t)‖ ≤ ‖c i‖ := by
      have heq := congrArg (fun z : Y => ‖z‖) (ht i).symm
      exact heq.le.trans ((c i).norm_coe_le_norm t)
    calc
      ‖P (fun i => w i t)‖ ≤ K*∑ i,
          ‖w i t‖*∏ j ∈ Finset.univ.erase i, ‖S (w j t)‖ := hP _
      _ ≤ K*∑ i, ‖w i t‖*∏ j ∈ Finset.univ.erase i, ‖c j‖ := by
        apply mul_le_mul_of_nonneg_left _ hK
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hlow j))
          (norm_nonneg _)
      _ = ∑ i, b i t := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [b,a]
        ring
  have hmeas := P.cont.comp_aestronglyMeasurable (finite_lp_pi_measurable (fun i => Q (U i)))
  have hm : MemLp (fun t : unitInterval => P (fun i => w i t)) 2 volume :=
    hB.mono' hmeas hpoint
  refine ⟨hm,?_⟩
  have hmono : eLpNorm (fun t => P (fun i => w i t)) 2 volume ≤
      eLpNorm (fun t => ∑ i, b i t) 2 volume :=
    eLpNorm_mono_ae (hpoint.mono fun t ht => ht.trans (le_abs_self _))
  have hterm (i : Fin n) : lpNorm (b i) 2 volume = a i*‖w i‖ := by
    change lpNorm ((a i) • (fun t => ‖w i t‖)) 2 volume = _
    rw [lpNorm_const_smul,lpNorm_norm (Lp.aestronglyMeasurable (w i)),
      ← toReal_eLpNorm (Lp.aestronglyMeasurable (w i))]
    change ‖a i‖*‖w i‖ = a i*‖w i‖
    rw [Real.norm_eq_abs,abs_of_nonneg (ha i)]
  calc
    ‖hm.toLp (fun t => P (fun i => w i t))‖ =
        (eLpNorm (fun t => P (fun i => w i t)) 2 volume).toReal := Lp.norm_toLp _ _
    _ ≤ (eLpNorm (fun t => ∑ i, b i t) 2 volume).toReal :=
      ENNReal.toReal_mono hB.eLpNorm_ne_top hmono
    _ = lpNorm (fun t => ∑ i, b i t) 2 volume := toReal_eLpNorm hB.aestronglyMeasurable
    _ ≤ ∑ i, lpNorm (b i) 2 volume := by
      have heq : (fun t => ∑ i, b i t) = ∑ i, b i := by
        funext t
        simp only [Finset.sum_apply]
      rw [heq]
      exact lpNorm_sum_le (s := Finset.univ) (fun i _ => hb i)
        (by norm_num : (1:ℝ≥0∞) ≤ 2)
    _ = ∑ i, a i*‖w i‖ := Finset.sum_congr rfl (fun i _ => hterm i)
    _ ≤ ∑ _i : Fin n, K*∏ j, ‖U j‖ := by
      apply Finset.sum_le_sum
      intro i _
      have hcj (j : Fin n) : ‖c j‖ ≤ ‖U j‖ := (hcomponent (U j)).1
      have hwi : ‖w i‖ ≤ ‖U i‖ := (hcomponent (U i)).2
      have hp : (∏ j ∈ Finset.univ.erase i, ‖c j‖) ≤
          ∏ j ∈ Finset.univ.erase i, ‖U j‖ :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hcj j)
      calc
        a i*‖w i‖ ≤ (K*∏ j ∈ Finset.univ.erase i, ‖U j‖)*‖U i‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hp hK) hwi (norm_nonneg _) (by positivity)
        _ = K*∏ j, ‖U j‖ := by
          rw [mul_assoc,Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    _ = (K*n)*∏ i, ‖U i‖ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

set_option maxHeartbeats 800000 in
private def lpPointwiseMultilinear
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (Q : E →L[ℂ] Lp F 2 (volume : Measure unitInterval))
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => F) G)
    (hm : ∀ U : Fin n → E,
      MemLp (fun t : unitInterval => P (fun i => Q (U i) t)) 2
        (volume : Measure unitInterval)) :
    MultilinearMap ℂ (fun _ : Fin n => E)
      (Lp G 2 (volume : Measure unitInterval)) where
  toFun U := (hm U).toLp _
  map_update_add' U i x y := by
    classical
    have ha : (Q (x+y) : unitInterval → F)
        =ᵐ[volume] fun t => Q x t+Q y t := by
      have hmap : Q (x+y) =
          Q x+Q y := by
        simpa only using! (Q).map_add x y
      filter_upwards [Lp.coeFn_add (Q x) (Q y)] with t ht
      have hEval := congrArg (fun q : Lp F 2 (volume : Measure unitInterval) => q t) hmap
      exact hEval.trans (by simpa only [Pi.add_apply] using! ht)
    apply Lp.ext
    filter_upwards [(hm (Function.update U i (x+y))).coeFn_toLp,
      (hm (Function.update U i x)).coeFn_toLp,(hm (Function.update U i y)).coeFn_toLp,
      Lp.coeFn_add ((hm (Function.update U i x)).toLp _)
        ((hm (Function.update U i y)).toLp _),ha] with t hxy hx hy hs ht
    simp only [Pi.add_apply] at hs
    rw [hxy,hs,hx,hy]
    have hupdate (z : E) :
        (fun j => Q (Function.update U i z j) t) =
          Function.update (fun j => Q (U j) t) i
            (Q z t) := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [hupdate,hupdate,hupdate,ht,P.map_update_add]
  map_update_smul' U i a x := by
    classical
    have ha : (Q (a • x) : unitInterval → F)
        =ᵐ[volume] fun t => a • Q x t := by
      have hmap : Q (a • x) = a • Q x := by
        simpa only using! (Q).map_smul a x
      filter_upwards [Lp.coeFn_smul a (Q x)] with t ht
      have hEval := congrArg (fun q : Lp F 2 (volume : Measure unitInterval) => q t) hmap
      exact hEval.trans (by simpa only [Pi.smul_apply] using! ht)
    apply Lp.ext
    filter_upwards [(hm (Function.update U i (a • x))).coeFn_toLp,
      (hm (Function.update U i x)).coeFn_toLp,
      Lp.coeFn_smul a ((hm (Function.update U i x)).toLp _),ha] with t hax hx hs ht
    simp only [Pi.smul_apply] at hs
    rw [hax,hs,hx]
    have hupdate (z : E) :
        (fun j => Q (Function.update U i z j) t) =
          Function.update (fun j => Q (U j) t) i
            (Q z t) := by
      funext j
      by_cases hji : j = i <;> simp [hji]
    rw [hupdate,hupdate,ht,P.map_update_smul]

section GenericLift
variable {E F Y G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup G] [NormedSpace ℂ G] {n : ℕ}
    (Q : E →L[ℂ] Lp F 2 (volume : Measure unitInterval))
    (cmap : E →L[ℂ] C(unitInterval,Y)) (S : F →L[ℂ] Y)
    (hcomponent : ∀ x : E, ‖cmap x‖ ≤ ‖x‖ ∧ ‖Q x‖ ≤ ‖x‖)
    (hinc : ∀ x : E, ∀ᵐ t ∂(volume : Measure unitInterval), cmap x t = S (Q x t))
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => F) G)
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i, ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖S (f j)‖)

private def lpMixedMultilinear :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => E) (Lp G 2 (volume : Measure unitInterval)) :=
  (lpPointwiseMultilinear (E := E) (F := F) (G := G) (n := n) Q P
    (fun U => (lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose)).mkContinuous (K*n)
        (fun U => (lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose_spec)

private theorem lp_mixed_multilinear_ae (U : Fin n → E) :
    (lpMixedMultilinear Q cmap S hcomponent hinc P K hK hP U : unitInterval → G) =ᵐ[volume]
      fun t => P (fun i => Q (U i) t) := by
  change (((lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose).toLp
    (fun t => P (fun i => Q (U i) t)) : unitInterval → G) =ᵐ[volume]
      fun t => P (fun i => Q (U i) t)
  exact MemLp.coeFn_toLp
    (lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose

private theorem lp_mixed_multilinear_norm (U : Fin n → E) :
    ‖lpMixedMultilinear Q cmap S hcomponent hinc P K hK hP U‖ ≤ (K*n)*∏ i, ‖U i‖ := by
  change ‖((lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose).toLp
    (fun t => P (fun i => Q (U i) t))‖ ≤ _
  exact (lp_multilinear_mixed_mem_bound Q cmap S hcomponent hinc P K hK hP U).choose_spec

include hcomponent hinc hK hP in
/-- Keep the concrete measurable-representative construction behind an
opaque proposition before specializing the ambient Banach spaces. -/
private theorem exists_lp_mixed_multilinear :
    ∃ L : ContinuousMultilinearMap ℂ (fun _ : Fin n => E)
        (Lp G 2 (volume : Measure unitInterval)),
      (∀ U : Fin n → E, (L U : unitInterval → G) =ᵐ[volume]
        fun t => P (fun i => Q (U i) t)) ∧
      ∀ U : Fin n → E, ‖L U‖ ≤ (K*n)*∏ i, ‖U i‖ := by
  refine ⟨lpMixedMultilinear Q cmap S hcomponent hinc P K hK hP,?_,?_⟩
  · exact lp_mixed_multilinear_ae Q cmap S hcomponent hinc P K hK hP
  · exact lp_mixed_multilinear_norm Q cmap S hcomponent hinc P K hK hP

end GenericLift

set_option maxHeartbeats 800000 in
private def composeBilinearFinite
    {X A B G : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (M : A →L[ℂ] B →L[ℂ] G) (p : X →L[ℂ] A) (q : X →L[ℂ] B) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 2 => X) G where
  toFun f := M (p (f 0)) (q (f 1))
  map_update_add' f i x y := by
    fin_cases i <;> simp [map_add,ContinuousLinearMap.add_apply]
  map_update_smul' f i a x := by
    fin_cases i <;> simp [map_smul,ContinuousLinearMap.smul_apply]
  cont := M.isBoundedBilinearMap.continuous.comp
    ((p.continuous.comp (continuous_apply 0)).prodMk
      (q.continuous.comp (continuous_apply 1)))

set_option maxHeartbeats 800000 in
private def composeTrilinearFinite
    {X A B G : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup A] [NormedSpace ℂ A]
    [NormedAddCommGroup B] [NormedSpace ℂ B]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (M : A →L[ℂ] B →L[ℂ] G) (mulA : A →L[ℂ] A →L[ℂ] A)
    (p : X →L[ℂ] A) (q : X →L[ℂ] B) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 3 => X) G :=
  let L : A →L[ℂ] X →L[ℂ] G :=
    ((ContinuousLinearMap.compL ℂ X B G).flip q).comp M
  let H : ContinuousMultilinearMap ℂ (fun _ : Fin 2 => X) (X →L[ℂ] G) :=
    L.compContinuousMultilinearMap
      (composeBilinearFinite (X := X) (A := A) (B := A) (G := A) mulA p p)
  H.uncurryRight

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private def parabolicH2Inclusion :
    CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
  (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)

private theorem parabolic_component_norms (U : CircleParabolicSpace T τ) :
    ‖circleParabolicCurve T τ U‖ ≤ ‖U‖ ∧ ‖circleParabolicH4 T τ U‖ ≤ ‖U‖ := by
  change ‖U.1.1‖ ≤ ‖U.1‖ ∧ ‖U.1.2.1‖ ≤ ‖U.1‖
  exact ⟨norm_fst_le _,(norm_fst_le U.1.2).trans (norm_snd_le U.1)⟩

private theorem parabolic_h4_h2_ae (U : CircleParabolicSpace T τ) :
    ∀ᵐ t ∂(volume : Measure unitInterval),
      circleParabolicCurve T τ U t = parabolicH2Inclusion T (circleParabolicH4 T τ U t) := by
  simpa only [parabolicH2Inclusion,ContinuousLinearMap.comp_apply] using!
    circle_parabolic_h2_h4_ae T τ U

set_option maxHeartbeats 800000 in
private theorem exists_parabolic_product_lift {n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => CircleSobolevSpace T 4) (CircleL2 T))
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i,
      ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f j)‖) :
    ∃ L : ContinuousMultilinearMap ℂ
        (fun _ : Fin n => CircleParabolicSpace T τ) (CircleTimeL2 T),
      (∀ U : Fin n → CircleParabolicSpace T τ,
        (L U : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => P (fun i => circleParabolicH4 T τ (U i) t)) ∧
      ∀ U : Fin n → CircleParabolicSpace T τ, ‖L U‖ ≤ (K*n)*∏ i, ‖U i‖ := by
  simpa only using! exists_lp_mixed_multilinear
    (E := ↥(CircleParabolicSpace T τ)) (F := ↥(CircleSobolevSpace T 4))
    (Y := ↥(CircleSobolevSpace T 2)) (G := ↥(CircleL2 T)) (n := n)
    (circleParabolicH4 T τ) (circleParabolicCurve T τ) (parabolicH2Inclusion T)
    (fun U => by simpa only using! parabolic_component_norms T τ U)
    (fun U => by simpa only using! parabolic_h4_h2_ae T τ U) P K hK
    (fun f => by simpa only using! hP f)

private def parabolicProductLift {n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => CircleSobolevSpace T 4) (CircleL2 T))
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i,
      ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f j)‖) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => CircleParabolicSpace T τ) (CircleTimeL2 T) :=
  (exists_parabolic_product_lift T τ P K hK hP).choose

set_option maxHeartbeats 800000 in
private theorem parabolic_product_lift_ae {n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => CircleSobolevSpace T 4) (CircleL2 T))
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i,
      ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f j)‖)
    (U : Fin n → CircleParabolicSpace T τ) :
    (parabolicProductLift T τ P K hK hP U : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => P (fun i => circleParabolicH4 T τ (U i) t) :=
  (exists_parabolic_product_lift T τ P K hK hP).choose_spec.1 U

set_option maxHeartbeats 800000 in
private theorem parabolic_product_lift_norm {n : ℕ}
    (P : ContinuousMultilinearMap ℂ (fun _ : Fin n => CircleSobolevSpace T 4) (CircleL2 T))
    (K : ℝ) (hK : 0 ≤ K)
    (hP : ∀ f, ‖P f‖ ≤ K*∑ i,
      ‖f i‖*∏ j ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f j)‖)
    (U : Fin n → CircleParabolicSpace T τ) :
    ‖parabolicProductLift T τ P K hK hP U‖ ≤ (K*n)*∏ i, ‖U i‖ :=
  (exists_parabolic_product_lift T τ P K hK hP).choose_spec.2 U

private def productSecondCoordinate :
    CircleSobolevSpace T 4 →L[ℂ] C(AddCircle T, ℂ) :=
  (ContinuousLinearMap.proj (2 : Fin 4)).comp (circleSobolevContinuousJet T)

set_option maxHeartbeats 800000 in
private def spatialSecondProduct (j : Fin 5) :
    ContinuousMultilinearMap ℂ (fun _ : Fin 2 => CircleSobolevSpace T 4) (CircleL2 T) := by
  simpa only using! composeBilinearFinite
    (X := ↥(CircleSobolevSpace T 4)) (A := C(AddCircle T, ℂ))
    (B := CircleL2 T) (G := CircleL2 T)
    (circleCoefficientMultiplyL2 T) (productSecondCoordinate T) (circleSobolevCoordinate T 4 j)

set_option maxHeartbeats 800000 in
private def spatialCubicSecondProduct :
    ContinuousMultilinearMap ℂ (fun _ : Fin 3 => CircleSobolevSpace T 4) (CircleL2 T) := by
  simpa only using! composeTrilinearFinite
    (X := ↥(CircleSobolevSpace T 4)) (A := C(AddCircle T, ℂ))
    (B := CircleL2 T) (G := CircleL2 T)
    (circleCoefficientMultiplyL2 T) (ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ))
    (productSecondCoordinate T) (circleSobolevCoordinate T 4 2)

private def parabolicProductConstant : ℝ := (circle_sobolev_second_product_bounds T).choose

private theorem real_mixed_two_reorder (k a b c d : ℝ) :
    k*(a*b+c*d) = k*(d*c+b*a) := by ring

private theorem real_mixed_two_padding (k a b c d : ℝ) (h : 0 ≤ k*c*d) :
    k*a*b ≤ k*(a*b+c*d) := by linear_combination h

private theorem real_mixed_three_padding (k a b c d e f : ℝ) (h : 0 ≤ k*f*a*c) :
    k*(a*b+c*d)*e ≤ k*(d*(c*e)+b*(a*e)+f*(a*c)) := by linear_combination h

private theorem real_three_scale (k a b c : ℝ) :
    (k*3)*(a*b*c) = (3*k)*a*b*c := by ring

set_option maxHeartbeats 800000 in
private theorem spatial_products_mixed :
    let K := parabolicProductConstant T
    (0 < K) ∧
    (∀ j : Fin 5, j = 2 ∨ j = 3 → ∀ f : Fin 2 → CircleSobolevSpace T 4,
      ‖spatialSecondProduct T j f‖ ≤ K*∑ i,
        ‖f i‖*∏ k ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f k)‖) ∧
    (∀ f : Fin 3 → CircleSobolevSpace T 4,
      ‖spatialCubicSecondProduct T f‖ ≤ K*∑ i,
        ‖f i‖*∏ k ∈ Finset.univ.erase i, ‖parabolicH2Inclusion T (f k)‖) := by
  obtain ⟨hK,hbound⟩ := (circle_sobolev_second_product_bounds T).choose_spec
  let K := parabolicProductConstant T
  have hK' : 0 < K := hK
  refine ⟨hK,?_,?_⟩
  · intro j hj f
    have he0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
    have he1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
    simp only [Fin.sum_univ_two,he0,he1,Finset.prod_singleton]
    rcases hj with rfl | rfl
    · have h := (hbound (f 0) (f 1) 0).1
      change ‖spatialSecondProduct T 2 f‖ ≤ K*‖f 0‖*‖parabolicH2Inclusion T (f 1)‖ at h
      have hp : 0 ≤ K*‖f 1‖*‖parabolicH2Inclusion T (f 0)‖ := by positivity
      exact h.trans (real_mixed_two_padding K ‖f 0‖
        ‖parabolicH2Inclusion T (f 1)‖ ‖f 1‖ ‖parabolicH2Inclusion T (f 0)‖ hp)
    · have h := (hbound (f 0) (f 1) 0).2.2
      change ‖spatialSecondProduct T 3 f‖ ≤
        K*(‖parabolicH2Inclusion T (f 0)‖*‖f 1‖+
          ‖parabolicH2Inclusion T (f 1)‖*‖f 0‖) at h
      exact h.trans (real_mixed_two_reorder K ‖parabolicH2Inclusion T (f 0)‖
        ‖f 1‖ ‖parabolicH2Inclusion T (f 1)‖ ‖f 0‖).le
  · intro f
    have he0 : (Finset.univ : Finset (Fin 3)).erase 0 = {1,2} := by decide
    have he1 : (Finset.univ : Finset (Fin 3)).erase 1 = {0,2} := by decide
    have he2 : (Finset.univ : Finset (Fin 3)).erase 2 = {0,1} := by decide
    rw [Fin.sum_univ_three,he0,he1,he2,
      Finset.prod_pair (by decide : (1 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 2),
      Finset.prod_pair (by decide : (0 : Fin 3) ≠ 1)]
    have h := (hbound (f 0) (f 1) (f 2)).2.1
    change ‖spatialCubicSecondProduct T f‖ ≤
      K*(‖parabolicH2Inclusion T (f 0)‖*‖f 1‖+
        ‖parabolicH2Inclusion T (f 1)‖*‖f 0‖)*‖parabolicH2Inclusion T (f 2)‖ at h
    have hp : 0 ≤ K*‖f 2‖*‖parabolicH2Inclusion T (f 0)‖*
        ‖parabolicH2Inclusion T (f 1)‖ := by positivity
    exact h.trans (real_mixed_three_padding K ‖parabolicH2Inclusion T (f 0)‖
      ‖f 1‖ ‖parabolicH2Inclusion T (f 1)‖ ‖f 0‖
      ‖parabolicH2Inclusion T (f 2)‖ ‖f 2‖ hp)

/-- The actual time-L2 product of the two second derivatives. -/
def circleParabolicSecondProduct :
    ContinuousMultilinearMap ℂ (fun _ : Fin 2 => CircleParabolicSpace T τ) (CircleTimeL2 T) :=
  parabolicProductLift T τ (spatialSecondProduct T 2) (parabolicProductConstant T)
    (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 2 (Or.inl rfl))

/-- The actual time-L2 product of three second derivatives. -/
def circleParabolicCubicSecondProduct :
    ContinuousMultilinearMap ℂ (fun _ : Fin 3 => CircleParabolicSpace T τ) (CircleTimeL2 T) :=
  parabolicProductLift T τ (spatialCubicSecondProduct T) (parabolicProductConstant T)
    (spatial_products_mixed T).1.le (spatial_products_mixed T).2.2

/-- The actual time-L2 product of a second and a third derivative. -/
def circleParabolicSecondThirdProduct :
    ContinuousMultilinearMap ℂ (fun _ : Fin 2 => CircleParabolicSpace T τ) (CircleTimeL2 T) :=
  parabolicProductLift T τ (spatialSecondProduct T 3) (parabolicProductConstant T)
    (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 3 (Or.inr rfl))

set_option maxHeartbeats 800000 in
/-- One positive constant bounds all three genuine multilinear products,
whose representatives are the indicated products of the actual H4 jets. -/
theorem circle_parabolic_product_bounds :
    ∃ K > 0,
      (∀ U V : CircleParabolicSpace T τ,
        (circleParabolicSecondProduct T τ ![U,V] : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => circleMultiplyL2 T
            (circleSobolevContinuousJet T (circleParabolicH4 T τ U t) 2)
            (circleSobolevCoordinate T 4 2 (circleParabolicH4 T τ V t))) ∧
      (∀ U V W : CircleParabolicSpace T τ,
        (circleParabolicCubicSecondProduct T τ ![U,V,W] : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => circleMultiplyL2 T
            (circleSobolevContinuousJet T (circleParabolicH4 T τ U t) 2*
              circleSobolevContinuousJet T (circleParabolicH4 T τ V t) 2)
            (circleSobolevCoordinate T 4 2 (circleParabolicH4 T τ W t))) ∧
      (∀ U V : CircleParabolicSpace T τ,
        (circleParabolicSecondThirdProduct T τ ![U,V] : unitInterval → CircleL2 T) =ᵐ[volume]
          fun t => circleMultiplyL2 T
            (circleSobolevContinuousJet T (circleParabolicH4 T τ U t) 2)
            (circleSobolevCoordinate T 4 3 (circleParabolicH4 T τ V t))) ∧
      ∀ U V W : CircleParabolicSpace T τ,
        ‖circleParabolicSecondProduct T τ ![U,V]‖ ≤ K*‖U‖*‖V‖ ∧
        ‖circleParabolicCubicSecondProduct T τ ![U,V,W]‖ ≤ K*‖U‖*‖V‖*‖W‖ ∧
        ‖circleParabolicSecondThirdProduct T τ ![U,V]‖ ≤ K*‖U‖*‖V‖ := by
  let K0 := parabolicProductConstant T
  let K : ℝ := 3*K0
  have hK0 : 0 < K0 := (spatial_products_mixed T).1
  have hK : 0 < K := mul_pos (by norm_num) hK0
  have htwo : K0*2 ≤ K := by dsimp only [K]; linear_combination hK0.le
  refine ⟨K,hK,?_,?_,?_,?_⟩
  · intro U V
    exact parabolic_product_lift_ae T τ (spatialSecondProduct T 2) (parabolicProductConstant T)
      (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 2 (Or.inl rfl)) ![U,V]
  · intro U V W
    exact parabolic_product_lift_ae T τ (spatialCubicSecondProduct T) (parabolicProductConstant T)
      (spatial_products_mixed T).1.le (spatial_products_mixed T).2.2 ![U,V,W]
  · intro U V
    exact parabolic_product_lift_ae T τ (spatialSecondProduct T 3) (parabolicProductConstant T)
      (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 3 (Or.inr rfl)) ![U,V]
  · intro U V W
    have hn2 : ((Nat.succ (Nat.succ 0) : ℕ) : ℝ) = 2 := by norm_num
    have hn3 : ((Nat.succ (Nat.succ (Nat.succ 0)) : ℕ) : ℝ) = 3 := by norm_num
    have hB := parabolic_product_lift_norm T τ (spatialSecondProduct T 2) K0
      (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 2 (Or.inl rfl)) ![U,V]
    have hC := parabolic_product_lift_norm T τ (spatialCubicSecondProduct T) K0
      (spatial_products_mixed T).1.le (spatial_products_mixed T).2.2 ![U,V,W]
    have hD := parabolic_product_lift_norm T τ (spatialSecondProduct T 3) K0
      (spatial_products_mixed T).1.le ((spatial_products_mixed T).2.1 3 (Or.inr rfl)) ![U,V]
    simp only [Fin.prod_univ_two,Fin.prod_univ_three,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,hn2,hn3] at hB hC hD
    refine ⟨hB.trans ?_,?_,hD.trans ?_⟩
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right htwo
        (by positivity : 0 ≤ ‖U‖*‖V‖)
    · exact hC.trans (real_three_scale K0 ‖U‖ ‖V‖ ‖W‖).le
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right htwo
        (by positivity : 0 ≤ ‖U‖*‖V‖)

end Lemniscate
