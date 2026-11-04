import Lemniscate.PeriodicParabolicEstimates
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! The pointwise H2-H4 tame estimate gives a genuine time-L2 Nemytskii
map on the H2-small part of the parabolic space. The H4 representative
need only be strongly measurable, and is never assumed continuous in time.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private def circleTimeH4Norm (w : CircleTimeH4 T) :
    Lp ℝ 2 (volume : Measure unitInterval) :=
  (Lp.memLp w).norm.toLp (fun t => ‖w t‖)

private theorem circle_time_h4_norm_ae (w : CircleTimeH4 T) :
    (circleTimeH4Norm T w : unitInterval → ℝ) =ᵐ[volume] fun t => ‖w t‖ :=
  MemLp.coeFn_toLp (Lp.memLp w).norm

private theorem circle_time_h4_norm_norm (w : CircleTimeH4 T) :
    ‖circleTimeH4Norm T w‖ = ‖w‖ := by
  rw [circleTimeH4Norm,Lp.norm_toLp,eLpNorm_norm]
  rfl

private theorem circle_time_two_term_bound (F : CircleTimeL2 T)
    (d u v : CircleTimeH4 T) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖F t‖ ≤ a*‖d t‖+b*(‖u t‖+‖v t‖)) :
    ‖F‖ ≤ a*‖d‖+b*(‖u‖+‖v‖) := by
  let nd := circleTimeH4Norm T d
  let nu := circleTimeH4Norm T u
  let nv := circleTimeH4Norm T v
  let W : Lp ℝ 2 (volume : Measure unitInterval) := a • nd+b • (nu+nv)
  have hW : (W : unitInterval → ℝ) =ᵐ[volume]
      fun t => a*‖d t‖+b*(‖u t‖+‖v t‖) := by
    filter_upwards [Lp.coeFn_add (a • nd) (b • (nu+nv)),
      Lp.coeFn_smul a nd,Lp.coeFn_smul b (nu+nv),Lp.coeFn_add nu nv,
      circle_time_h4_norm_ae T d,circle_time_h4_norm_ae T u,
      circle_time_h4_norm_ae T v] with t hsum hsa hsb huv hd hu hv
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hsum hsa hsb huv
    change (a • nd+b • (nu+nv)) t = _
    rw [hsum,hsa,hsb,huv,hd,hu,hv]
  have hFW : ‖F‖ ≤ ‖W‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h,hW] with t ht hWt
    rw [hWt,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact ht
  calc
    ‖F‖ ≤ ‖W‖ := hFW
    _ ≤ ‖a • nd‖+‖b • (nu+nv)‖ := norm_add_le _ _
    _ = a*‖nd‖+b*‖nu+nv‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_nonneg ha,abs_of_nonneg hb]
    _ ≤ a*‖nd‖+b*(‖nu‖+‖nv‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le nu nv) hb)
    _ = a*‖d‖+b*(‖u‖+‖v‖) := by
      rw [circle_time_h4_norm_norm,circle_time_h4_norm_norm,circle_time_h4_norm_norm]

private theorem circle_parabolic_h2_h4_norm_ae (U : CircleParabolicSpace T τ) :
    ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖circleSobolevInclusion T 2
        (circleSobolevInclusion T 3 (circleParabolicH4 T τ U t))‖ ≤
          ‖circleParabolicCurve T τ U‖ := by
  let E : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let c : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ U
  let w : CircleTimeH4 T := circleParabolicH4 T τ U
  have hinc : ∀ᵐ t ∂(volume : Measure unitInterval), c t = E (w t) :=
    circle_parabolic_h2_h4_ae T τ U
  change ∀ᵐ t ∂(volume : Measure unitInterval), ‖E (w t)‖ ≤ ‖c‖
  filter_upwards [hinc] with t ht
  have hn : ‖E (w t)‖ = ‖c t‖ :=
    congrArg (fun z : CircleSobolevSpace T 2 => ‖z‖) ht.symm
  exact hn.le.trans (c.norm_coe_le_norm t)

variable {δ C : ℝ} {N : CircleSobolevSpace T 4 → CircleL2 T}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hN0 : N 0 = 0)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖))

include htame in
private theorem circle_nonlinear_tame_continuous :
    ContinuousOn N {f : CircleSobolevSpace T 4 |
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ} := by
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let D : Set (CircleSobolevSpace T 4) := {f | ‖S f‖ < δ}
  intro f hf
  let Q : CircleSobolevSpace T 4 → ℝ := fun g =>
    C*((‖S g‖+‖S f‖)*‖g-f‖+(‖g‖+‖f‖)*‖S (g-f)‖)
  have hQ : Continuous Q := by
    dsimp only [Q]
    fun_prop
  have hQzero : Q f = 0 := by
    simp only [Q,sub_self,map_zero,norm_zero,mul_zero,add_zero]
  have hlim' : Tendsto Q (𝓝 f) (𝓝 (Q f)) := hQ.continuousAt
  have hlim : Tendsto Q (𝓝[D] f) (𝓝 0) := by
    simpa only [hQzero] using hlim'.mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ g in 𝓝[D] f, ‖N g-N f‖ ≤ Q g := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    exact htame g f hg hf
  change Tendsto N (𝓝[D] f) (𝓝 (N f))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Eventually.of_forall fun g => norm_nonneg (N g-N f)) hbound hlim

include hδ hC hN0 htame

set_option maxHeartbeats 800000 in
private theorem circle_parabolic_nonlinear_memLp (U : CircleParabolicSpace T τ)
    (hU : ‖circleParabolicCurve T τ U‖ < δ) :
    MemLp (fun t => N (circleParabolicH4 T τ U t)) 2
      (volume : Measure unitInterval) := by
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let D : Set (CircleSobolevSpace T 4) := {f | ‖S f‖ < δ}
  let w : CircleTimeH4 T := circleParabolicH4 T τ U
  have hinc : ∀ᵐ t ∂(volume : Measure unitInterval),
      circleParabolicCurve T τ U t = S (w t) :=
    circle_parabolic_h2_h4_ae T τ U
  have hmem : ∀ᵐ t ∂(volume : Measure unitInterval), w t ∈ D := by
    filter_upwards [hinc] with t ht
    change ‖S (w t)‖ < δ
    rw [← ht]
    exact lt_of_le_of_lt ((circleParabolicCurve T τ U).norm_coe_le_norm t) hU
  have hzero : (0 : CircleSobolevSpace T 4) ∈ D := by
    simpa only [D,mem_setOf_eq,map_zero,norm_zero] using hδ
  have hmeas : AEStronglyMeasurable (fun t => N (w t))
      (volume : Measure unitInterval) := by
    borelize ↥(CircleSobolevSpace T 4)
    have hopen : IsOpen D := isOpen_Iio.preimage S.continuous.norm
    obtain ⟨g,hg,hgD,hweq⟩ :=
      (Lp.aestronglyMeasurable w).exists_stronglyMeasurable_range_subset
        hopen.measurableSet ⟨0,hzero⟩ hmem
    let z : unitInterval → D := fun t => ⟨g t,hgD t⟩
    have hz : StronglyMeasurable z := by
      apply (Embedding.comp_stronglyMeasurable_iff
        (g := ((↑) : D → CircleSobolevSpace T 4))
        Topology.IsEmbedding.subtypeVal).mp
      exact hg
    have hc : Continuous (fun f : D => N f.1) :=
      (circle_nonlinear_tame_continuous T htame).domRestrict
    refine ⟨fun t => N (z t).1,hc.comp_stronglyMeasurable hz,?_⟩
    filter_upwards [hweq] with t ht
    exact congrArg N ht
  have hbound : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖N (w t)‖ ≤ (2*C*‖circleParabolicCurve T τ U‖)*‖w t‖ := by
    filter_upwards [hinc,hmem] with t ht hm
    have hh := htame (w t) 0 hm hzero
    simp only [hN0,map_zero,norm_zero,add_zero,sub_zero] at hh
    have hnorm : ‖S (w t)‖ ≤ ‖circleParabolicCurve T τ U‖ := by
      rw [← ht]
      exact (circleParabolicCurve T τ U).norm_coe_le_norm t
    calc
      ‖N (w t)‖ ≤ C*(‖S (w t)‖*‖w t‖+‖w t‖*‖S (w t)‖) := hh
      _ = (2*C*‖S (w t)‖)*‖w t‖ := by ring
      _ ≤ (2*C*‖circleParabolicCurve T τ U‖)*‖w t‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (by positivity)) (norm_nonneg _)
  exact ((Lp.memLp w).norm.const_mul (2*C*‖circleParabolicCurve T τ U‖)).mono'
    hmeas hbound

/-- The time-L2 nonlinear term on the open H2-small part of the actual
parabolic space. Its definition uses the proved measurability and L2 bound. -/
def circleParabolicNemytskii
    (U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ}) :
    CircleTimeL2 T :=
  (circle_parabolic_nonlinear_memLp T τ hδ hC hN0 htame U.1 U.2).toLp
    (fun t => N (circleParabolicH4 T τ U.1 t))

omit hδ hN0 in
set_option maxHeartbeats 800000 in
private theorem circle_parabolic_time_tame_bound
    (U V : CircleParabolicSpace T τ)
    (hU : ‖circleParabolicCurve T τ U‖ < δ)
    (hV : ‖circleParabolicCurve T τ V‖ < δ)
    (F G : CircleTimeL2 T)
    (hF : (F : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => N (circleParabolicH4 T τ U t))
    (hG : (G : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => N (circleParabolicH4 T τ V t)) :
    ‖F-G‖ ≤ C*
      ((‖circleParabolicCurve T τ U‖+‖circleParabolicCurve T τ V‖)*
          ‖circleParabolicH4 T τ (U-V)‖+
        (‖circleParabolicH4 T τ U‖+‖circleParabolicH4 T τ V‖)*
          ‖circleParabolicCurve T τ (U-V)‖) := by
  let cu : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ U
  let cv : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ V
  let cd : C(unitInterval, CircleSobolevSpace T 2) := circleParabolicCurve T τ (U-V)
  let u : CircleTimeH4 T := circleParabolicH4 T τ U
  let v : CircleTimeH4 T := circleParabolicH4 T τ V
  let d : CircleTimeH4 T := circleParabolicH4 T τ (U-V)
  let a : ℝ := ‖cu‖+‖cv‖
  let b : ℝ := ‖cd‖
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  have hUae : ∀ᵐ t ∂(volume : Measure unitInterval), ‖S (u t)‖ ≤ ‖cu‖ :=
    circle_parabolic_h2_h4_norm_ae T τ U
  have hVae : ∀ᵐ t ∂(volume : Measure unitInterval), ‖S (v t)‖ ≤ ‖cv‖ :=
    circle_parabolic_h2_h4_norm_ae T τ V
  have hDae : ∀ᵐ t ∂(volume : Measure unitInterval), ‖S (d t)‖ ≤ b :=
    circle_parabolic_h2_h4_norm_ae T τ (U-V)
  have hd : d = u-v := (circleParabolicH4 T τ).map_sub U V
  have hdae : (d : unitInterval → CircleSobolevSpace T 4) =ᵐ[volume]
      fun t => u t-v t := by
    rw [hd]
    exact Lp.coeFn_sub u v
  have hpoint : ∀ᵐ t ∂(volume : Measure unitInterval),
      ‖(F-G) t‖ ≤ (C*a)*‖d t‖+(C*b)*(‖u t‖+‖v t‖) := by
    filter_upwards [Lp.coeFn_sub F G,hF,hG,hdae,hUae,hVae,hDae]
      with t hsub hFt hGt hdt hUbound hVbound hDbound
    have hdiffbound : ‖S (u t-v t)‖ ≤ b := by
      have heq : ‖S (u t-v t)‖ = ‖S (d t)‖ :=
        congrArg (fun z : CircleSobolevSpace T 4 => ‖S z‖) hdt.symm
      exact heq.le.trans hDbound
    have ht := htame (u t) (v t)
      (lt_of_le_of_lt hUbound hU) (lt_of_le_of_lt hVbound hV)
    simp only [Pi.sub_apply] at hsub
    have hvalue : (F-G) t = N (u t)-N (v t) :=
      hsub.trans (congrArg₂ (fun x y : CircleL2 T => x-y) hFt hGt)
    calc
      ‖(F-G) t‖ = ‖N (u t)-N (v t)‖ := congrArg norm hvalue
      _ ≤ C*
          ((‖S (u t)‖+‖S (v t)‖)*‖u t-v t‖+
            (‖u t‖+‖v t‖)*‖S (u t-v t)‖) := ht
      _ ≤ C*(a*‖u t-v t‖+b*(‖u t‖+‖v t‖)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (add_le_add hUbound hVbound) (norm_nonneg _)
        · simpa only [mul_comm b] using
            mul_le_mul_of_nonneg_left hdiffbound (by positivity : 0 ≤ ‖u t‖+‖v t‖)
      _ = (C*a)*‖d t‖+(C*b)*(‖u t‖+‖v t‖) := by rw [hdt]; ring
  have h := circle_time_two_term_bound T (F-G) d u v (C*a) (C*b)
    (mul_nonneg hC (by dsimp only [a]; positivity))
    (mul_nonneg hC (norm_nonneg _)) hpoint
  calc
    ‖F-G‖ ≤ (C*a)*‖d‖+(C*b)*(‖u‖+‖v‖) := h
    _ = C*((‖circleParabolicCurve T τ U‖+‖circleParabolicCurve T τ V‖)*
          ‖circleParabolicH4 T τ (U-V)‖+
        (‖circleParabolicH4 T τ U‖+‖circleParabolicH4 T τ V‖)*
          ‖circleParabolicCurve T τ (U-V)‖) := by
      dsimp only [a,b,d,u,v,cu,cv,cd]
      ring

/-- The actual Nemytskii representative and the mixed H2-H4 time estimate
needed for Picard iteration. Both time-H4 components are merely Lp classes. -/
theorem circle_parabolic_nemytskii_tame :
    let R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} →
        CircleTimeL2 T := circleParabolicNemytskii T τ hδ hC hN0 htame
    (∀ U, (R U : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => N (circleParabolicH4 T τ U.1 t)) ∧
    ∀ U V, ‖R U-R V‖ ≤ C*
      ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
          ‖circleParabolicH4 T τ (U.1-V.1)‖+
        (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
          ‖circleParabolicCurve T τ (U.1-V.1)‖) := by
  let R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} →
      CircleTimeL2 T := circleParabolicNemytskii T τ hδ hC hN0 htame
  have hR (U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ}) :
      (R U : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => N (circleParabolicH4 T τ U.1 t) :=
    MemLp.coeFn_toLp
      (circle_parabolic_nonlinear_memLp T τ hδ hC hN0 htame U.1 U.2)
  refine ⟨hR,?_⟩
  intro U V
  exact circle_parabolic_time_tame_bound T τ hC htame U.1 V.1 U.2 V.2
    (R U) (R V) (hR U) (hR V)

end Lemniscate
