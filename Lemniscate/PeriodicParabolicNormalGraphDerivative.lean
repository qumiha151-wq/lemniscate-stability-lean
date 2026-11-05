import Lemniscate.PeriodicParabolicNormalGraphFlow
import Lemniscate.PeriodicParabolicLowerOrder
import Lemniscate.PeriodicTimeNonlinearRemainder
import Lemniscate.NormalGraphSobolevRemainder
import Lemniscate.PeriodicSobolevPrincipalEstimate

/-! The derivative of the actual time normal-graph data map. Its nonlinear
remainder is the existing measurable time-L2 Nemytskii map, with a genuine
quadratic bound in the maximal-regularity norm.


-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal Topology

private theorem quadratic_remainder_hasFDerivAt
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : X → Y) (L : X →L[ℂ] Y) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ᶠ u in 𝓝 (0 : X), ‖F u-F 0-L u‖ ≤ C*‖u‖^2) :
    HasFDerivAt F L 0 := by
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  filter_upwards [hbound,Metric.ball_mem_nhds (0 : X) (div_pos hε hC)]
    with u hu hsmall
  have hn : ‖u‖ < ε/C := by
    simpa only [Metric.mem_ball,dist_zero_right] using hsmall
  have hc : C*‖u‖ ≤ ε := by
    simpa only [mul_comm] using (le_div_iff₀ hC).mp hn.le
  simp only [zero_add]
  calc
    ‖F u-F 0-L u‖ ≤ C*‖u‖^2 := hu
    _ = (C*‖u‖)*‖u‖ := by ring
    _ ≤ ε*‖u‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg u)

private theorem mixed_quadratic_bound {a b x C : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hax : a ≤ x) (hbx : b ≤ x) :
    C*(a*b+b*a) ≤ (2*C)*x^2 := by
  have hab : a*b ≤ x*x := mul_le_mul hax hbx hb hx
  have hba : b*a ≤ x*x := mul_le_mul hbx hax ha hx
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hab),
    mul_nonneg hC (sub_nonneg.mpr hba)]

private theorem mixed_scalar_bound
    (n a a₀ b b₀ ad bd x C : ℝ)
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hax : a ≤ x) (hbx : b ≤ x)
    (ha₀ : a₀ = 0) (hb₀ : b₀ = 0) (had : ad = a) (hbd : bd = b)
    (h : n ≤ C*((a+a₀)*bd+(b+b₀)*ad)) : n ≤ (2*C)*x^2 := by
  have hclean : n ≤ C*(a*b+b*a) := by
    simpa only [ha₀,hb₀,had,hbd,add_zero] using h
  exact hclean.trans (mixed_quadratic_bound hC ha hb hx hax hbx)

private theorem remainder_difference {Y : Type*} [AddCommGroup Y]
    (f f₀ l r r₀ : Y) (hu : r = f-l) (hzero : r₀ = f₀) :
    f-f₀-l = r-r₀ := by rw [hu,hzero]; abel

private theorem spatial_remainder_difference
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : X → Y) (D : X →L[ℂ] Y) (f g : X) :
    (F f-D f)-(F g-D g) = F f-F g-D (f-g) := by
  rw [map_sub]
  abel

private theorem spatial_remainder_zero
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : X → Y) (D : X →L[ℂ] Y) (hFzero : F 0 = 0) :
    (fun f => F f-D f) 0 = 0 := by
  change F 0-D 0 = 0
  rw [hFzero,map_zero,sub_zero]

private theorem spatial_remainder_tame
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (F : X → Y) (D : X →L[ℂ] Y) (H : X → ℝ) (δ C : ℝ)
    (htame : ∀ f g : X, H f < δ → H g < δ →
      ‖F f-F g-D (f-g)‖ ≤ C*
        ((H f+H g)*‖f-g‖+(‖f‖+‖g‖)*H (f-g))) :
    ∀ f g : X, H f < δ → H g < δ →
      ‖(F f-D f)-(F g-D g)‖ ≤ C*
        ((H f+H g)*‖f-g‖+(‖f‖+‖g‖)*H (f-g)) := by
  intro f g hf hg
  exact (congrArg norm (spatial_remainder_difference F D f g)).le.trans (htame f g hf hg)

private theorem positive_pair_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ δ > 0, ∃ C > 0, P δ C)
    (k : ∀ δ, 0 < δ → ∀ C, 0 < C → P δ C → Q) : Q := by
  obtain ⟨δ,hδ,C,hC,hP⟩ := h
  exact k δ hδ C hC hP

private theorem eventually_norm_lt_zero
    {X : Type*} [NormedAddCommGroup X] {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : X in 𝓝 0, ‖u‖ < δ := by
  filter_upwards [Metric.ball_mem_nhds (0 : X) hδ] with u hu
  simpa only [Metric.mem_ball,dist_zero_right] using hu

private theorem derivative_of_tame_remainder
    {X A Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup A]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (c : X → A)
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (R : {u : X | ‖c u‖ < δ} → Y)
    (z : {u : X | ‖c u‖ < δ}) (hz : z.1 = 0)
    (hquadratic : ∀ u, ‖R u-R z‖ ≤ (2*C)*‖u.1‖^2)
    (G : X → Y) (L : X →L[ℂ] Y) (S : X → Prop)
    (hS0 : S 0) (hS : ∀ᶠ u in 𝓝 0, S u)
    (hcnorm : ∀ u, ‖c u‖ ≤ ‖u‖)
    (hrep : ∀ u, S u.1 → R u = G u.1-L u.1) : HasFDerivAt G L 0 := by
  have hSz : S z.1 := hz.symm ▸ hS0
  have hrep0 : R z = G 0 := by
    simpa only [hz,map_zero,sub_zero] using hrep z hSz
  apply quadratic_remainder_hasFDerivAt G L (mul_pos (by norm_num : (0:ℝ) < 2) hC)
  filter_upwards [hS,eventually_norm_lt_zero (X := X) hδ] with U hU hnorm
  let u : {u : X | ‖c u‖ < δ} := ⟨U,(hcnorm U).trans_lt hnorm⟩
  have hquad : ‖R u-R z‖ ≤ (2*C)*‖U‖^2 := hquadratic u
  have heq : G U-G 0-L U = R u-R z :=
    remainder_difference (G U) (G 0) (L U) (R u) (R z) (hrep u hU) hrep0
  exact (congrArg norm heq).le.trans hquad

private def productDataLinear
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (initial : X →L[ℂ] Y) (v L : X →L[ℂ] Z) : X →L[ℂ] (Y × Z) :=
  initial.prod (v-L)

private theorem product_data_hasFDerivAt
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    (initial : X →L[ℂ] Y) (v L : X →L[ℂ] Z) (F : X → Z)
    (hF : HasFDerivAt F L 0) :
    HasFDerivAt (fun u => (initial u,v u-F u)) (productDataLinear initial v L) 0 :=
  initial.hasFDerivAt.prodMk (v.hasFDerivAt.sub hF)

private theorem hasFDerivAt_transport
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {F : X → Y} {L M : X →L[ℂ] Y} {x : X}
    (h : HasFDerivAt F L x) (hLM : ∀ u, L u = M u) : HasFDerivAt F M x := by
  have hEq : L = M := ContinuousLinearMap.ext hLM
  subst M
  exact h

variable (T : ℝ) [Fact (0 < T)]

/-- The six fixed spatial background fields, pulled back to time and space. -/
def circleTimeConstantBackground (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    Fin 6 → CircleTimeCoefficient T :=
  fun i => (![K.k,K.ks,K.kss,K.ksss,K.eta,K.b] i).comp
    ⟨Prod.snd,continuous_snd⟩

private theorem constant_background_restrict
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (t : unitInterval) :
    circleTimeNormalGraphBackground T (circleTimeConstantBackground T K) t = K := by
  cases K
  rfl

variable (τ : ℝ)

private def timeSpatialDerivative
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T) :
    CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T := by
  simpa only using!
    (D.compLpL 2 (volume : Measure unitInterval)).comp (circleParabolicH4 T τ)

private theorem derivative_curve_norm_le (U : CircleParabolicSpace T τ) :
    ‖circleParabolicCurve T τ U‖ ≤ ‖U‖ := norm_fst_le U.1

private theorem derivative_h4_norm_le (U : CircleParabolicSpace T τ) :
    ‖circleParabolicH4 T τ U‖ ≤ ‖U‖ :=
  (norm_fst_le U.1.2).trans (norm_snd_le U.1)

set_option maxHeartbeats 800000 in
private theorem time_remainder_quadratic_bound
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} → CircleTimeL2 T)
    (htame : ∀ U V, ‖R U-R V‖ ≤ C*
      ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
          ‖circleParabolicH4 T τ (U.1-V.1)‖+
        (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
          ‖circleParabolicCurve T τ (U.1-V.1)‖))
    (U : CircleParabolicSpace T τ) (hU : ‖circleParabolicCurve T τ U‖ < δ) :
    let z : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} :=
      ⟨0,by
        change ‖circleParabolicCurve T τ (0 : CircleParabolicSpace T τ)‖ < δ
        simpa only [map_zero,norm_zero] using hδ⟩
    ‖R ⟨U,hU⟩-R z‖ ≤ (2*C)*‖U‖^2 := by
  let z : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} :=
    ⟨0,by
      change ‖circleParabolicCurve T τ (0 : CircleParabolicSpace T τ)‖ < δ
      simpa only [map_zero,norm_zero] using hδ⟩
  change ‖R ⟨U,hU⟩-R z‖ ≤ (2*C)*‖U‖^2
  have ht := htame ⟨U,hU⟩ z
  have ha₀ : ‖circleParabolicCurve T τ z.1‖ = 0 :=
    (congrArg (fun f : C(unitInterval,CircleSobolevSpace T 2) => ‖f‖)
      (map_zero (circleParabolicCurve T τ))).trans norm_zero
  have hb₀ : ‖circleParabolicH4 T τ z.1‖ = 0 := by
    change ‖circleParabolicH4 T τ (0 : CircleParabolicSpace T τ)‖ = 0
    have hz : ‖(0 : CircleTimeH4 T)‖ = 0 := by
      simpa only using! (norm_zero (E := CircleTimeH4 T))
    have hzero := congrArg (fun f : CircleTimeH4 T => ‖f‖)
      (map_zero (circleParabolicH4 T τ))
    exact hzero.trans hz
  have hsub : U-z.1 = U := by
    change U-(0 : CircleParabolicSpace T τ) = U
    exact sub_zero U
  have had : ‖circleParabolicCurve T τ (U-z.1)‖ = ‖circleParabolicCurve T τ U‖ :=
    congrArg (fun V : CircleParabolicSpace T τ => ‖circleParabolicCurve T τ V‖) hsub
  have hbd : ‖circleParabolicH4 T τ (U-z.1)‖ = ‖circleParabolicH4 T τ U‖ :=
    congrArg (fun V : CircleParabolicSpace T τ => ‖circleParabolicH4 T τ V‖) hsub
  exact mixed_scalar_bound ‖R ⟨U,hU⟩-R z‖
    ‖circleParabolicCurve T τ U‖ ‖circleParabolicCurve T τ z.1‖
    ‖circleParabolicH4 T τ U‖ ‖circleParabolicH4 T τ z.1‖
    ‖circleParabolicCurve T τ (U-z.1)‖ ‖circleParabolicH4 T τ (U-z.1)‖ ‖U‖ C
    hC (norm_nonneg (circleParabolicCurve T τ U))
    (norm_nonneg (circleParabolicH4 T τ U)) (norm_nonneg U)
    (derivative_curve_norm_le T τ U) (derivative_h4_norm_le T τ U)
    ha₀ hb₀ had hbd ht

set_option maxHeartbeats 800000 in
private theorem time_nemytskii_exists
    {δ C : ℝ} {N : CircleSobolevSpace T 4 → CircleL2 T}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hN0 : N 0 = 0)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖)) :
    ∃ R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} → CircleTimeL2 T,
      (∀ U, (R U : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => N (circleParabolicH4 T τ U.1 t)) ∧
      ∀ U V, ‖R U-R V‖ ≤ C*
        ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
            ‖circleParabolicH4 T τ (U.1-V.1)‖+
          (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
            ‖circleParabolicCurve T τ (U.1-V.1)‖) :=
  ⟨circleParabolicNemytskii T τ hδ hC hN0 htame,
    circle_parabolic_nemytskii_tame T τ hδ hC hN0 htame⟩

set_option maxHeartbeats 800000 in
private theorem time_normal_graph_remainder_eq
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (N : CircleSobolevSpace T 4 → CircleL2 T)
    (hN : ∀ f, N f = circleNormalGraphFlow T K c f-D f)
    (U : CircleParabolicSpace T τ) (r : CircleTimeL2 T)
    (hU : (circleTimeConstantBackground T K,U) ∈ circleParabolicNormalGraphDomain T τ)
    (hr : (r : unitInterval → CircleL2 T) =ᵐ[volume]
      fun t => N (circleParabolicH4 T τ U t)) :
    r = circleParabolicNormalGraphFlow T τ c (circleTimeConstantBackground T K,U)-
      timeSpatialDerivative T τ D U := by
  let v : CircleTimeL2 T :=
    circleParabolicNormalGraphFlow T τ c (circleTimeConstantBackground T K,U)
  let l : CircleTimeL2 T := timeSpatialDerivative T τ D U
  apply Lp.ext
  have hlinear := D.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval))
    (circleParabolicH4 T τ U)
  have hflow := circle_parabolic_normal_graph_flow_ae T τ c
    (circleTimeConstantBackground T K) U hU
  filter_upwards [hr,hflow,hlinear,Lp.coeFn_sub v l] with t hrt hft hlt hsub
  have hf : v t = circleNormalGraphFlow T K c (circleParabolicH4 T τ U t) := by
    simpa only [v,constant_background_restrict] using hft
  have hNt := hrt.trans (hN (circleParabolicH4 T τ U t))
  change (v-l) t = v t-l t at hsub
  change r t = (v-l) t
  exact hNt.trans ((congrArg₂ (fun x y : CircleL2 T => x-y) hf hlt).symm.trans hsub.symm)

set_option maxHeartbeats 800000 in
private theorem fixed_time_normal_graph_hasFDerivAt_of_remainder
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (N : CircleSobolevSpace T 4 → CircleL2 T)
    (hN : ∀ f, N f = circleNormalGraphFlow T K c f-D f)
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hNzero : N 0 = 0)
    (hNtame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖)) :
    HasFDerivAt
      (fun U : CircleParabolicSpace T τ => circleParabolicNormalGraphFlow T τ c
        (circleTimeConstantBackground T K,U))
      (timeSpatialDerivative T τ D) 0 := by
  refine (time_nemytskii_exists T τ hδ hC.le hNzero hNtame).elim ?_
  intro R hR
  let a := circleTimeConstantBackground T K
  let G : CircleParabolicSpace T τ → CircleTimeL2 T :=
    fun U => circleParabolicNormalGraphFlow T τ c (a,U)
  let L : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
    timeSpatialDerivative T τ D
  have hsmooth := circle_parabolic_normal_graph_flow_smooth T τ c
  have hdom0 : (a,(0 : CircleParabolicSpace T τ)) ∈ circleParabolicNormalGraphDomain T τ :=
    hsmooth.2.1 a
  have hpair : Continuous (fun U : CircleParabolicSpace T τ => (a,U)) :=
    continuous_const.prodMk continuous_id
  have hdomain : ∀ᶠ U : CircleParabolicSpace T τ in 𝓝 0,
      (a,U) ∈ circleParabolicNormalGraphDomain T τ :=
    hpair.continuousAt.preimage_mem_nhds
      (hsmooth.1.mem_nhds hdom0)
  let z : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} :=
    ⟨0,by
      change ‖circleParabolicCurve T τ (0 : CircleParabolicSpace T τ)‖ < δ
      simpa only [map_zero,norm_zero] using hδ⟩
  have hquadratic : ∀ U, ‖R U-R z‖ ≤ (2*C)*‖U.1‖^2 :=
    fun U => time_remainder_quadratic_bound T τ δ C hδ hC.le R hR.2 U.1 U.2
  have hderivative := derivative_of_tame_remainder
    (fun U : CircleParabolicSpace T τ => circleParabolicCurve T τ U)
    δ C hδ hC R z rfl hquadratic G L (fun U => (a,U) ∈ circleParabolicNormalGraphDomain T τ)
    hdom0 hdomain (derivative_curve_norm_le T τ)
    (fun U hU => time_normal_graph_remainder_eq T τ K c D N hN
      U.1 (R U) hU (hR.1 U))
  simpa only [G,L,a] using! hderivative

set_option maxHeartbeats 800000 in
private theorem fixed_time_normal_graph_hasFDerivAt
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (hFzero : circleNormalGraphFlow T K c 0 = 0) :
    HasFDerivAt
      (fun U : CircleParabolicSpace T τ => circleParabolicNormalGraphFlow T τ c
        (circleTimeConstantBackground T K,U))
      (timeSpatialDerivative T τ (circleNormalGraphDerivative T K c)) 0 := by
  exact positive_pair_transport (circle_normal_graph_sobolev_tame_remainder T K c)
    (fun δ hδ C hC htame =>
      fixed_time_normal_graph_hasFDerivAt_of_remainder T τ K c
        (circleNormalGraphDerivative T K c)
        (fun f => circleNormalGraphFlow T K c f-circleNormalGraphDerivative T K c f)
        (fun _ => rfl) δ C hδ hC
        (spatial_remainder_zero (circleNormalGraphFlow T K c)
          (circleNormalGraphDerivative T K c) hFzero)
        (spatial_remainder_tame (circleNormalGraphFlow T K c)
          (circleNormalGraphDerivative T K c)
          (fun f => ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖) δ C htame))

set_option maxHeartbeats 600000 in
private theorem normal_graph_linear_data_eq
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hBA : ∀ f : CircleSobolevSpace T 4,
      circleSobolevPrincipalOperator T f-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) = -(D f))
    (U : CircleParabolicSpace T τ) :
    (circleParabolicInitialValue T τ U,
      circleParabolicTimeDerivative T τ U-timeSpatialDerivative T τ D U) =
      circleParabolicLowerOrderData T τ B U := by
  apply Prod.ext
  · rfl
  · let v := circleParabolicTimeDerivative T τ U
    let w := circleParabolicH4 T τ U
    let z := circleParabolicH2Time T τ U
    let A := circleSobolevPrincipalOperator T
    have hD := D.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) w
    have hA := A.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) w
    have hB := B.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) z
    have hz : (z : unitInterval → CircleSobolevSpace T 2) =ᵐ[volume]
        circleParabolicCurve T τ U :=
      ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
        (circleParabolicCurve T τ U)
    change v-(D.compLpL 2 (volume : Measure unitInterval)) w =
      (v+(A.compLpL 2 (volume : Measure unitInterval)) w)-
        (B.compLpL 2 (volume : Measure unitInterval)) z
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub v ((D.compLpL 2 (volume : Measure unitInterval)) w),
      Lp.coeFn_sub (v+(A.compLpL 2 (volume : Measure unitInterval)) w)
        ((B.compLpL 2 (volume : Measure unitInterval)) z),
      Lp.coeFn_add v ((A.compLpL 2 (volume : Measure unitInterval)) w),
      hD,hA,hB,hz,circle_parabolic_h2_h4_ae T τ U]
      with t hleft hright hadd hDt hAt hBt hzt hwt
    change (v-(D.compLpL 2 (volume : Measure unitInterval)) w) t =
      v t-((D.compLpL 2 (volume : Measure unitInterval)) w) t at hleft
    change ((v+(A.compLpL 2 (volume : Measure unitInterval)) w)-
      (B.compLpL 2 (volume : Measure unitInterval)) z) t =
      (v+(A.compLpL 2 (volume : Measure unitInterval)) w) t-
        ((B.compLpL 2 (volume : Measure unitInterval)) z) t at hright
    change (v+(A.compLpL 2 (volume : Measure unitInterval)) w) t =
      v t+((A.compLpL 2 (volume : Measure unitInterval)) w) t at hadd
    have hinc : z t = circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w t)) :=
      hzt.trans hwt
    have hspatial := hBA (w t)
    have halg (x y z d : CircleL2 T) (h : y-z = -d) : x-d = (x+y)-z := by
      calc
        x-d = x+(-d) := sub_eq_add_neg _ _
        _ = x+(y-z) := congrArg (fun a : CircleL2 T => x+a) h.symm
        _ = (x+y)-z := by abel
    calc
      (v-(D.compLpL 2 (volume : Measure unitInterval)) w) t =
          v t-D (w t) := hleft.trans (congrArg (fun d : CircleL2 T => v t-d) hDt)
      _ = (v t+A (w t))-B (circleSobolevInclusion T 2
          (circleSobolevInclusion T 3 (w t))) := halg _ _ _ _ hspatial
      _ = (v t+((A.compLpL 2 (volume : Measure unitInterval)) w) t)-
          ((B.compLpL 2 (volume : Measure unitInterval)) z) t :=
        congrArg₂ (fun x y : CircleL2 T => x-y)
          (congrArg (fun x : CircleL2 T => v t+x) hAt.symm)
          ((congrArg B hinc).symm.trans hBt.symm)
      _ = ((v+(A.compLpL 2 (volume : Measure unitInterval)) w)-
          (B.compLpL 2 (volume : Measure unitInterval)) z) t :=
        (congrArg (fun x : CircleL2 T => x-
          ((B.compLpL 2 (volume : Measure unitInterval)) z) t) hadd.symm).trans hright.symm

set_option maxHeartbeats 800000 in
/-- The derivative of the actual normal-graph initial-value and equation
map is the previously constructed principal-plus-lower-order data map. -/
theorem circle_parabolic_normal_graph_hasFDerivAt
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hFzero : circleNormalGraphFlow T K c 0 = 0)
    (hBA : ∀ f : CircleSobolevSpace T 4,
      circleSobolevPrincipalOperator T f-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) =
          -(circleNormalGraphDerivative T K c f)) :
    HasFDerivAt
      (fun U : CircleParabolicSpace T τ =>
        (circleParabolicInitialValue T τ U,
          circleParabolicTimeDerivative T τ U-circleParabolicNormalGraphFlow T τ c
            (circleTimeConstantBackground T K,U)))
      (circleParabolicLowerOrderData T τ B) 0 := by
  have hflow := fixed_time_normal_graph_hasFDerivAt T τ K c hFzero
  have hdata := product_data_hasFDerivAt
    (X := ↥(CircleParabolicSpace T τ)) (Y := ↥(CircleSobolevSpace T 2))
    (Z := ↥(CircleTimeL2 T)) (circleParabolicInitialValue T τ)
    (circleParabolicTimeDerivative T τ)
    (timeSpatialDerivative T τ (circleNormalGraphDerivative T K c))
    (fun U => circleParabolicNormalGraphFlow T τ c (circleTimeConstantBackground T K,U)) hflow
  exact hasFDerivAt_transport hdata
    (fun U => normal_graph_linear_data_eq T τ (circleNormalGraphDerivative T K c) B hBA U)

end Lemniscate
