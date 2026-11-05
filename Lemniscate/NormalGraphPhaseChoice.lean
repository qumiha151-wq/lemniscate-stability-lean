import Lemniscate.UniformScalarImplicitRoot
import Mathlib.Topology.Order.LeftRightNhds

/-! A C1 phase equation selects a small angle with a continuous zero
trace at the initial time. The velocity will be recovered from the
geometric evolution equation, so no implicit velocity formula is needed. -/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology ContDiff NNReal

/-- The uniform scalar root gives a small C1 angle and its zero trace. -/
private theorem normal_graph_phase_choice_on_rectangle
    (Φ : ℝ × ℝ → ℝ) (T a d₀ : ℝ) (hT : 0 < T) (ha : 0 < a) (hd₀ : d₀ ≠ 0)
    (hΦ : ContDiffOn ℝ 1 Φ (Ioo 0 T ×ˢ Ioo (-a) a))
    (c : ℝ≥0) (hc : (c:ℝ) < 1/2)
    (hzero : ∀ t ∈ Ioo 0 T, |Φ (t,0)/d₀| ≤ a/4)
    (hangle : ∀ t ∈ Ioo 0 T, ∀ x : ℝ, |x| ≤ a/2 →
      |1-deriv (fun y => Φ (t,y)) x/d₀| ≤ c)
    (htrace : Tendsto (fun t => Φ (t,0)) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    ∃ θ : ℝ → ℝ,
      ContDiffOn ℝ 1 θ (Ioo 0 T) ∧
      Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ t ∈ Ioo 0 T, |θ t| < a/2 ∧ Φ (t,θ t) = 0 := by
  let U := Ioo (0:ℝ) T
  let V := Ioo (-a) a
  let f : ℝ × ℝ → ℝ := fun q => Φ q/d₀
  have hrV : Metric.closedBall (0:ℝ) (a/2) ⊆ V := by
    intro x hx
    have hb : |x| ≤ a/2 := by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hx
    rcases abs_le.mp hb with ⟨hl,hu⟩
    constructor <;> linarith only [hl,hu,ha]
  obtain ⟨θ,hθ,hroot,_⟩ := uniform_scalar_implicit_root
    1 (by simp) U isOpen_Ioo V isOpen_Ioo f (hΦ.div_const d₀)
    (a/2) (by positivity) hrV c hc
    (by
      intro t ht
      have hz := hzero t ht
      dsimp only [f]
      linarith only [hz])
    (by
      intro t ht x hx
      simpa only [f,deriv_div_const] using hangle t ht x hx)
  have hphase (t : ℝ) (ht : t ∈ U) : Φ (t,θ t) = 0 := by
    have heq := (hroot t ht).2.1
    change Φ (t,θ t)/d₀ = 0 at heq
    simpa only [zero_mul] using (div_eq_iff hd₀).mp heq
  have hmajor : Tendsto (fun t => 2*|Φ (t,0)/d₀|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_div,abs_zero,mul_zero] using (htrace.div_const d₀).abs.const_mul 2
  have hθtrace : Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hmajor
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    simpa only [Real.norm_eq_abs,f] using (hroot t ht).2.2
  exact ⟨θ,hθ,hθtrace,fun t ht => ⟨(hroot t ht).1,hphase t ht⟩⟩

/-- A nonzero angular phase derivative at the initial graph selects the
actual small angle on a sufficiently short positive time interval. Its
continuous extension at the initial parameter is enough; no initial time
derivative or uniform numerical derivative estimate is assumed. -/
theorem normal_graph_phase_choice
    (Φ D : ℝ × ℝ → ℝ) (T₀ a₀ : ℝ) (hT₀ : 0<T₀) (ha₀ : 0<a₀)
    (hΦ : ContDiffOn ℝ 1 Φ (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀))
    (hD : ContinuousWithinAt D
      (insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀)) (0,0))
    (hD₀ : D (0,0)≠0)
    (hangle : ∀ t ∈ Ioo 0 T₀, ∀ x ∈ Ioo (-a₀) a₀,
      deriv (fun y => Φ (t,y)) x=D (t,x))
    (htrace : Tendsto (fun t => Φ (t,0)) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    ∃ T>0, T≤T₀ ∧ ∃ a>0, a≤a₀ ∧ ∃ θ : ℝ → ℝ,
      ContDiffOn ℝ 1 θ (Ioo 0 T) ∧
      Tendsto θ (𝓝[>] (0:ℝ)) (𝓝 0) ∧
      ∀ t ∈ Ioo 0 T, |θ t|<a/2 ∧ Φ (t,θ t)=0 := by
  let K := insert ((0:ℝ),0) (Ioo 0 T₀ ×ˢ Ioo (-a₀) a₀)
  let B : ℝ × ℝ → ℝ := fun z => |1-D z/D (0,0)|
  have hB : ContinuousWithinAt B K (0,0) :=
    (continuousWithinAt_const.sub (hD.div_const (D (0,0)))).abs
  have hB₀ : B (0,0)=0 := by simp only [B,div_self hD₀,sub_self,abs_zero]
  have hBm : {z : ℝ × ℝ | B z<(1/4:ℝ)} ∈ 𝓝[K] (0,0) := by
    have hn : ∀ᶠ y : ℝ in 𝓝 (B (0,0)), y<(1/4:ℝ) :=
      isOpen_Iio.mem_nhds (by rw [hB₀]; norm_num)
    exact hB.eventually hn
  obtain ⟨r,hr,hbound⟩ := Metric.mem_nhdsWithin_iff.mp hBm
  let a := min a₀ r/2
  have ha : 0<a := div_pos (lt_min ha₀ hr) (by norm_num)
  have haa₀ : a≤a₀ := by dsimp only [a]; linarith only [min_le_left a₀ r,ha₀]
  have har : a<r := by dsimp only [a]; linarith only [min_le_right a₀ r,hr]
  have hres : Tendsto (fun t => |Φ (t,0)/D (0,0)|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_div,abs_zero] using (htrace.div_const (D (0,0))).abs
  have hsmall : {t : ℝ | |Φ (t,0)/D (0,0)|<a/4} ∈ 𝓝[>] (0:ℝ) := by
    have hn : ∀ᶠ y : ℝ in 𝓝 (0:ℝ), y<a/4 :=
      isOpen_Iio.mem_nhds (div_pos ha (by norm_num))
    exact hres.eventually hn
  obtain ⟨b,hb,hbsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let T := min T₀ (min (r/2) b)
  have hT : 0<T := lt_min hT₀ (lt_min (by positivity) hb)
  have hTT₀ : T≤T₀ := min_le_left _ _
  have hTr : T≤r/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hTb : T≤b := (min_le_right _ _).trans (min_le_right _ _)
  have htime (t : ℝ) (ht : t∈Ioo 0 T) : t∈Ioo 0 T₀ :=
    ⟨ht.1,ht.2.trans_le hTT₀⟩
  have hscalar (x : ℝ) (hx : |x|≤a/2) : x∈Ioo (-a₀) a₀ := by
    have hxa : |x|<a₀ := hx.trans_lt ((by linarith only [ha] : a/2<a).trans_le haa₀)
    exact abs_lt.mp hxa
  have hrestriction : ContDiffOn ℝ 1 Φ (Ioo 0 T ×ˢ Ioo (-a) a) := by
    apply hΦ.mono
    intro z hz
    exact ⟨htime z.1 hz.1,⟨by linarith only [hz.2.1,haa₀],
      hz.2.2.trans_le haa₀⟩⟩
  have hzero (t : ℝ) (ht : t∈Ioo 0 T) : |Φ (t,0)/D (0,0)|≤a/4 :=
    (hbsmall ⟨ht.1,ht.2.trans_le hTb⟩).le
  have hderiv (t : ℝ) (ht : t∈Ioo 0 T) (x : ℝ) (hx : |x|≤a/2) :
      |1-deriv (fun y => Φ (t,y)) x/D (0,0)|≤((1/4:ℝ≥0):ℝ) := by
    rw [hangle t (htime t ht) x (hscalar x hx)]
    have htball : |t|<r := by rw [abs_of_pos ht.1]; linarith only [ht.2,hTr,hr]
    have hxball : |x|<r := hx.trans_lt (by linarith only [har,ha])
    have hball : (t,x)∈Metric.ball ((0:ℝ),0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using
        And.intro htball hxball
    exact (hbound ⟨hball,Or.inr ⟨htime t ht,hscalar x hx⟩⟩).le
  obtain ⟨θ,hθ,hθtrace,hθroot⟩ := normal_graph_phase_choice_on_rectangle
    Φ T a (D (0,0)) hT ha hD₀ hrestriction (1/4) (by norm_num) hzero hderiv htrace
  exact ⟨T,hT,hTT₀,a,ha,haa₀,θ,hθ,hθtrace,hθroot⟩

end Lemniscate
