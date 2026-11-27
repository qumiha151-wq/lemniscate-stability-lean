import SolitonClassification.LocalCrossingRootUniqueness
import Mathlib.Topology.Sequences

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace ClosedSimilarity.CrossingResponse

private theorem deriv_value_of_constant {f : ℝ → ℝ} {x c v l u : ℝ} (der : HasDerivAt f v x)
    (hx : x ∈ Ioo l u) (flat : ∀ t ∈ Ioo l u, f t = c) : v = 0 := by
  have eqn : f =ᶠ[𝓝 x] fun _ => c := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    exact flat t ht
  exact der.unique ((hasDerivAt_const x c).congr_of_eventuallyEq eqn)

/-- The actual frozen height is strictly increasing on the entire real
axis. A hypothetical plateau forces both curvature and its slope to
vanish, contradicting the unit frozen tangent. -/
theorem strictMono_frozen_height : StrictMono (Y 0) := by
  obtain ⟨_,dK,dY,_⟩ := frozen_data
  have mono : Monotone (Y 0) := monotone_of_deriv_nonneg (fun t => (dY t).differentiableAt)
    (fun t => by rw [(dY t).deriv]; positivity)
  intro l u lt
  refine lt_of_le_of_ne (mono lt.le) ?_
  intro eq
  have flat (t : ℝ) (ht : t ∈ Ioo l u) : Y 0 t = Y 0 l :=
    le_antisymm ((mono ht.2.le).trans eq.ge) (mono ht.1.le)
  have zero (t : ℝ) (ht : t ∈ Ioo l u) : K 0 t = 0 := by
    have val := deriv_value_of_constant (dY t) ht flat
    nlinarith [sq_nonneg (K 0 t)]
  let t := (l+u)/2
  have inside : t ∈ Ioo l u := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
  have v := deriv_value_of_constant (dK t) inside zero
  have unit : (ty 0 t)^2+(tx 0 t)^2=1 := Real.sin_sq_add_cos_sq _
  rw [(frozen_tangent t).1,(frozen_tangent t).2,zero t inside,v] at unit
  norm_num at unit

private theorem moving_value {f : ℝ → ℝ → ℝ} (continuous : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    {e r : ℕ → ℝ} {d t : ℝ} (he : Tendsto e atTop (𝓝 d)) (hr : Tendsto r atTop (𝓝 t)) :
    Tendsto (fun n => f (e n) (r n)) atTop (𝓝 (f d t)) :=
  (continuous.tendsto (d,t)).comp (he.prodMk_nhds hr)

private theorem eventually_avoid_compact_level {f : ℝ → ℝ → ℝ}
    (continuous : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) {e h : ℕ → ℝ} {d v : ℝ}
    (he : Tendsto e atTop (𝓝 d)) (hh : Tendsto h atTop (𝓝 v))
    {S : Set ℝ} (compact : IsCompact S) (avoid : ∀ t ∈ S, f d t ≠ v) :
    ∀ᶠ n in atTop, ∀ t ∈ S, f (e n) t ≠ h n := by
  classical
  by_contra bad
  have many : ∃ᶠ n in atTop, ∃ t ∈ S, f (e n) t = h n := by
    change ¬ ∀ᶠ n in atTop, ¬ ∃ t ∈ S, f (e n) t = h n
    simpa only [not_exists,not_and] using bad
  obtain ⟨φ,hφ,points⟩ := extraction_of_frequently_atTop many
  choose t mem same using points
  obtain ⟨s,hs,ψ,hψ,lim⟩ := compact.tendsto_subseq mem
  have sub := hφ.tendsto_atTop.comp hψ.tendsto_atTop
  have left := moving_value (f := f) continuous (he.comp sub) lim
  have eqn : (fun i => f (e (φ (ψ i))) (t (ψ i))) =ᶠ[atTop] fun i => h (φ (ψ i)) :=
    Eventually.of_forall fun i => same (ψ i)
  exact avoid s hs (tendsto_nhds_unique (left.congr' eqn) (hh.comp sub))

/-- On every fixed bounded nonnegative fast-time interval, the chosen
axis intersection has exactly one possible first-quarter preimage. Its
centrally inverted height does not occur anywhere on that interval. -/
theorem eventually_unique_fast_preimage {a B : ℝ} (positive : 0<a) (simple : V 0 a ≠ 0)
    (e r : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 a)) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) B,
      (X (e n) t = X (e n) (r n) → Y (e n) t = Y (e n) (r n) → t = r n) ∧
        Y (e n) t ≠ - Y (e n) (r n) := by
  obtain ⟨d,hd,inj⟩ := eventually_injOn_signed_axis simple e (fun _ => 0) he tendsto_const_nhds
  let J := Ioo (a-d) (a+d)
  have amem : a ∈ J := ⟨by linarith,by linarith⟩
  have heights := moving_value (f := Y) Y_cont he hr
  have nonmem (t : ℝ) (ht : t ∈ Icc (0:ℝ) B \ J) : Y 0 t ≠ Y 0 a :=
    fun h => ht.2 ((strictMono_frozen_height.injective h) ▸ amem)
  have off := eventually_avoid_compact_level Y_cont he heights (isCompact_Icc.diff isOpen_Ioo) nonmem
  have origin : Y 0 0 = 0 := by change (∫ t in (0:ℝ)..0, ty 0 t) = 0; simp
  have sep (t : ℝ) (ht : t ∈ Icc (0:ℝ) B) : Y 0 t ≠ -Y 0 a := by
    have pos := strictMono_frozen_height positive
    have nonneg := strictMono_frozen_height.monotone ht.1
    linarith
  have opposite := eventually_avoid_compact_level Y_cont he heights.neg isCompact_Icc sep
  filter_upwards [inj, off, opposite, hr.eventually (isOpen_Ioo.mem_nhds amem)] with n hi ho hn rw'
  intro t ht
  refine ⟨?_, hn t ht⟩
  intro hx hy
  by_cases mem : t ∈ J
  · apply hi mem rw'
    simpa using hx
  · exact (ho t ⟨ht,mem⟩ hy).elim

/-- If visits to each fixed disk on the full first-quarter trajectory
have a uniform fast-time bound, the window result excludes extra first-
quarter preimages and all preimages of the opposite point. -/
theorem eventually_unique_quarter_preimage {a : ℝ} (positive : 0<a) (simple : V 0 a ≠ 0)
    (e r T : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 a))
    (capture : ∀ R : ℝ, 0 ≤ R → ∃ B : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) (T n),
      X (e n) t^2 + Y (e n) t^2 ≤ R^2 → t ≤ B) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) (T n),
      (X (e n) t = X (e n) (r n) → Y (e n) t = Y (e n) (r n) → t = r n) ∧
        ¬ (X (e n) t = -X (e n) (r n) ∧ Y (e n) t = -Y (e n) (r n)) := by
  let E := X 0 a ^ 2 + Y 0 a ^ 2
  have hE : 0 ≤ E := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have large : E < (E+1)^2 := by nlinarith [sq_nonneg E]
  obtain ⟨B,cap⟩ := capture (E+1) (by linarith)
  have radii := ((moving_value (f := X) X_cont he hr).pow 2).add ((moving_value (f := Y) Y_cont he hr).pow 2)
  have bound : ∀ᶠ n in atTop, X (e n) (r n)^2 + Y (e n) (r n)^2 < (E+1)^2 :=
    radii.eventually (Iio_mem_nhds large)
  filter_upwards [cap,bound,eventually_unique_fast_preimage (B := B) positive simple e r he hr]
    with n hn radius window
  intro t ht
  constructor
  · intro x y
    have bt := hn t ht (by rw [x,y]; exact radius.le)
    exact (window t ⟨ht.1,bt⟩).1 x y
  · rintro ⟨x,y⟩
    have bt := hn t ht (by simpa only [x,y,neg_sq] using radius.le)
    exact (window t ⟨ht.1,bt⟩).2 y

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.strictMono_frozen_height
#print axioms ClosedSimilarity.CrossingResponse.eventually_unique_fast_preimage
#print axioms ClosedSimilarity.CrossingResponse.eventually_unique_quarter_preimage
