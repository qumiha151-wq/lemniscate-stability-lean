import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Hom.Basic

/-! Joint continuity of the inverses of a continuous family of increasing
real order isomorphisms, without derivative or uniformity assumptions. -/
namespace Lemniscate
open Filter Set
open scoped Topology

/-- An increasing real coordinate depending jointly continuously on an
arbitrary topological parameter has a jointly continuous inverse. Fixed
order brackets give neighborhoods for the inverse directly. -/
theorem parametric_order_iso_inverse_continuous
    {P : Type*} [TopologicalSpace P] (e : P → (ℝ ≃o ℝ))
    (he : Continuous (fun p : P × ℝ => e p.1 p.2)) :
    Continuous (fun p : P × ℝ => (e p.1).symm p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q : P × ℝ => (e q.1).symm q.2)
    (𝓝 p) (𝓝 ((e p.1).symm p.2))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hc : Continuous (fun q : P × ℝ => e q.1 a) :=
      he.comp (continuous_fst.prodMk continuous_const)
    have hp : e p.1 a < p.2 := (e p.1).lt_symm_apply.mp ha
    have hnear : ∀ᶠ q : P × ℝ in 𝓝 p, e q.1 a < q.2 :=
      (isOpen_lt hc continuous_snd).mem_nhds hp
    filter_upwards [hnear] with q hq
    exact (e q.1).lt_symm_apply.mpr hq
  · intro b hb
    have hc : Continuous (fun q : P × ℝ => e q.1 b) :=
      he.comp (continuous_fst.prodMk continuous_const)
    have hp : p.2 < e p.1 b := (e p.1).symm_apply_lt.mp hb
    have hnear : ∀ᶠ q : P × ℝ in 𝓝 p, q.2 < e q.1 b :=
      (isOpen_lt continuous_snd hc).mem_nhds hp
    filter_upwards [hnear] with q hq
    exact (e q.1).symm_apply_lt.mpr hq

end Lemniscate
