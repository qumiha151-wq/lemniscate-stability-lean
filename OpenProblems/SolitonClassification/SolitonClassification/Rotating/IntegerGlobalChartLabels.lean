import SolitonClassification.Rotating.IntegerGlobalLedger
import SolitonClassification.Rotating.IntegerUniqueTransverseCharts
namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set CrossingCharts

def InAChart (x y : ℝ) := ∃k : Fin 2, x∈dom k false ∧ y∈dom k true

private theorem lo_values : firstIndex 0 false=1807 ∧ firstIndex 0 true=2204 ∧
    firstIndex 1 false=1684 ∧ firstIndex 1 true=2395 := by decide +kernel

theorem chart_of_box {A B C D : ℤ} {x y : ℝ} (point : Inside x y A B C D)
    {flag : Bool} (pass : ChartPass A B C D flag) : InAChart x y := by
  rcases point with ⟨h1,h2,h3,h4⟩
  obtain ⟨one,two,three,four⟩ := lo_values
  cases flag
  · change 1807≤A ∧ B≤1815 ∧ 2204≤C ∧ D≤2212 at pass
    obtain ⟨a,b,c,d⟩ := pass
    refine ⟨0,?_,?_⟩
    · change ((firstIndex 0 false:ℕ):ℝ)≤x ∧ x≤((firstIndex 0 false:ℕ):ℝ)+8
      rw [one]
      constructor <;> push_cast <;> linarith [show (1807:ℝ)≤A by exact_mod_cast a,show (B:ℝ)≤1815 by exact_mod_cast b]
    · change ((firstIndex 0 true:ℕ):ℝ)≤y ∧ y≤((firstIndex 0 true:ℕ):ℝ)+8
      rw [two]
      constructor <;> push_cast <;> linarith [show (2204:ℝ)≤C by exact_mod_cast c,show (D:ℝ)≤2212 by exact_mod_cast d]
  · change 1684≤A ∧ B≤1692 ∧ 2395≤C ∧ D≤2403 at pass
    obtain ⟨a,b,c,d⟩ := pass
    refine ⟨1,?_,?_⟩
    · change ((firstIndex 1 false:ℕ):ℝ)≤x ∧ x≤((firstIndex 1 false:ℕ):ℝ)+8
      rw [three]
      constructor <;> push_cast <;> linarith [show (1684:ℝ)≤A by exact_mod_cast a,show (B:ℝ)≤1692 by exact_mod_cast b]
    · change ((firstIndex 1 true:ℕ):ℝ)≤y ∧ y≤((firstIndex 1 true:ℕ):ℝ)+8
      rw [four]
      constructor <;> push_cast <;> linarith [show (2395:ℝ)≤C by exact_mod_cast c,show (D:ℝ)≤2403 by exact_mod_cast d]

theorem chart_in_period {k : Fin 2} {x y : ℝ} (hx : x∈dom k false) (hy : y∈dom k true) :
    0<x ∧ x<y ∧ y<3000 := by
  obtain ⟨one,two,three,four⟩ := lo_values
  fin_cases k
  · change (firstIndex 0 false:ℝ)≤x ∧ x≤(firstIndex 0 false:ℝ)+8 at hx
    change (firstIndex 0 true:ℝ)≤y ∧ y≤(firstIndex 0 true:ℝ)+8 at hy
    rw [one] at hx
    rw [two] at hy
    norm_num at hx hy
    exact ⟨by linarith [hx.1],by linarith [hx.2,hy.1],by linarith [hy.2]⟩
  · change (firstIndex 1 false:ℝ)≤x ∧ x≤(firstIndex 1 false:ℝ)+8 at hx
    change (firstIndex 1 true:ℝ)≤y ∧ y≤(firstIndex 1 true:ℝ)+8 at hy
    rw [three] at hx
    rw [four] at hy
    norm_num at hx hy
    exact ⟨by linarith [hx.1],by linarith [hx.2,hy.1],by linarith [hy.2]⟩

/-- A complete parametrization of ordered self-intersection pairs in a
single half-open period. The exactness field excludes triple points. -/
structure TwoCrossingPairs (f : ℝ → ℝ×ℝ) (T : ℝ) where
  pair : Fin 2 → ℝ×ℝ
  inside : ∀k, -(T) ≤ (pair k).1 ∧ (pair k).1 < (pair k).2 ∧ (pair k).2 < T
  coincide : ∀k, f (pair k).1 = f (pair k).2
  distinct : f (pair 0).1 ≠ f (pair 1).1
  exhaustive : ∀{s t}, -T≤s → s<t → t<T → f s=f t → ∃k, (s,t)=pair k

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount
#print axioms SolitonClassification.Rotating.IntegerTarget.GlobalCount.chart_of_box

