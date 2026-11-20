import LengthGrowth.ActualFlow.StrongArcCover
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open MeasureTheory Set
namespace LengthGrowth.ActualFlow.MacroscopicTurning

private def intervals (S : Finset (ℝ × ℝ)) := ⋃ I∈S, Ioo I.1 I.2

private theorem measurable_intervals (S : Finset (ℝ × ℝ)) : MeasurableSet (intervals S) :=
  (isOpen_biUnion (fun _ _ => isOpen_Ioo)).measurableSet

private theorem intervals_subset {k : ℝ→ℝ} {a b : ℝ} {S : Finset (ℝ × ℝ)}
    (hs : ∀I∈S,Lobe k a b I) : intervals S ⊆ Ioo a b := by
  intro x hx
  obtain ⟨I,hi⟩:=mem_iUnion.mp hx
  obtain ⟨hit,hxi⟩:=mem_iUnion.mp hi
  exact ⟨(hs I hit).left.trans_lt hxi.1,hxi.2.trans_le (hs I hit).right⟩

private theorem sum_eq_union {k f : ℝ→ℝ} {a b : ℝ} {S : Finset (ℝ × ℝ)}
    (hs : ∀I∈S,Lobe k a b I)
    (hd : ∀I∈S,∀J∈S, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2))
    (hf : Continuous f) :
    (∑ I∈S, ∫ x in I.1..I.2,f x) = ∫ x in intervals S, f x := by
  classical
  rw [intervals, integral_biUnion_finset S (fun _ _ => measurableSet_Ioo)
    (fun I hi J hj ne => hd I hi J hj ne)
    (fun I _ => (hf.integrableOn_Icc (a:=I.1) (b:=I.2)).mono_set Ioo_subset_Icc_self)]
  apply Finset.sum_congr rfl
  intro I hi
  rw [intervalIntegral.integral_of_le (hs I hi).ordered.le,integral_Ioc_eq_integral_Ioo]

theorem sum_lobe_integrals_le {k f : ℝ→ℝ} {a b : ℝ} (hab : a≤b) {S : Finset (ℝ × ℝ)}
    (hs : ∀I∈S,Lobe k a b I)
    (hd : ∀I∈S,∀J∈S, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2))
    (hf : Continuous f) (hf0 : ∀x,0≤f x) :
    (∑ I∈S,∫x in I.1..I.2,f x) ≤ ∫x in a..b,f x := by
  rw [sum_eq_union hs hd hf,intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo]
  exact setIntegral_mono_set (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (Filter.Eventually.of_forall hf0) (intervals_subset hs).eventuallyLE

/-- A continuous density supported on the selected high-curvature lobes can
be integrated using their full intervals, including both zero endpoints. -/
theorem sum_lobe_integrals_eq {k f : ℝ→ℝ} {a b : ℝ} (hab : a≤b) {S : Finset (ℝ × ℝ)}
    (hs : ∀I∈S,Lobe k a b I)
    (hd : ∀I∈S,∀J∈S, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2))
    (hf : Continuous f) (supp : ∀x∈Ioo a b, f x≠0 → ∃I∈S,x∈Ioo I.1 I.2) :
    (∑ I∈S,∫x in I.1..I.2,f x) = ∫x in a..b,f x := by
  rw [sum_eq_union hs hd hf,intervalIntegral.integral_of_le hab,integral_Ioc_eq_integral_Ioo]
  have z : (∫x in Ioo a b \ intervals S, f x)=0 := by
    have eq := setIntegral_congr_fun (μ:=volume) (measurableSet_Ioo.diff (measurable_intervals S))
      (f:=f) (g:=fun _ => (0:ℝ)) (by
        intro x hx
        by_contra nz
        obtain ⟨I,hi,mem⟩:=supp x hx.1 nz
        exact hx.2 (mem_iUnion.mpr ⟨I,mem_iUnion.mpr ⟨hi,mem⟩⟩))
    simpa using eq
  rw [setIntegral_sdiff (measurable_intervals S) (hf.integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (intervals_subset hs)] at z
  linarith

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.sum_lobe_integrals_eq
