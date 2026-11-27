import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open Finset Filter Set
open scoped Topology
namespace LengthGrowth.ActualFlow.TurningEnvelope

def multiplicity {n : ℕ} (u : Fin n → ℝ) (a : ℝ) : ℝ :=
  ∑ i, if u i=a then (1:ℝ) else 0

private theorem count_nonneg {n : ℕ} (u : Fin n→ℝ) (a : ℝ) : 0≤multiplicity u a := by
  exact sum_nonneg fun i _ => by split <;> norm_num

theorem sum_at_endpoints {n : ℕ} (u : Fin n→ℝ) (s : Finset ℝ)
    (hu : ∀i, u i∈s) (V : ℝ→ℝ) : ∑ a∈s, multiplicity u a * V a = ∑ i, V (u i) := by
  classical
  simp_rw [multiplicity,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul,hu i]

/-- The angular velocities of a maximizing family are bounded by n times
    their one-sided spread. Coincident right and left endpoints cancel with
    their multiplicities, including when several arcs share one endpoint. -/
theorem rate_of_variations {n : ℕ} (l r : Fin n→ℝ) (θ V : ℝ→ℝ) {ref rate : ℝ}
    (pos : 0≤rate)
    (maxV : ∀ x, IsLocalMax θ x → V x ≤ ref+rate)
    (minV : ∀ x, IsLocalMin θ x → ref ≤ V x)
    (opt : ∀ x, ∀ᶠ h in 𝓝 x,
      (multiplicity r x-multiplicity l x)*(θ h-θ x)≤0) :
    ∑ i, (V (r i)-V (l i)) ≤ (n:ℝ)*rate := by
  classical
  let s : Finset ℝ := Finset.univ.image r ∪ Finset.univ.image l
  have hr (i : Fin n) : r i ∈ s := Finset.mem_union_left _ (mem_image_of_mem r (mem_univ i))
  have hl (i : Fin n) : l i ∈ s := Finset.mem_union_right _ (mem_image_of_mem l (mem_univ i))
  have localBound (a : ℝ) : (multiplicity r a-multiplicity l a)*(V a-ref)≤multiplicity r a*rate := by
    rcases lt_trichotomy (multiplicity l a) (multiplicity r a) with h|h|h
    · have p := sub_pos.mpr h
      have ismax : IsLocalMax θ a := (opt a).mono fun x hx =>
        sub_nonpos.mp (nonpos_of_mul_nonpos_right hx p)
      have H := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr (maxV a ismax)) p.le
      exact H.trans (mul_le_mul_of_nonneg_right (by linarith [count_nonneg l a]) pos)
    · rw [h,sub_self,zero_mul]
      exact mul_nonneg (count_nonneg r a) pos
    · have p := sub_neg.mpr h
      have ismin : IsLocalMin θ a := (opt a).mono fun x hx =>
        sub_nonneg.mp (nonneg_of_mul_nonpos_right hx p)
      exact (mul_nonpos_of_nonpos_of_nonneg p.le (sub_nonneg.mpr (minV a ismin))).trans
        (mul_nonneg (count_nonneg r a) pos)
  have bound := sum_le_sum (s:=s) (fun a _ => localBound a)
  have nr := sum_at_endpoints r s hr (fun _ => (1:ℝ))
  have nl := sum_at_endpoints l s hl (fun _ => (1:ℝ))
  simp at nr nl
  simp_rw [sub_mul,mul_sub] at bound
  simp only [sum_sub_distrib,←sum_mul,sum_at_endpoints r s hr V,sum_at_endpoints l s hl V,nr,nl] at bound
  rw [sum_sub_distrib]
  linarith

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.rate_of_variations
