import Migration.LowDefectModeSums
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
open Finset
namespace MigrationGeometry.Flow.LowDefect

def inverseWeight (n : ℤ) : ℝ :=
  if n=0 ∨ n=1 ∨ n=2 then 0 else 1/((n:ℝ)^2*((n:ℝ)-1)^2)

private def tailWeight (k : ℕ) : ℝ := 1/(((k:ℝ)+4)^2*((k:ℝ)+3)^2)
private def cap (k : ℕ) : ℝ := 1/(3*((k:ℝ)+3)^3)

private theorem step_cap (k : ℕ) : tailWeight k + cap (k+1) ≤ cap k := by
  dsimp [tailWeight,cap]
  push_cast
  have a : 0<(k:ℝ)+3 := by positivity
  have b : 0<(k:ℝ)+4 := by positivity
  rw [show (k:ℝ)+1+3=(k:ℝ)+4 by ring]
  field_simp
  nlinarith [sq_nonneg (k:ℝ),Nat.cast_nonneg (α:=ℝ) k]

private theorem tail_bound : Summable tailWeight ∧ (∑' k,tailWeight k)≤1/81 := by
  have pos (k) : 0≤tailWeight k := by dsimp [tailWeight]; positivity
  have sum (N : ℕ) : (∑k ∈ range N,tailWeight k)+cap N≤cap 0 := by
    induction N with
    | zero => simp
    | succ n hn => rw [sum_range_succ]; linarith [step_cap n]
  have sums (N : ℕ) : (∑k ∈ range N,tailWeight k)≤1/81 := by
    have cc : 0≤cap N := by dsimp [cap]; positivity
    have z : cap 0=1/81 := by norm_num [cap]
    linarith [sum N]
  exact ⟨summable_of_sum_range_le pos sums,Real.tsum_le_of_sum_range_le pos sums⟩

theorem inverseWeight_sum : Summable inverseWeight ∧ (∑' n, inverseWeight n) ≤ (575/1000)^2 := by
  let A := ∑' i,tailWeight i
  have h := tail_bound.1.hasSum
  have pos (k : ℕ) : inverseWeight ((k+4:ℕ):ℤ)=tailWeight k := by
    simp only [inverseWeight,tailWeight,Nat.cast_add,Nat.cast_ofNat,Int.cast_add,Int.cast_natCast,Int.cast_ofNat]
    rw [if_neg (by omega)]
    ring_nf
  have neg (k : ℕ) : inverseWeight (-(((k+2:ℕ):ℤ)+1))=tailWeight k := by
    simp only [inverseWeight,tailWeight,Nat.cast_add,Nat.cast_ofNat,Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_ofNat,Int.cast_one]
    rw [if_neg (by omega)]
    ring_nf
  have s1 : HasSum (fun k : ℕ=>inverseWeight k) (A+1/36) := by
    have p := (hasSum_nat_add_iff (f:=fun k : ℕ=>inverseWeight k) 4).mp (by simpa only [pos] using h)
    have f : (∑ k ∈ range 4,inverseWeight (k:ℤ))=1/36 := by norm_num [Finset.sum_range_succ,inverseWeight]
    rw [f] at p
    exact p
  have s2 : HasSum (fun k : ℕ=>inverseWeight (-(k+1:ℤ))) (A+(1/4+1/36)) := by
    have p := (hasSum_nat_add_iff (f:=fun k : ℕ=>inverseWeight (-(k+1:ℤ))) 2).mp (by simpa only [neg] using h)
    have f : (∑ k ∈ range 2,inverseWeight (-(k+1:ℤ)))=1/4+1/36 := by norm_num [Finset.sum_range_succ,inverseWeight]
    rw [f] at p
    exact p
  have t := s1.of_nat_of_neg_add_one s2
  refine ⟨t.summable,?_⟩
  rw [t.tsum_eq]
  dsimp [A]
  linarith [tail_bound.2]

end MigrationGeometry.Flow.LowDefect
#print axioms MigrationGeometry.Flow.LowDefect.inverseWeight_sum
