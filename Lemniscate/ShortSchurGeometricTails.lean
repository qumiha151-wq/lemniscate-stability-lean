import Lemniscate.GeometricTails
import Lemniscate.ShortSchurHighData
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! Complete two-sided geometric tails, including arbitrary translations.
Only the scalar geometric-series identities are used here. -/
namespace Lemniscate
open CoarseArithmetic Finset

theorem short_hasSum_int_natAbs (G : ℕ → ℝ) (S : ℝ)
    (hG : HasSum G S) (hzero : G 0 = 0) :
    HasSum (fun k : ℤ => G k.natAbs) (2*S) := by
  have hp : HasSum (fun k : ℕ => G (k:ℤ).natAbs) S := by
    simpa only [Int.natAbs_natCast] using hG
  have hn : HasSum (fun k : ℕ => G (-(k:ℤ)).natAbs) S := by
    simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hG
  have h := HasSum.of_nat_of_neg (f := fun k : ℤ => G k.natAbs) hp hn
  simpa only [Int.natAbs_zero,hzero,sub_zero,two_mul] using h

theorem short_finite_translated_geometric_tail (z : ℚ)
    (hz : 0 ≤ z) (hz1 : ‖(z:ℝ)‖ < 1)
    (I : Finset ℤ) (n : ℤ) (L : ℕ)
    (hI : ∀ m ∈ I, L ≤ (m-n).natAbs) :
    (∑ m ∈ I, ((m-n).natAbs:ℝ)*(z:ℝ)^(m-n).natAbs) ≤
      2*(tail1 z L:ℝ) := by
  let G (k : ℕ) : ℝ := if L ≤ k then (k:ℝ)*(z:ℝ)^k else 0
  have hshift : HasSum (fun k : ℕ => G (k+L)) (tail1 z L:ℝ) := by
    simpa [G] using tail1_sound z hz1 L
  have hhead : (∑ k ∈ Finset.range L, G k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact if_neg (by have := Finset.mem_range.mp hk; omega)
  have hG : HasSum G (tail1 z L:ℝ) := by
    apply (hasSum_nat_add_iff' L).mp
    simpa only [hhead,sub_zero] using hshift
  have hzero : G 0 = 0 := by
    dsimp only [G]
    split_ifs <;> simp only [Nat.cast_zero,zero_mul]
  have hZ := short_hasSum_int_natAbs G (tail1 z L:ℝ) hG hzero
  have htrans : HasSum (fun m : ℤ => G (m-n).natAbs) (2*(tail1 z L:ℝ)) := by
    have h := (Equiv.addRight (-n)).hasSum_iff.mpr hZ
    change HasSum (fun m : ℤ => G (m+ -n).natAbs) _ at h
    simpa only [Function.comp_def,sub_eq_add_neg] using h
  have hnonneg (m : ℤ) : 0 ≤ G (m-n).natAbs := by
    have hzR : 0 ≤ (z:ℝ) := Rat.cast_nonneg.mpr hz
    dsimp only [G]
    split_ifs <;> positivity
  have h := Summable.sum_le_tsum I (fun m _ => hnonneg m) htrans.summable
  rw [htrans.tsum_eq] at h
  have heq : (∑ m ∈ I, G (m-n).natAbs) =
      ∑ m ∈ I, ((m-n).natAbs:ℝ)*(z:ℝ)^(m-n).natAbs := by
    apply Finset.sum_congr rfl
    intro m hm
    exact if_pos (hI m hm)
  rw [heq] at h
  exact h

noncomputable def shortOuterEnvelope (k : ℕ) : ℝ :=
  (H:ℝ)*(k+7)*(qb:ℝ)^(k-7)

private theorem short_outer_envelope_sums :
    HasSum (fun k : ℕ => shortOuterEnvelope (k+15))
      ((shortInsideRowTail:ℝ)/(2*10^6)) ∧
    HasSum (fun k : ℕ => shortOuterEnvelope (k+15)^2)
      ((shortCrossTailSquare:ℝ)/(14*10^12)) := by
  have hq : ‖(qb:ℝ)‖ < 1 := by norm_num [qb]
  have hq2 : ‖((qb^2:ℚ):ℝ)‖ < 1 := by norm_num [qb]
  have h0 := hasSum_geometric_moment_zero (qb:ℝ) hq
  have h1 := hasSum_geometric_moment_one (qb:ℝ) hq
  have h02 := hasSum_geometric_moment_zero ((qb^2:ℚ):ℝ) hq2
  have h12 := hasSum_geometric_moment_one ((qb^2:ℚ):ℝ) hq2
  have h22 := hasSum_geometric_moment_two ((qb^2:ℚ):ℝ) hq2
  constructor
  · convert! (h1.add (h0.mul_left 22)).mul_left ((H:ℝ)*(qb:ℝ)^8) using 1
    · funext k
      simp only [shortOuterEnvelope,show k+15-7 = k+8 by omega,
        Nat.cast_add,Nat.cast_ofNat,pow_add]
      ring
    · norm_num [shortInsideRowTail,tail1,moment,H,rhi,qb]
  · convert! ((h22.add (h12.mul_left 44)).add (h02.mul_left 484)).mul_left
      ((H:ℝ)^2*((qb^2:ℚ):ℝ)^8) using 1
    · funext k
      have hp : ((qb:ℝ)^(k+8))^2 = ((qb:ℝ)^2)^(k+8) := by
        rw [← pow_mul,← pow_mul,Nat.mul_comm (k+8) 2]
      simp only [shortOuterEnvelope,show k+15-7 = k+8 by omega,mul_pow]
      rw [hp,pow_add]
      simp only [Rat.cast_pow,Nat.cast_add,Nat.cast_ofNat]
      ring
    · norm_num [shortCrossTailSquare,tail2,tail1,moment,H,rhi,qb]

private theorem short_finite_natAbs_tail_bound (G : ℕ → ℝ) (S : ℝ)
    (hG : HasSum (fun k : ℕ => G (k+15)) S)
    (hnonneg : ∀ k, 0 ≤ G k) (I : Finset ℤ)
    (hI : ∀ m ∈ I, 15 ≤ m.natAbs) : (∑ m ∈ I, G m.natAbs) ≤ 2*S := by
  let F (k : ℕ) : ℝ := if 15 ≤ k then G k else 0
  have hhead : (∑ k ∈ Finset.range 15, F k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact if_neg (by have := Finset.mem_range.mp hk; omega)
  have hF : HasSum F S := by
    apply (hasSum_nat_add_iff' 15).mp
    simpa [F,hhead] using hG
  have hZ := short_hasSum_int_natAbs F S hF (by simp [F])
  have h := Summable.sum_le_tsum I (fun m _ => by
    dsimp only [F]
    split_ifs
    · exact hnonneg _
    · exact le_rfl) hZ.summable
  rw [hZ.tsum_eq] at h
  have heq : (∑ m ∈ I, F m.natAbs) = ∑ m ∈ I, G m.natAbs := by
    apply Finset.sum_congr rfl
    intro m hm
    exact if_pos (hI m hm)
  rwa [heq] at h

theorem short_finite_outer_envelope_tails (I : Finset ℤ)
    (hI : ∀ m ∈ I, 15 ≤ m.natAbs) :
    (∑ m ∈ I, shortOuterEnvelope m.natAbs) ≤ (shortInsideRowTail:ℝ)/10^6 ∧
    (∑ m ∈ I, shortOuterEnvelope m.natAbs^2) ≤ (shortCrossTailSquare:ℝ)/(7*10^12) := by
  have hpos (k : ℕ) : 0 ≤ shortOuterEnvelope k := by
    have hH : 0 ≤ (H:ℝ) := by norm_num [H,rhi,qb]
    have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
    dsimp only [shortOuterEnvelope]
    positivity
  have h1 := short_finite_natAbs_tail_bound shortOuterEnvelope _
    short_outer_envelope_sums.1 hpos I hI
  have h2 := short_finite_natAbs_tail_bound (fun k => shortOuterEnvelope k^2) _
    short_outer_envelope_sums.2 (fun k => sq_nonneg _) I hI
  constructor
  · convert h1 using 1 <;> ring
  · convert h2 using 1 <;> ring

end Lemniscate
