import SolitonClassification.Rotating.ResetHullSamples

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set DyadicReset
set_option maxHeartbeats 1500000

private theorem covered_cell (N : ℕ) (hN : 0<N) (v : ℝ) (h0 : 0≤v) (h1 : v≤N) :
    ∃i : ℕ, i<N ∧ ∃t∈unitCell, v=(i:ℝ)+t := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : 0<N ∧ v≤N
    · obtain ⟨i,lo,t,ht,e⟩ := ih h.1 h.2
      exact ⟨i,by omega,t,ht,e⟩
    · have low : (N:ℝ)≤v := by
        by_cases hn : N=0
        · simpa only [hn,Nat.cast_zero] using h0
        · exact le_of_not_ge (fun q => h ⟨by omega,q⟩)
      refine ⟨N,by omega,v-N,⟨by linarith,by push_cast at h1; linarith⟩,by ring⟩

private theorem actual_on_prefix {n : ℤ} {N : ℕ} (T : PolynomialTape n N)
    (hN : 0<N) (cap : N≤4000) (hs : |step n|≤1/125)
    (first : T.node 0=initialNode) {c : Parameters} (hc : c∈cube)
    (v : ℝ) (lo : 0≤v) (hi : v≤N) :
    HasDerivAt (fun u => wideFlow (u,shootingInitial phase c))
      (field (wideFlow (v*step n,shootingInitial phase c))) (v*step n) := by
  obtain ⟨i,bi,t,bt,e⟩ := covered_cell N hN v lo hi
  rw [e]
  exact (prefix_physical T hN cap hs first hc i bi t bt).1

theorem sampled_arc_follows_equation {c : Parameters} (hc : c∈cube) (s : ℝ)
    (hs : s∈Icc lowerTime upperTime) :
    HasDerivAt (fun u => wideFlow (u,shootingInitial phase c))
      (field (wideFlow (s,shootingInitial phase c))) s := by
  by_cases pos : 0≤s
  · have p : 0<step Middle.hn := by norm_num [step,Middle.hn,Middle.hd]
    have v : s/step Middle.hn≤(640:ℕ) := (div_le_iff₀ p).mpr (by
      change s≤(640:ℝ)*step Middle.hn
      have h : s≤636*step Middle.hn := hs.2
      linarith)
    have h := actual_on_prefix HullPlus.tape (by decide) (by decide) (signedHalfSteps true)
      ((HullPlus.node_at 0 (by decide)).trans rfl) hc _ (div_nonneg pos p.le) v
    simpa only [div_mul_cancel₀ _ p.ne'] using h
  · have p : step (-Middle.hn)<0 := by norm_num [step,Middle.hn,Middle.hd]
    have v : s/step (-Middle.hn)≤(3200:ℕ) := (div_le_iff_of_neg p).mpr (by
      change (3200:ℝ)*step (-Middle.hn)≤s
      have h : 3193*step (-Middle.hn)≤s := hs.1
      linarith)
    have h := actual_on_prefix HullMinus.tape (by decide) (by decide) (signedHalfSteps false)
      ((HullMinus.node_at 0 (by decide)).trans rfl) hc _ (div_nonneg_of_nonpos (le_of_not_ge pos) p.le) v
    simpa only [div_mul_cancel₀ _ p.ne] using h

/-- The very arc enclosing the square has the physical unit-speed tangent. -/
theorem sampled_arc_unit_tangent {c : Parameters} (hc : c∈cube) (s : ℝ)
    (hs : s∈Icc lowerTime upperTime) :
    let θ := wideFlow (s,shootingInitial phase c) 5
    HasDerivAt (fun u => (segmentPosition c u).1) (Real.cos θ) s ∧
    HasDerivAt (fun u => (segmentPosition c u).2) (Real.sin θ) s := by
  let z := fun u : ℝ => wideFlow (u,shootingInitial phase c)
  have dz (j : Fin 6) : HasDerivAt (fun u => z u j) (field (z s) j) s :=
    (ContinuousLinearMap.proj j : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (sampled_arc_follows_equation hc s hs)
  let k := fun u => z u 0
  let p := fun u => z u 2
  let q := fun u => z u 3
  let θ := fun u => z u 5
  have dp : HasDerivAt p (-k s*q s) s := dz 2
  have dq : HasDerivAt q (1+k s*p s) s := dz 3
  have dt : HasDerivAt θ (k s) s := dz 5
  exact ⟨ClosedSimilarity.profileX_hasDerivAt k p q θ s dp dq dt,
    ClosedSimilarity.profileY_hasDerivAt k p q θ s dp dq dt⟩

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.sampled_arc_unit_tangent
