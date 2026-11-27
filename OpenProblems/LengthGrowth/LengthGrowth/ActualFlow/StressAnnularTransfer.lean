import LengthGrowth.ActualFlow.StressScaleCurrent

noncomputable section
open Filter Topology
namespace LengthGrowth.ActualFlow

/-- Contribution from all strictly larger stress bands. At the next smaller
scale the previous weights are halved. -/
def largerBandAction (mass : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j+1 => mass j + largerBandAction mass j / 2

/-- At or below the target stress, the exact geometric majorant has mass 4/3. -/
theorem smaller_band_bound {mass : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hn : ∀ n, 0 ≤ mass n) (tail : ∀ n, j≤n → mass n≤b) :
    (∑' n : ℕ, (1/4:ℝ)^n * mass (j+n)) ≤ (4/3)*b := by
  have major := (summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4)
    (by norm_num : (1/4:ℝ)<1)).mul_right b
  have bound (n : ℕ) : (1/4:ℝ)^n*mass (j+n)≤(1/4:ℝ)^n*b :=
    mul_le_mul_of_nonneg_left (tail _ (by omega)) (by positivity)
  have summ := Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hn (j+n))) bound major
  refine (summ.tsum_le_tsum bound major).trans_eq ?_
  rw [tsum_mul_right,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

private theorem larger_band_tail {mass : ℕ → ℝ} {b : ℝ} {N : ℕ}
    (hb : 0≤b) (tail : ∀ n, N≤n → mass n≤b) (j : ℕ) :
    largerBandAction mass (N+j) ≤ 2*b+(1/2:ℝ)^j*largerBandAction mass N := by
  induction j with
  | zero => simp; linarith
  | succ j ih =>
    rw [Nat.add_succ,largerBandAction, pow_succ]
    linarith only [ih,tail (N+j) (by omega)]

/-- Concentration inequality for the two-sided dyadic convolution. Indices
start with any band above the maximum stress of the selected time tail. -/
theorem annular_force_transfer {mass err : ℕ → ℝ} {E b : ℝ}
    (hn : ∀ n, 0≤mass n) (hb : 0≤b) (e0 : Tendsto err atTop (𝓝 0))
    (tail : ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n, N≤n → mass n≤b+ε)
    (transfer : ∀ j, E≤err j + (9/2)*((∑' n : ℕ, (1/4:ℝ)^n * mass (j+n)) +
      largerBandAction mass j)) : E≤15*b := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  let h := δ/15
  have hh : 0<h := by dsimp only [h]; positivity
  obtain ⟨N,ht⟩ := tail h hh
  have p := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1/2:ℝ)<1)
  have shift : Tendsto (fun j : ℕ => N+j) atTop atTop := by
    apply tendsto_atTop.2
    exact fun m => eventually_atTop.2 ⟨m,fun n hn => by omega⟩
  have lim : Tendsto (fun j : ℕ => err (N+j)+(9/2)*
        ((4/3)*(b+h)+2*(b+h)+(1/2:ℝ)^j*largerBandAction mass N)) atTop (𝓝 (15*b+δ)) := by
    have exactLimit : (0:ℝ)+(9/2)*(((4/3)*(b+h)+2*(b+h))+0*largerBandAction mass N) =
        15*b+δ := by dsimp only [h]; ring
    rw [←exactLimit]
    exact (e0.comp shift).add (tendsto_const_nhds.mul
      (tendsto_const_nhds.add (p.mul_const (largerBandAction mass N))))
  apply ge_of_tendsto' lim
  intro j
  have sm := smaller_band_bound (j:=N+j) hn (fun n hn => ht n (by omega))
  have lg := larger_band_tail (add_nonneg hb hh.le) ht j
  linarith only [transfer (N+j),sm,lg]

theorem vanishing_band_action {mass err : ℕ → ℝ} {E : ℝ}
    (hn : ∀ n, 0≤mass n) (e0 : Tendsto err atTop (𝓝 0)) (m0 : Tendsto mass atTop (𝓝 0))
    (transfer : ∀ j, E≤err j + (9/2)*((∑' n : ℕ, (1/4:ℝ)^n * mass (j+n)) +
      largerBandAction mass j)) : E≤0 := by
  have bound := annular_force_transfer (b:=0) hn le_rfl e0 (fun ε hε => by
    obtain ⟨N,hN⟩ := eventually_atTop.1 (m0.eventually_lt_const hε)
    exact ⟨N,fun n h => by simpa only [zero_add] using (hN n h).le⟩) transfer
  simpa only [mul_zero] using bound

end LengthGrowth.ActualFlow
