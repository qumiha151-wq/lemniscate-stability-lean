import LengthGrowth.ActualFlow.CriticalDensityFlow
import LengthGrowth.ActualFlow.CriticalDensityIndex
import LengthGrowth.ActualFlow.CriticalDensitySubpower

/-! Subpower growth and its converse for the canonical half-RMS index
computed from each individual material slice of one free elastic flow. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

private def coefficient (η : ℝ) : ℝ := η/(4096*(1+η))

private theorem coefficient_pos {η : ℝ} (h : 0<η) : 0<coefficient η := by
  dsimp [coefficient]
  positivity

private theorem stress_of_small_index {U z n η : ℝ} (hu : 0<U) (hn : 0≤n) (he : 0<η)
    (large : (coefficient η)⁻¹^(3:ℝ) ≤ U)
    (small : n ≤ coefficient η*U^(1/3:ℝ))
    (force : Real.sqrt U ≤ z+2048*(n+1)*Real.sqrt (n+1)) :
    Real.sqrt U ≤ (1+η)*z := by
  let K := coefficient η
  have kp : 0<K := coefficient_pos he
  have ee : 4096*K*(1+η)=η := by
    dsimp [K,coefficient]
    field_simp [(show 1+η≠0 by positivity)]
  have k1 : 2*K≤1 := by
    dsimp [K,coefficient]
    rw [←mul_div_assoc,div_le_one (by positivity)]
    linarith
  have pw := Real.rpow_le_rpow
    (Real.rpow_nonneg (inv_nonneg.mpr kp.le) (3:ℝ)) large (by norm_num : (0:ℝ)≤1/3)
  rw [←Real.rpow_mul (inv_nonneg.mpr kp.le),show (3:ℝ)*(1/3)=1 by norm_num,Real.rpow_one] at pw
  have one : 1≤K*U^(1/3:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left pw kp.le
    rwa [mul_inv_cancel₀ kp.ne'] at hh
  have count : n+1≤(2*K)*U^(1/3:ℝ) := by
    change n ≤ K*_ at small
    linarith only [small,one]
  have bound := count_deficit_to_power (U:=U) (z:=z) (C:=2048) (σ:=1/3)
    hu (show 0≤n+1 by linarith) (show 0≤2*K by positivity) (by norm_num) count force
  rw [show (1-3*(1/3:ℝ))/2=0 by norm_num,Real.rpow_zero,one_mul,
    show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (by positivity),Real.rpow_one,←Real.sqrt_eq_rpow] at bound
  have sqrtK : Real.sqrt (2*K)≤1 := by simpa using Real.sqrt_le_sqrt k1
  have wx := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left sqrtK (show 0≤2*K by positivity)) (Real.sqrt_nonneg U)
  have gap : Real.sqrt U-z ≤ 4096*K*Real.sqrt U := by
    linarith only [bound,wx]
  have den : 0≤1+η := by positivity
  nlinarith only [mul_le_mul_of_nonneg_left gap den,
    congrArg (fun q : ℝ => q*Real.sqrt U) ee]

/-- The least material half-RMS reversal index may approach the cube-root
scale with no fixed power saving. The large-product cutoff can depend on δ. -/
theorem length_energy_of_half_rms_index_little_o (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0≤T)
    (little : ∀δ : ℝ, 0<δ → ∃M : ℝ, ∀t, (ht : T<t) → M≤c.normalizedProduct t →
      ((c.regularPositionAt (hT.trans ht.le)).criticalDensityIndex : ℝ)
        ≤ δ*c.normalizedProduct t^(1/3:ℝ)) :
    (∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε)) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  apply c.length_energy_of_subpower_deficit hf hT
  intro η he
  obtain ⟨M,hm⟩ := little (coefficient η) (coefficient_pos he)
  refine ⟨max M ((coefficient η)⁻¹^(3:ℝ)),fun t ht high => ?_⟩
  let p := c.regularPositionAt (hT.trans ht.le)
  exact stress_of_small_index (mul_pos (c.energy_pos (hT.trans ht.le)) (c.length_pos (hT.trans ht.le)))
    (show 0≤(p.criticalDensityIndex:ℝ) by positivity) he ((le_max_right ..).trans high)
    (hm t ht ((le_max_left ..).trans high))
    (p.criticalDensity_dissipation_bound p.criticalDensityIndex p.criticalDensityIndex_spec)

/-- Failure of the exponent 1/4+ε forces the least material reversal index
above an explicit multiple of U^(1/3) at arbitrarily late times on the same
flow, with arbitrarily large U. -/
theorem arbitrarily_late_half_rms_index_of_superquarter (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T ε : ℝ} (hT : 0≤T) (he : 0<ε)
    (fail : ¬∃ C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε)) :
    ∀ S, (hs : T≤S) → ∀ M : ℝ, ∃ t, ∃ ht : S<t, M≤c.normalizedProduct t ∧
      ((2*ε)/(4096*(1+2*ε)))*c.normalizedProduct t^(1/3:ℝ) <
        ((c.regularPositionAt ((hT.trans hs).trans ht.le)).criticalDensityIndex : ℝ) := by
  intro S hs M
  let η := 2*ε
  have ep : 0<η := mul_pos (by norm_num) he
  obtain ⟨t,ht,high,gap⟩ := c.arbitrarily_late_stress_deficit_of_superquarter hf hT he fail
    S hs (max M ((coefficient η)⁻¹^(3:ℝ)))
  refine ⟨t,ht,(le_max_left ..).trans high,?_⟩
  have t0 := (hT.trans hs).trans ht.le
  let p := c.regularPositionAt t0
  change coefficient η*c.normalizedProduct t^(1/3:ℝ) < (p.criticalDensityIndex:ℝ)
  by_contra! small
  have bound := stress_of_small_index (mul_pos (c.energy_pos t0) (c.length_pos t0))
    (show 0≤(p.criticalDensityIndex:ℝ) by positivity) ep ((le_max_right ..).trans high) small
    (p.criticalDensity_dissipation_bound p.criticalDensityIndex p.criticalDensityIndex_spec)
  exact (not_lt_of_ge bound) gap

#print axioms length_energy_of_half_rms_index_little_o
#print axioms arbitrarily_late_half_rms_index_of_superquarter

/-- The times and the products tend to infinity along one explicit sequence
of choices, and the same fixed ε-dependent density bound holds throughout. -/
theorem exists_half_rms_index_sequence_of_superquarter (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T ε : ℝ} (hT : 0≤T) (he : 0<ε)
    (fail : ¬∃ C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε)) :
    ∃ τ : ℕ→ℝ, ∃ hτ : ∀j, 0≤τ j, Tendsto τ atTop atTop ∧
      Tendsto (fun j => c.normalizedProduct (τ j)) atTop atTop ∧
      ∀j, ((2*ε)/(4096*(1+2*ε)))*c.normalizedProduct (τ j)^(1/3:ℝ) <
        ((c.regularPositionAt (hτ j)).criticalDensityIndex : ℝ) := by
  classical
  have witness (j : ℕ) := c.arbitrarily_late_half_rms_index_of_superquarter hf hT he fail
    (max T (j:ℝ)) (le_max_left ..) j
  let τ := fun j => Classical.choose (witness j)
  have hp (j : ℕ) := Classical.choose_spec (witness j)
  have tpos (j : ℕ) : 0≤τ j := (hT.trans (le_max_left ..)).trans (hp j).choose.le
  have growing (g : ℕ→ℝ) (hg : ∀ j : ℕ, (j:ℝ)≤g j) : Tendsto g atTop atTop := by
    apply tendsto_atTop.2
    intro a
    obtain ⟨N,hN⟩ := exists_nat_gt a
    filter_upwards [eventually_ge_atTop N] with j hj
    exact (hN.le.trans (by exact_mod_cast hj : (N:ℝ)≤j)).trans (hg j)
  exact ⟨τ,tpos,growing _ (fun j => (le_max_right ..).trans (hp j).choose.le),
    growing _ (fun j => (hp j).choose_spec.1),fun j => (hp j).choose_spec.2⟩

#print axioms exists_half_rms_index_sequence_of_superquarter
end LengthGrowth.ActualFlow.ForwardImmersion
