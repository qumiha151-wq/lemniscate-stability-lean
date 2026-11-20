import LengthGrowth.ActualFlow.SharpVirial
import LengthGrowth.ActualFlow.GrowthEquivalence

/-! The sharp lower obstruction on the fourth-root length scale. -/
noncomputable section
open Set FreeElasticScalar
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem inverse_energy_of_length_envelope (hflow : c.IsNormalFEF) {A s t : ℝ}
    (hA : 0<A) (hs : 0≤s) (hst : s≤t)
    (bound : ∀ x ∈ Icc s t, c.length x ≤ A*fourthRoot (1+x)) :
    (c.energy s)⁻¹ + (16*Real.pi^2/A^3)*(fourthRoot (1+t)-fourthRoot (1+s)) ≤ (c.energy t)⁻¹ := by
  let G := fun x => (c.energy x)⁻¹ - (16*Real.pi^2/A^3)*fourthRoot (1+x)
  have sub : Icc s t ⊆ Ici 0 := fun _ hx => hs.trans hx.1
  have hqc : Continuous (fun x : ℝ => fourthRoot (1+x)) :=
    fourthRoot_continuous.comp (continuous_const.add continuous_id)
  have hGc : ContinuousOn G (Icc s t) := ((c.energy_continuousOn.inv₀
    (fun x hx => (c.energy_pos hx).ne')).sub (continuousOn_const.mul hqc.continuousOn)).mono sub
  let d := fun x => c.dissipation x/c.energy x^2 - (4*Real.pi^2)/(A^3*fourthRoot (1+x)^3)
  have hdiff (x : ℝ) (hx : x ∈ Ioo s t) : HasDerivAt G (d x) x := by
    have hp := hs.trans_lt hx.1
    have hr : 0<1+x := by linarith
    have hq := (fourthRoot_hasDerivAt hr).comp x ((hasDerivAt_id x).const_add 1)
    simp only [mul_one] at hq
    convert! ((c.energy_hasDerivAt_normal hflow hp).inv (c.energy_pos hp.le).ne').sub
      (hq.const_mul (16*Real.pi^2/A^3)) using 1
    dsimp only [d]
    norm_num only [Pi.inv_apply,neg_neg]
    field_simp [hA.ne',(fourthRoot_pos hr).ne',(c.energy_pos hp.le).ne']
    ring
  have mono : MonotoneOn G (Icc s t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) hGc (f':=d)
    · intro x hx
      exact (hdiff x (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have ht0 := (hs.trans_lt hx.1).le
      have hL := c.length_pos ht0
      have hE := c.energy_pos ht0
      have vir := c.sharp_virial ht0
      have hsplit : 4*Real.pi^2/c.length x^3 ≤ c.dissipation x/c.energy x^2 := by
        apply (div_le_div_iff₀ (pow_pos hL 3) (pow_pos hE 2)).mpr
        exact vir
      have hlen : c.length x^3 ≤ A^3*fourthRoot (1+x)^3 := by
        simpa [mul_pow] using pow_le_pow_left₀ hL.le (bound x ⟨hx.1.le,hx.2.le⟩) 3
      exact sub_nonneg.mpr ((div_le_div_of_nonneg_left (by positivity) (pow_pos hL 3) hlen).trans hsplit)
  have hm := mono (show s ∈ Icc s t from ⟨le_rfl,hst⟩) (show t ∈ Icc s t from ⟨hst,le_rfl⟩) hst
  dsimp only [G] at hm
  linarith

theorem length_lower_of_upper_envelope (hflow : c.IsNormalFEF) {A s t : ℝ}
    (hA : 0<A) (hs : 0≤s) (hst : s≤t)
    (bound : ∀ x ∈ Icc s t, c.length x ≤ A*fourthRoot (1+x)) :
    2*Real.pi^2*(c.energy s)⁻¹ + (32*Real.pi^4/A^3)*(fourthRoot (1+t)-fourthRoot (1+s))
      ≤ c.length t := by
  have he := c.energy_pos (hs.trans hst)
  have static : (2*Real.pi^2)*(c.energy t)⁻¹ ≤ c.length t := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ he).mpr (by simpa [mul_comm] using c.sharp_energy_length (hs.trans hst))
  have h := mul_le_mul_of_nonneg_left (c.inverse_energy_of_length_envelope hflow hA hs hst bound)
    (show 0≤2*Real.pi^2 by positivity)
  apply le_trans _ (h.trans static)
  apply le_of_eq
  ring

private theorem fourthRoot_eventually_above (S B : ℝ) :
    ∃ t, S<t ∧ B<fourthRoot (1+t) := by
  let m := max 1 (max S B)
  have hm : 1≤m := le_max_left _ _
  have hs : S≤m := (le_max_left S B).trans (le_max_right _ _)
  have hb : B≤m := (le_max_right S B).trans (le_max_right _ _)
  let t := m^4+m+1
  have ht : S<t := by dsimp [t]; linarith [sq_nonneg (m^2),pow_nonneg (zero_le_one.trans hm) 4]
  have ht0 : 0<1+t := by dsimp [t]; linarith [pow_nonneg (zero_le_one.trans hm) 4]
  refine ⟨t,ht,hb.trans_lt ?_⟩
  by_contra! h
  have h4 := pow_le_pow_left₀ (fourthRoot_pos ht0).le h 4
  rw [fourthRoot_pow_four ht0.le] at h4
  dsimp only [t] at h4
  linarith

/-- An eventual upper coefficient A forces every lower coefficient
below 32π⁴/A³ on the same solution. -/
theorem eventual_lower_from_upper (hflow : c.IsNormalFEF) {A B s : ℝ}
    (hA : 0<A) (hs : 0≤s) (hB : B < 32*Real.pi^4/A^3)
    (up : ∀ x, s≤x → c.length x ≤ A*fourthRoot (1+x)) :
    ∃ T, s≤T ∧ ∀ t, T≤t → B*fourthRoot (1+t) < c.length t := by
  let U := 32*Real.pi^4/A^3
  have hp : 0<U-B := sub_pos.mpr hB
  obtain ⟨T,hT,hq⟩ := fourthRoot_eventually_above s (U*fourthRoot (1+s)/(U-B))
  refine ⟨T,hT.le,fun t ht => ?_⟩
  have hm := fourthRoot_mono (show 1+T≤1+t by linarith)
  have hlarge := (div_lt_iff₀ hp).mp (hq.trans_le hm)
  have h := c.length_lower_of_upper_envelope hflow hA hs (hT.le.trans ht) (fun x hx => up x hx.1)
  change 2*Real.pi^2*(c.energy s)⁻¹+U*(fourthRoot (1+t)-fourthRoot (1+s)) ≤ c.length t at h
  have hpos := c.energy_pos hs
  nlinarith only [hlarge,h,show 0≤2*Real.pi^2*(c.energy s)⁻¹ by positivity]

/-- For an eventual length coefficient A, the eventual energy-length
upper coefficient can be taken arbitrarily close to A⁴/(16π²). -/
theorem eventual_energyLength_from_upper (hflow : c.IsNormalFEF) {A K s : ℝ}
    (hA : 0<A) (hs : 0≤s) (hK : A^4 < 16*Real.pi^2*K)
    (up : ∀ x, s≤x → c.length x ≤ A*fourthRoot (1+x)) :
    ∃ T, s≤T ∧ ∀ t, T≤t → c.energy t*c.length t < K := by
  let U := 16*Real.pi^2/A^3
  have hKpos : 0<K := by
    by_contra! hn
    have bad := mul_nonpos_of_nonneg_of_nonpos (show 0≤16*Real.pi^2 by positivity) hn
    linarith [pow_pos hA 4]
  have hg : A < K*U := by
    dsimp [U]
    rw [←mul_div_assoc]
    apply (lt_div_iff₀ (pow_pos hA 3)).mpr
    nlinarith only [hK]
  have hpos := sub_pos.mpr hg
  obtain ⟨T,hT,hq⟩ := fourthRoot_eventually_above s (K*U*fourthRoot (1+s)/(K*U-A))
  refine ⟨T,hT.le,fun t ht => ?_⟩
  have hst := hT.le.trans ht
  have he := c.energy_pos (hs.trans hst)
  have hm := fourthRoot_mono (show 1+T≤1+t by linarith)
  have hh := (div_lt_iff₀ hpos).mp (hq.trans_le hm)
  have inv := c.inverse_energy_of_length_envelope hflow hA hs hst (fun x hx => up x hx.1)
  change (c.energy s)⁻¹ + U*(fourthRoot (1+t)-fourthRoot (1+s)) ≤ (c.energy t)⁻¹ at inv
  have h := mul_le_mul_of_nonneg_left inv hKpos.le
  have hEs := c.energy_pos hs
  have hcap : c.length t < K / c.energy t := by
    rw [div_eq_mul_inv]
    nlinarith only [hh,h,up t hst,show 0 ≤ K*(c.energy s)⁻¹ by positivity]
  simpa only [mul_comm (c.length t)] using (lt_div_iff₀ he).mp hcap

/-- Every positive coefficient below the expanding circle coefficient is
exceeded at arbitrarily late times by every actual flow. -/
theorem arbitrarily_late_above_subcritical (hflow : c.IsNormalFEF) {A : ℝ}
    (hA : 0<A) (hsmall : A^4 < 32*Real.pi^4) (S : ℝ) :
    ∃ t, S<t ∧ A*fourthRoot (1+t) < c.length t := by
  by_contra! hn
  let s := max 0 (S+1)
  have hs : 0≤s := le_max_left _ _
  have hSs : S<s := lt_of_lt_of_le (by linarith : S<S+1) (le_max_right _ _)
  let B := 32*Real.pi^4/A^3
  have hgap : 0<B-A := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ (pow_pos hA 3)).mpr
    nlinarith only [hsmall]
  obtain ⟨t,ht,hlarge⟩ := fourthRoot_eventually_above s (B*fourthRoot (1+s)/(B-A))
  have blow := (div_lt_iff₀ hgap).mp hlarge
  have hlow := c.length_lower_of_upper_envelope hflow hA hs ht.le
    (fun x hx => hn x (hSs.trans_le hx.1))
  change 2*Real.pi^2*(c.energy s)⁻¹+B*(fourthRoot (1+t)-fourthRoot (1+s)) ≤ c.length t at hlow
  have hi := hn t (hSs.trans ht)
  nlinarith only [blow,hlow,hi,show 0 ≤ 2*Real.pi^2*(c.energy s)⁻¹ by
    have := c.energy_pos hs; positivity]

/-- Quantified form of the unconditional lower bound
`limsup (L(t)^4 / t) ≥ 32π⁴`. No eventual upper bound is assumed here. -/
theorem sharp_length_fourth_limsup_lower (hflow : c.IsNormalFEF) {b : ℝ}
    (hb : 0 < b) (hsmall : b < 32*Real.pi^4) (S : ℝ) :
    ∃ t, max 0 S < t ∧ b < c.length t^4/t := by
  let A := fourthRoot b
  have hA : 0<A := fourthRoot_pos hb
  have hA4 : A^4=b := fourthRoot_pow_four hb.le
  obtain ⟨t,ht,high⟩ := c.arbitrarily_late_above_subcritical hflow hA (hA4 ▸ hsmall) (max 0 S)
  have hpos := (le_max_left 0 S).trans_lt ht
  have hq := fourthRoot_pos (show 0<1+t by linarith)
  have h4 := pow_lt_pow_left₀ high (mul_nonneg hA.le hq.le) (by decide : (4:ℕ)≠0)
  rw [mul_pow,hA4,fourthRoot_pow_four (show 0≤1+t by linarith)] at h4
  exact ⟨t,ht,(lt_div_iff₀ hpos).mpr (by linarith)⟩

end LengthGrowth.ActualFlow.ForwardImmersion
