import LengthGrowth.ActualFlow.FiniteSignTime
import LengthGrowth.ActualFlow.FiniteSignSlice

noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Here \(2EL\) and \(L^5D\) are precisely the bending integral and
dissipation on the unit-length spatial rescaling. -/
def normalizedNodalDeficit (E L D C : ℝ) : Prop :=
  (2*(E*L))*Real.sqrt (2*(E*L))/2 ≤ Real.sqrt (L^5*D) + C*(1+2*(E*L))

theorem deficit_of_unit_length_slice {t C : ℝ} (ht : 0≤t) (hC : 0≤C)
    (hs : normalizedNodalDeficit (c.energy t) (c.length t) (c.dissipation t) C) :
    NodalDeficit (c.energy t) (c.length t) (c.dissipation t) (3*C) := by
  let E:=c.energy t
  let L:=c.length t
  let D:=c.dissipation t
  let U:=E*L
  let z:=Real.sqrt (D*L^3/(2*E^2))
  have he:0<E:=c.energy_pos ht
  have hl:0<L:=c.length_pos ht
  have hd:0≤D:=c.dissipation_nonneg t
  have hu:0<U:=mul_pos he hl
  have hz:0≤z:=Real.sqrt_nonneg _
  have zz:z^2*(2*E^2)=D*L^3:= (eq_div_iff (by positivity : 2*E^2≠0)).mp
    (Real.sq_sqrt (by positivity : 0≤D*L^3/(2*E^2)))
  have ht2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have htwo:1≤Real.sqrt 2:=by nlinarith [Real.sqrt_nonneg 2]
  have eq1 : Real.sqrt (L^5*D)=Real.sqrt 2*U*z := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity),mul_pow,mul_pow,ht2]
    dsimp [U]
    have h:=congrArg (fun q : ℝ=>q*L^2) zz
    nlinarith only [h]
  have hu1 : 1≤U := by
    have h:=c.sharp_energy_length ht
    dsimp [U,E,L]; nlinarith [Real.pi_gt_three]
  change (2*U)*Real.sqrt (2*U)/2 ≤ Real.sqrt (L^5*D)+C*(1+2*U) at hs
  rw [eq1,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hs
  change Real.sqrt U≤z+3*C
  apply (mul_le_mul_iff_right₀ (by positivity : 0<Real.sqrt 2*U)).mp
  nlinarith only [hs,mul_nonneg hC (sub_nonneg.mpr hu1),
    mul_nonneg (mul_nonneg hC hu.le) (sub_nonneg.mpr htwo)]

theorem log_quarter_and_energy_decay_of_nodal_deficit (hf : c.IsNormalFEF) {T C : ℝ}
    (hT : 0≤T) (hC : 0≤C)
    (hs : ∀t>T, normalizedNodalDeficit (c.energy t) (c.length t) (c.dissipation t) C) :
    (∃ B : ℝ, 0<B ∧ ∀t≥T, c.length t≤B*fourthRoot (1+t)*(1+Real.log (1+t))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  have h3 : 0≤3*C := by positivity
  have hu (t:ℝ) (ht:T<t) := c.nodalSliceBound_of_deficit (hT.trans ht.le) h3
    (c.deficit_of_unit_length_slice (hT.trans ht.le) hC (hs t ht))
  exact ⟨c.nodal_log_quarter_length hf hT (mul_nonneg h3 (by linarith)) hu,
    c.nodal_energy_tendsto_zero hf hT (mul_nonneg h3 (by linarith)) hu⟩

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.log_quarter_and_energy_decay_of_nodal_deficit
