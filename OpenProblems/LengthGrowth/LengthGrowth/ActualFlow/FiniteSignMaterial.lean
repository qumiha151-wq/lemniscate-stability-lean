import LengthGrowth.ActualFlow.FiniteSignFlow
import LengthGrowth.ActualFlow.FiniteSignPartition
import LengthGrowth.ActualFlow.CriticalRMSAdapter

noncomputable section
open Set Function MeasureTheory Filter FreeElasticScalar
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- Every subarc of length at most one splits into at most N+1 weakly
one-sign pieces; this convention also covers change-of-basepoint windows. -/
def BoundedNodalCount (k : ℝ→ℝ) (N : ℕ) : Prop :=
  ∀a b:ℝ,a≤b → b≤a+1 → ∃ n≤N+1, LengthGrowth.FiniteSign.Pieces k n a b

/-- The remaining scalar, static assertion. The quantities are computed from
the arbitrary smooth unit-period profile and its ordinary derivatives. -/
def FiniteSignScalarEstimate (N : ℕ) (C : ℝ) : Prop :=
  ∀k : ℝ→ℝ, ContDiff ℝ ∞ k → Periodic k 1 → BoundedNodalCount k N →
    let B := ∫s in (0:ℝ)..1,k s^2
    let d := ∫s in (0:ℝ)..1,(deriv (deriv k) s+k s^3/2)^2
    B*Real.sqrt B/2 ≤ Real.sqrt d+C*(1+ B)

theorem PeriodicRegularPosition.nodalDeficit_of_scalar (c : PeriodicRegularPosition)
    {C : ℝ} {N : ℕ} (hs : FiniteSignScalarEstimate N C)
    (hn : BoundedNodalCount (c.scaledArclengthCurvature c.length) N) :
    ForwardImmersion.normalizedNodalDeficit (materialEnergy c.position c.period) c.length
      (materialDissipation c.position c.period) C := by
  let L:=c.length
  let k:=c.scaledArclengthCurvature L
  have hL : 0<L:=c.length_pos
  have M:=c.scaledArclengthCurvature_moment (a:=L) (P:=1) hL (by norm_num) (by simp [L])
  have hB:=M 2 0
  have hd:=M 0 2
  simp only [pow_zero,one_mul,mul_one,div_one] at hB hd
  have e : (∫s in 0..c.period,curvature c.position s^2*speed c.position s) = 2*materialEnergy c.position c.period := by
    unfold materialEnergy; ring
  have hB' : (∫s in (0:ℝ)..1,k s^2)=2*(materialEnergy c.position c.period*L) := by
    rw [hB,e]; change L^2/L*(2*_) = _; field_simp
  have hd' : (∫s in (0:ℝ)..1,(deriv (deriv k) s+k s^3/2)^2) = L^5*materialDissipation c.position c.period := by
    simp only [div_eq_inv_mul] at *
    change (∫s in (0:ℝ)..1,(deriv (deriv k) s+2⁻¹*k s^3)^2) = _
    calc
      _ = (L^3)^2/L*materialDissipation c.position c.period := by simpa [k,L,materialDissipation,div_eq_inv_mul] using hd
      _ = _ := by field_simp
  have h:=hs k (c.scaledArclengthCurvature_smooth L) (c.scaledArclengthCurvature_periodic (by simp [L])) hn
  dsimp only at h
  rwa [hB',hd'] at h

theorem ForwardImmersion.log_quarter_and_decay_of_scalar_finite_sign (c : ForwardImmersion)
    (hf : c.IsNormalFEF) {N : ℕ} {T C : ℝ} (hT : 0≤T) (hC : 0≤C)
    (static : FiniteSignScalarEstimate N C)
    (nodes : ∀t, (ht:T<t) → let p:=c.regularPositionAt (hT.trans ht.le)
      BoundedNodalCount (p.scaledArclengthCurvature p.length) N) :
    (∃ B : ℝ, 0<B ∧ ∀t≥T, c.length t ≤ B*fourthRoot (1+t)*(1+Real.log (1+t))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  apply c.log_quarter_and_energy_decay_of_nodal_deficit hf hT hC
  intro t ht
  exact (c.regularPositionAt (hT.trans ht.le)).nodalDeficit_of_scalar static (nodes t ht)

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.log_quarter_and_decay_of_scalar_finite_sign
