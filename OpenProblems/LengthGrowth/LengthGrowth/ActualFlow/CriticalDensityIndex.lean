import LengthGrowth.ActualFlow.CriticalDensityMaterial
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open Set Function
open scoped ContDiff
namespace LengthGrowth.ActualFlow
namespace CriticalDensity

/-- Unlike the number of all inflection points, the number of pieces
separating the two half-RMS levels is finite for every smooth slice. -/
theorem exists_count {k : ℝ→ℝ} {P : ℝ} (hP : 0<P) (hk : ContDiff ℝ ∞ k)
    (hp : Periodic k P) : ∃ N : ℕ, Count k P N := by
  let v:=deriv k
  have ck : Continuous v := (contDiff_infty_iff_deriv.mp hk).2.continuous
  have pv : Periodic v P := actual_deriv_periodic hp (hk.differentiable (by simp))
  obtain ⟨z,_,mx⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hP.le)
    ck.abs.continuousOn
  let B:=|v z|
  have B0 : 0≤B:=abs_nonneg _
  have bv (t : ℝ) : |v t|≤B := by
    obtain ⟨r,hr,he⟩:=pv.exists_mem_Ico₀ hP t
    have tmax:=mx (show r∈Icc 0 P from ⟨hr.1,hr.2.le⟩)
    change |v r|≤B at tmax
    rwa [he]
  obtain ⟨N,hN⟩ := exists_nat_gt (2*B*P)
  refine ⟨N, ?_⟩
  intro a b hab hlen
  let δ:=(b-a)/((N:ℝ)+1)
  have denom : 0<(N:ℝ)+1 := by positivity
  have d0 : 0≤δ := div_nonneg (sub_nonneg.mpr hab) denom.le
  have small : B*δ≤1/2 := by
    change B*((b-a)/((N:ℝ)+1))≤1/2
    rw [←mul_div_assoc]
    apply (div_le_iff₀ denom).mpr
    linarith [mul_le_mul_of_nonneg_left (show b-a≤P by linarith) B0]
  have pieces : ∀ j : ℕ, Pieces k (1/2) j a (a+(j:ℝ)*δ) := by
    intro j
    induction j with
    | zero => simpa using (Pieces.empty (k:=k) (δ:=1/2) a)
    | succ j ih =>
      let l:=a+(j:ℝ)*δ
      let r:=a+((j+1:ℕ):ℝ)*δ
      have sub : r-l=δ := by dsimp [l,r];push_cast;ring
      have lr : l≤r := by linarith
      apply Pieces.append ih lr
      have osc (x:ℝ) (hx:x∈Icc l r) : |k x-k l|≤1/2 := by
        have bem (t : ℝ) (_ht : t∈Ico l r) : ‖v t‖≤B := by simpa only [Real.norm_eq_abs] using bv t
        have der (t : ℝ) (_ht : t∈Icc l r) : HasDerivWithinAt k (v t) (Icc l r) t :=
          ((hk.differentiable (by simp)) t).hasDerivAt.hasDerivWithinAt
        have h:=norm_image_sub_le_of_norm_deriv_le_segment' der bem x hx
        rw [Real.norm_eq_abs] at h
        exact h.trans ((mul_le_mul_of_nonneg_left (by linarith [hx.2] : x-l≤δ) B0).trans small)
      by_cases h : 0≤k l
      · exact Or.inl (fun x hx => by linarith [(abs_le.mp (osc x hx)).1])
      · exact Or.inr (fun x hx => by linarith [(abs_le.mp (osc x hx)).2,lt_of_not_ge h])
  have join : a+((N+1:ℕ):ℝ)*δ=b := by
    dsimp [δ]
    push_cast
    field_simp [denom.ne']
    ring
  exact ⟨N+1,le_rfl,join ▸ pieces (N+1)⟩

end CriticalDensity
namespace PeriodicRegularPosition

theorem exists_criticalDensityCount (p : PeriodicRegularPosition) : ∃ N : ℕ, p.CriticalDensityCount N := by
  let P:=Real.sqrt (2*(materialEnergy p.position p.period*p.length))
  have hP : 0<P:=Real.sqrt_pos.mpr (by positivity [p.material_energy_pos,p.length_pos])
  exact CriticalDensity.exists_count hP (p.scaledArclengthCurvature_smooth (p.length/P))
    (p.scaledArclengthCurvature_periodic (div_mul_cancel₀ _ hP.ne'))

/-- Least N for which every subarc of one normalized period fits in N+1
pieces admitting the half-RMS orientation. -/
def criticalDensityIndex (p : PeriodicRegularPosition) : ℕ := by
  classical
  exact Nat.find p.exists_criticalDensityCount

theorem criticalDensityIndex_spec (p : PeriodicRegularPosition) :
    p.CriticalDensityCount p.criticalDensityIndex := by
  classical
  exact Nat.find_spec p.exists_criticalDensityCount

theorem criticalDensityIndex_le (p : PeriodicRegularPosition) {N : ℕ}
    (hn : p.CriticalDensityCount N) : p.criticalDensityIndex≤N := by
  classical
  exact Nat.find_min' p.exists_criticalDensityCount hn

end PeriodicRegularPosition
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.criticalDensityIndex_spec
