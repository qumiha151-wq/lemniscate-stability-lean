import LengthGrowth.ActualFlow.SharpVirial
import LengthGrowth.ActualFlow.CriticalDensityTime

/-! The full unsigned normal area swept in the material plane and the logarithmic
energy cost of every segment terminating at an energy-length record. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The instantaneous integral of absolute normal velocity against actual arclength. -/
def sweptAreaRate (t : ℝ) : ℝ :=
  ∫u in 0..c.period, |force (c.position t) u| *speed (c.position t) u

theorem sweptAreaRate_continuousOn : ContinuousOn c.sweptAreaRate (Ici 0) :=
  continuousOn_intervalIntegral_forward ((c.force_continuousOn.abs.mul c.speed_continuousOn).mono
    (fun _ h => ⟨h.1, mem_univ _⟩))

theorem sweptAreaRate_nonneg (t : ℝ) : 0≤c.sweptAreaRate t :=
  intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun _u => mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem sweptAreaRate_sq {t : ℝ} (h : 0≤t) :
    c.sweptAreaRate t^2≤c.length t*c.dissipation t := by
  let γ:=c.position t
  let w:=fun u=>Real.sqrt (speed γ u)
  have hw : Continuous w := (speed_smooth (c.position_slice_smooth h) (c.immersion t h)).continuous.sqrt
  have hf : Continuous (fun u=>|force γ u|) :=
    (force_smooth (c.position_slice_smooth h) (c.immersion t h)).continuous.abs
  have cs:=LengthGrowth.interval_integral_mul_sq_le hw (hf.mul hw) c.period_pos.le
  have sq (u:ℝ) : w u^2=speed γ u := Real.sq_sqrt (speed_pos (c.immersion t h) u).le
  have prod (u:ℝ) : w u*(|force γ u| *w u)=|force γ u| *speed γ u := by
    rw [←sq]; ring
  simp only [Pi.mul_apply,prod,mul_pow,sq_abs,sq] at cs
  exact cs

/-- Relative bending-energy dissipation pays for the unsigned swept area in
units of the current squared length. The coefficient is attained by a circle. -/
theorem sweptAreaRate_virial {t : ℝ} (h : 0≤t) :
    2*Real.pi*c.sweptAreaRate t ≤ c.length t^2*(c.dissipation t/c.energy t) := by
  let L:=c.length t
  let E:=c.energy t
  let D:=c.dissipation t
  let S:=c.sweptAreaRate t
  have Lp : 0<L := c.length_pos h
  have Ep : 0<E := c.energy_pos h
  have Dn : 0≤D := c.dissipation_nonneg _
  have ss : S^2≤L*D := c.sweptAreaRate_sq h
  have vv : 4*Real.pi^2*E^2≤D*L^3 := c.sharp_virial h
  have product:=mul_le_mul ss vv (by positivity) (mul_nonneg Lp.le Dn)
  have bound : 2*Real.pi*S*E≤L^2*D := by
    apply le_of_sq_le_sq _ (mul_nonneg (sq_nonneg L) Dn)
    nlinarith only [product]
  change 2*Real.pi*S≤L^2*(D/E)
  rw [←mul_div_assoc,le_div_iff₀ Ep]
  exact bound

theorem sweptArea_of_length_cap (hf : c.IsNormalFEF) {s t R : ℝ} (hs : 0≤s) (st : s≤t)
    (cap : ∀u∈Icc s t, c.length u≤R) :
    2*Real.pi*(∫u in s..t,c.sweptAreaRate u) ≤
    R^2*(Real.log (c.energy s)-Real.log (c.energy t)) := by
  have sub : Icc s t⊆Ici 0 := fun _ hu => hs.trans hu.1
  have epos (u:ℝ) (hu:u∈Icc s t) := c.energy_pos (sub hu)
  have ratio : ContinuousOn (fun u=>c.dissipation u/c.energy u) (Icc s t) :=
    (c.dissipation_continuousOn.mono sub).div (c.energy_continuousOn.mono sub) (fun u hu=>(epos u hu).ne')
  have der (u:ℝ) (hu:u∈Ioo s t) : HasDerivAt (fun x=>Real.log (c.energy x))
      (-c.dissipation u/c.energy u) u :=
    (c.energy_hasDerivAt_normal hf (hs.trans_lt hu.1)).log (c.energy_pos (hs.trans hu.1.le)).ne'
  have negRatio : ContinuousOn (fun u=> -c.dissipation u/c.energy u) (Icc s t) := by
    intro u hu
    exact ((c.dissipation_continuousOn u (sub hu)).neg.div (c.energy_continuousOn u (sub hu))
      (epos u hu).ne').mono sub
  have logInt:=intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le st
    ((c.energy_continuousOn.mono sub).log (fun u hu=>(epos u hu).ne'))
    der (negRatio.intervalIntegrable_of_Icc st)
  simp only [neg_div,intervalIntegral.integral_neg] at logInt
  have evalInt : (∫u in s..t,c.dissipation u/c.energy u)=Real.log (c.energy s)-Real.log (c.energy t) := by
    linarith only [logInt]
  have point (u:ℝ) (hu:u∈Icc s t) :
      2*Real.pi*c.sweptAreaRate u≤R^2*(c.dissipation u/c.energy u) :=
    (c.sweptAreaRate_virial (sub hu)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (c.length_nonneg u) (cap u hu) 2)
        (div_nonneg (c.dissipation_nonneg _) (epos u hu).le))
  have mon:=intervalIntegral.integral_mono_on (μ:=volume) st
    (((c.sweptAreaRate_continuousOn.mono sub).const_mul (2*Real.pi)).intervalIntegrable_of_Icc st)
    ((ratio.const_mul (R^2)).intervalIntegrable_of_Icc st) point
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,evalInt] at mon
  exact mon

theorem sweptArea_at_product_record (hf : c.IsNormalFEF) {s t : ℝ} (hs : 0≤s) (st : s≤t)
    (record : ∀u∈Icc s t,c.normalizedProduct u≤c.normalizedProduct t) :
    2*Real.pi*(∫u in s..t,c.sweptAreaRate u) ≤
      c.length t^2*(Real.log (c.energy s)-Real.log (c.energy t)) := by
  apply c.sweptArea_of_length_cap hf hs st
  intro u hu
  have up:=hs.trans hu.1
  have ep:=c.energy_pos (hs.trans st)
  have e:=c.energy_le_of_le hf up hu.2
  have lower:=mul_le_mul_of_nonneg_right e (c.length_nonneg u)
  apply le_of_mul_le_mul_left (a:=c.energy t) _ ep
  exact lower.trans (record u hu)

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.sweptArea_at_product_record
