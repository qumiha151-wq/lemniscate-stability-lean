import LengthGrowth.ActualFlow.SharpVirial
import LengthGrowth.ActualFlow.RelativeEnergy
import LengthGrowth.ActualFlow.MacroscopicTurningRecords
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

variable (c : ForwardImmersion)

/-- Square integral of the second arclength derivative of the actual force. -/
def forceSecondMass (t : ℝ) : ℝ :=
  ∫ u in 0..c.period, (arcDerivative (c.position t)
    (arcDerivative (c.position t) (force (c.position t))) u)^2 * speed (c.position t) u

theorem forceSecondMass_continuousOn : ContinuousOn c.forceSecondMass (Ioi 0) := by
  let p := c.interior
  have h₁ := p.arcDerivative_joint_smooth (f := fun t => force (p.position t)) p.force_joint_smooth
  have h₂ := p.arcDerivative_joint_smooth
    (f := fun t => arcDerivative (p.position t) (force (p.position t))) h₁
  exact continuousOn_intervalIntegral_of_isOpen isOpen_Ioi
    (((h₂.pow 2).mul p.speed_joint_smooth).continuousOn.mono (fun _ h => ⟨h.1,mem_univ _⟩))

theorem dissipation_differentiable_positive {t : ℝ} (ht : 0<t) :
    DifferentiableAt ℝ c.dissipation t := by
  let p := c.interior
  exact (hasDerivAt_intervalIntegral_of_jointC1 (a := 0) (b := c.period) isOpen_Ioi
    (F := fun x u => force (p.position x) u ^ 2 * speed (p.position x) u)
    (((p.force_joint_smooth.pow 2).mul p.speed_joint_smooth).of_le (by simp)) ht).differentiableAt

theorem force_dissipation_pos {t : ℝ} (ht : 0≤t) : 0 < c.dissipation t := by
  have hp : 0 < 4*Real.pi^2*(c.energy t)^2 := by have := c.energy_pos ht; positivity
  exact pos_of_mul_pos_left (hp.trans_le (c.sharp_virial ht)) (pow_nonneg (c.length_nonneg _) _)

/-- Integrating the force rate yields a bound on actual weighted spatial
derivatives on any positive time interval. The force rate is the explicit
geometric estimate supplied by the mathematical proof. -/
theorem force_weighted_budget (hf : c.IsNormalFEF) {s t C : ℝ} (hs : 0<s) (hst : s≤t)
    (rate : ∀ x ∈ Ioo s t, deriv c.dissipation x + c.forceSecondMass x ≤
      C * c.dissipation x ^ (5/3:ℝ)) :
    (∫ x in s..t, c.dissipation x ^ (-(2/3):ℝ) * c.forceSecondMass x) ≤
      3*(c.dissipation s ^ (1/3:ℝ)-c.dissipation t ^ (1/3:ℝ))+
      C*(c.energy s-c.energy t) := by
  let W := fun x : ℝ => -(3*c.dissipation x ^ (1/3:ℝ)+C*c.energy x)
  let w := fun x : ℝ => c.dissipation x ^ (-(2/3):ℝ)
  have sub : Icc s t ⊆ Ici (0:ℝ) := fun _ hx => hs.le.trans hx.1
  have sub' : Icc s t ⊆ Ioi (0:ℝ) := fun _ hx => hs.trans_le hx.1
  have hc := c.dissipation_continuousOn.mono sub
  have hd (x : ℝ) (hx : x∈Icc s t) := c.force_dissipation_pos (sub hx)
  have cw : ContinuousOn W (Icc s t) :=
    ((continuousOn_const.mul (hc.rpow_const (fun x hx => Or.inl (hd x hx).ne'))).add
      (continuousOn_const.mul (c.energy_continuousOn.mono sub))).neg
  have hw : ContinuousOn w (Icc s t) :=
    hc.rpow_const (fun x hx => Or.inl (hd x hx).ne')
  have dw (x : ℝ) (hx : x∈Ioo s t) : HasDerivAt W
      (C*c.dissipation x-w x*deriv c.dissipation x) x := by
    have htime := hs.trans hx.1
    have dp := c.force_dissipation_pos htime.le
    have dr := (c.dissipation_differentiable_positive htime).hasDerivAt.rpow_const
      (p := (1/3:ℝ)) (Or.inl dp.ne')
    have dz := ((dr.const_mul 3).add ((c.energy_hasDerivAt_normal hf htime).const_mul C)).neg
    convert! dz using 1
    change C*c.dissipation x-c.dissipation x ^ (-(2/3):ℝ)*deriv c.dissipation x = _
    norm_num
    ring
  have mult (x : ℝ) (hx : x∈Ioo s t) :
      w x*c.forceSecondMass x ≤ C*c.dissipation x-w x*deriv c.dissipation x := by
    have dp := c.force_dissipation_pos (hs.trans hx.1).le
    have wp : 0 ≤ w x := Real.rpow_nonneg dp.le _
    have eq : w x * c.dissipation x ^ (5/3:ℝ) = c.dissipation x := by
      rw [show w x=c.dissipation x ^ (-(2/3):ℝ) from rfl, ← Real.rpow_add dp]
      norm_num
    calc
      _ ≤ w x * (C*c.dissipation x ^ (5/3:ℝ)) - w x*deriv c.dissipation x := by
        linarith only [mul_le_mul_of_nonneg_left (rate x hx) wp]
      _ = _ := by rw [mul_left_comm,eq]
  have hi := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hst cw
    (fun x hx => (dw x hx).hasDerivWithinAt)
    ((hw.mul (c.forceSecondMass_continuousOn.mono sub')).integrableOn_Icc) mult
  dsimp [W,w] at hi
  linarith only [hi]

/-- A local upper force-rate up to the first threshold crossing provides a
physical future window. The estimate uses the actual smooth dissipation. -/
theorem force_forward_window {s t b A : ℝ} (hs : 0<s)
    (hA : 0≤A) (initial : c.dissipation s < b)
    (budget : A*(t-s) < b-c.dissipation s)
    (rate : ∀ x∈Ioo s t, c.dissipation x < b → deriv c.dissipation x ≤ A) :
    ∀ u ∈ Icc s t, c.dissipation u < b := by
  intro u hu
  by_contra! high
  let f := fun x : ℝ => c.dissipation (max x 0)
  have cf : Continuous f := c.dissipation_continuousOn.comp_continuous
    (continuous_id.max continuous_const) (fun x => le_max_right x 0)
  let K := Icc s u ∩ f ⁻¹' Ici b
  have hk : IsCompact K := isCompact_Icc.inter_right (isClosed_Ici.preimage cf)
  have huK : u∈K := ⟨⟨hu.1,le_rfl⟩,by simpa [f,max_eq_left (hs.le.trans hu.1)] using high⟩
  obtain ⟨v,hv,hm⟩ := hk.exists_isMinOn ⟨u,huK⟩ continuousOn_id
  have H : b ≤ c.dissipation v := by
    simpa [f,max_eq_left (hs.le.trans hv.1.1)] using hv.2
  have sv : s < v := lt_of_le_of_ne hv.1.1 (by rintro rfl; exact initial.not_ge H)
  obtain ⟨z,hz,he⟩ := exists_deriv_eq_slope c.dissipation sv
    (c.dissipation_continuousOn.mono (fun _ hx => hs.le.trans hx.1))
    (fun _ hx => (c.dissipation_differentiable_positive (hs.trans hx.1)).differentiableWithinAt)
  have below : c.dissipation z < b := by
    by_contra! bad
    have hzK : z∈K := ⟨⟨hz.1.le,hz.2.le.trans hv.1.2⟩, by
      simpa [f,max_eq_left (hs.trans hz.1).le] using bad⟩
    exact (not_lt_of_ge (hm hzK)) hz.2
  have g := rate z ⟨hz.1,hz.2.trans_le (hv.1.2.trans hu.2)⟩ below
  rw [he,div_le_iff₀ (sub_pos.mpr sv)] at g
  linarith only [g,H,budget,mul_le_mul_of_nonneg_left
    (sub_le_sub_right (hv.1.2.trans hu.2) s) hA]

/-- At an actual product record with initial energy scaled to one, the
small-dissipation rate gives a forward physical interval of controlled
force and energy drop. Its width is a constant times L(s)^(4/3). -/
theorem record_force_forward_persistence (hf : c.IsNormalFEF) {s t C : ℝ}
    (hs : 0<s) (hst : s≤t) (record : ∀u∈Icc 0 s,c.normalizedProduct u≤c.normalizedProduct s)
    (scale : c.energy s=1) (big : 2≤c.length s) (hC : 0≤C)
    (rate : ∀u∈Ioo s t, c.dissipation u≤1 →
      deriv c.dissipation u ≤ C*c.dissipation u^(5/3:ℝ))
    (window : C*(4/c.length s^2)^(5/3:ℝ)*(t-s)<2/c.length s^2) :
    (∀u∈Icc s t,c.dissipation u<4/c.length s^2) ∧
      1-(4/c.length s^2)*(t-s)≤c.energy t := by
  have lp := c.length_pos hs.le
  have sqp := sq_pos_of_pos lp
  have recordBound := c.dissipation_at_product_record hf hs record
  rw [scale] at recordBound
  have initial : c.dissipation s≤2/c.length s^2 := (le_div_iff₀ sqp).2 (by linarith only [recordBound])
  have twice : 2/c.length s^2<4/c.length s^2 := by
    gcongr
    norm_num
  have small : 4/c.length s^2≤1 := (div_le_iff₀ sqp).2 (by nlinarith only [big,sq_nonneg (c.length s-2)])
  have split : 4/c.length s^2=2/c.length s^2+2/c.length s^2 := by ring
  have bd := c.force_forward_window (t:=t) hs (b:=4/c.length s^2) (A:=C*(4/c.length s^2)^(5/3:ℝ))
    (by positivity) (initial.trans_lt twice) (window.trans_le (by
      apply le_sub_iff_add_le.mpr
      rw [split]
      exact add_le_add le_rfl initial)) (by
      intro u hu hdu
      exact (rate u hu (hdu.le.trans small)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (c.dissipation_nonneg u) hdu.le (by norm_num)) hC))
  refine ⟨bd,?_⟩
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hst
    ((c.dissipation_continuousOn.mono (show Icc s t⊆Ici 0 from
      fun _ hx => hs.le.trans hx.1)).intervalIntegrable_of_Icc hst)
    (intervalIntegrable_const (c:=4/c.length s^2)) (fun u hu => (bd u hu).le)
  have he := c.energy_add_integral_dissipation hf hs.le hst
  rw [intervalIntegral.integral_const,smul_eq_mul] at hi
  rw [scale] at he
  linarith only [hi,he]

#print axioms force_weighted_budget
#print axioms force_forward_window
#print axioms record_force_forward_persistence
end LengthGrowth.ActualFlow.ForwardImmersion
