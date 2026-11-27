import LengthGrowth.ActualFlow.RecordSweptAreaLimit

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The swept-area integrand is the absolute determinant of the two actual
coordinate derivatives of the material homotopy. -/
theorem sweptAreaRate_eq_jacobian (hf : c.IsNormalFEF) {t:ℝ} (ht : 0<t) :
    c.sweptAreaRate t = ∫u in 0..c.period,
      |determinant (deriv (c.position t) u) (deriv (fun x=>c.position x u) t)| := by
  unfold sweptAreaRate
  apply intervalIntegral.integral_congr
  intro u _
  let γ:=c.position t
  have reg:=c.immersion t ht.le
  have derivX : deriv γ u=speed γ u • tangent γ u :=
    positionJet1_eq_speed_tangent (c.position_slice_smooth ht.le) reg u
  have derivT : deriv (fun x=>c.position x u) t=(-force γ u) • normal γ u := by
    simpa only [Complex.real_smul,Complex.ofReal_neg] using (hf t ht u).deriv
  have detTN : determinant (tangent γ u) (normal γ u)=1 := by
    rw [determinant_eq_inner]
    change inner ℝ (normal γ u) (normal γ u)=1
    rw [real_inner_self_eq_norm_sq,normal_unit reg]
    norm_num
  change |force γ u| * speed γ u=|determinant (deriv γ u) (deriv (fun x=>c.position x u) t)|
  rw [derivX,derivT,determinant_smul_left,determinant_smul_right,detTN,mul_one,abs_mul,
    abs_neg,abs_of_pos (speed_pos reg u),mul_comm]

theorem sweptArea_duration (hf : c.IsNormalFEF) {s t R : ℝ} (hs : 0≤s) (st:s≤t)
    (cap : ∀u∈Icc s t,c.length u≤R) :
    (∫u in s..t,c.sweptAreaRate u)^2≤R*(t-s)*(c.energy s-c.energy t) := by
  have sub : Icc s t⊆Ici 0 := fun _ hu => hs.trans hu.1
  have S:=c.sweptAreaRate_continuousOn.mono sub
  have D:=c.dissipation_continuousOn.mono sub
  have cs:=LengthGrowth.interval_integral_mul_sq_le_continuousOn
    (continuousOn_const (c:=(1:ℝ))) S st
  simp only [one_mul,one_pow,intervalIntegral.integral_const,smul_eq_mul,mul_one] at cs
  have bound:=intervalIntegral.integral_mono_on (μ:=volume) st
    ((S.pow 2).intervalIntegrable_of_Icc st) ((D.const_mul R).intervalIntegrable_of_Icc st)
    (fun u hu=>(c.sweptAreaRate_sq (sub hu)).trans
      (mul_le_mul_of_nonneg_right (cap u hu) (c.dissipation_nonneg _)))
  have loss:=c.energy_add_integral_dissipation hf hs st
  rw [intervalIntegral.integral_const_mul,
    show (∫u in s..t,c.dissipation u)=c.energy s-c.energy t by linarith only [loss]] at bound
  simp only [Pi.pow_apply] at bound
  nlinarith only [cs,mul_le_mul_of_nonneg_left bound (sub_nonneg.mpr st)]

/-- Macroscopic swept area requires a time interval of length at least
a constant times the terminal product in terminal RMS time units. -/
theorem sweptArea_record_rms_duration (hf:c.IsNormalFEF) {s t q d:ℝ}
    (hs:0≤s) (st:s≤t) (dd:0≤d)
    (rec : ∀u∈Icc s t,c.normalizedProduct u≤c.normalizedProduct t)
    (level : q*c.length s=c.length t)
    (sweep : d*c.length t^2≤∫u in s..t,c.sweptAreaRate u) :
    4*d^2*c.normalizedProduct t ≤ (q-1)*((2*c.energy t/c.length t)^2*(t-s)) := by
  have tn:=hs.trans st
  have Lp:=c.length_pos tn
  have Ep:=c.energy_pos tn
  have cap (u:ℝ) (hu:u∈Icc s t) : c.length u≤c.length t := by
    have e:=c.energy_le_of_le hf (hs.trans hu.1) hu.2
    apply le_of_mul_le_mul_left (a:=c.energy t) _ Ep
    exact (mul_le_mul_of_nonneg_right e (c.length_nonneg _)).trans (rec u hu)
  have en : c.energy s≤q*c.energy t := by
    have r:=rec s ⟨le_rfl,st⟩
    change c.energy s*c.length s≤c.energy t*c.length t at r
    rw [←level] at r
    apply le_of_mul_le_mul_right (a:=c.length s) _ (c.length_pos hs)
    linarith only [r]
  have sq:=pow_le_pow_left₀ (mul_nonneg dd (sq_nonneg _)) sweep 2
  have time:=c.sweptArea_duration hf hs st cap
  have loss : c.energy s-c.energy t≤(q-1)*c.energy t := by linarith only [en]
  have bound:=sq.trans (time.trans (mul_le_mul_of_nonneg_left loss
    (mul_nonneg Lp.le (sub_nonneg.mpr st))))
  have shorter : d^2*c.length t^3≤(t-s)*(q-1)*c.energy t := by
    apply le_of_mul_le_mul_right (a:=c.length t) _ Lp
    nlinarith only [bound]
  unfold normalizedProduct
  rw [div_pow]
  field_simp [Lp.ne']
  nlinarith only [shorter]

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.sweptArea_record_rms_duration
