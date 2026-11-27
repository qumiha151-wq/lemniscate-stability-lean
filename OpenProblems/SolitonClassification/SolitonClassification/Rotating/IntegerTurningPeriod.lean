import SolitonClassification.Rotating.IntegerTwoArmImmersion
import SolitonClassification.Rotating.RotatingNormalEvolutionScalar

namespace SolitonClassification.Rotating.IntegerTarget
open Set

/-- For any shift of a real continuous periodic function the two graphs have
a common point. This holds even when the shift is irrational in period units. -/
private theorem equal_at_shift {g : ℝ → ℝ} {L : ℝ} (hL : 0<L)
    (cont : Continuous g) (per : Function.Periodic g L) (h : ℝ) :
    ∃s : ℝ, g (s+h)=g s := by
  have cover : g '' Icc 0 L = range g := by simpa using per.image_Icc hL 0
  have nonempty : (Icc (0:ℝ) L).Nonempty := ⟨0,left_mem_Icc.mpr hL.le⟩
  obtain ⟨lo,hlo,small⟩ := isCompact_Icc.exists_isMinOn nonempty cont.continuousOn
  obtain ⟨hi,hhi,large⟩ := isCompact_Icc.exists_isMaxOn nonempty cont.continuousOn
  have bounds (t : ℝ) : g lo≤g t ∧ g t≤g hi := by
    have hit : g t∈g '' Icc 0 L := cover.symm ▸ mem_range_self t
    obtain ⟨u,hu,e⟩ := hit
    rw [←e]
    exact ⟨small hu,large hu⟩
  let d := fun s : ℝ => g (s+h)-g s
  have cd : Continuous d := (cont.comp (continuous_id.add continuous_const)).sub cont
  obtain ⟨s,hs⟩ := intermediate_value_univ hi lo cd
    (show 0∈Icc (d hi) (d lo) from ⟨sub_nonpos.mpr (bounds (hi+h)).2,
                                      sub_nonneg.mpr (bounds (lo+h)).1⟩)
  exact ⟨s,sub_eq_zero.mp hs⟩

/-- A closed regular immersion with an actual signed turning of minus one
has precisely the integer multiples of its stated length as position periods. -/
theorem WindingOneImmersion.period_lattice {b L : ℝ} (I : WindingOneImmersion b L)
    (hL : 0<L) (h : ℝ) :
    Function.Periodic I.x h ∧ Function.Periodic I.y h ↔ ∃m : ℤ, h=(m:ℝ)*L := by
  constructor
  · rintro ⟨px,py⟩
    let g := fun s : ℝ => I.theta s+(2*Real.pi/L)*s
    have ct : Continuous I.theta := continuous_iff_continuousAt.mpr fun s =>
      (I.angleDerivative s).continuousAt
    have cg : Continuous g := by dsimp only [g]; fun_prop
    have pg : Function.Periodic g L := by
      intro s
      dsimp only [g]
      rw [I.turning s]
      field_simp [hL.ne']
      ring
    obtain ⟨s,hs⟩ := equal_at_shift hL cg pg h
    have tx := NormalEvolution.periodic_deriv px s
    have ty := NormalEvolution.periodic_deriv py s
    rw [(I.tangentX (s+h)).deriv,(I.tangentX s).deriv] at tx
    rw [(I.tangentY (s+h)).deriv,(I.tangentY s).deriv] at ty
    have angle : Real.cos (I.theta (s+h)-I.theta s)=1 := by
      rw [Real.cos_sub,tx,ty]
      nlinarith only [Real.sin_sq_add_cos_sq (I.theta s)]
    obtain ⟨m,hm⟩ := (Real.cos_eq_one_iff _).mp angle
    refine ⟨-m,?_⟩
    dsimp only [g] at hs
    field_simp [hL.ne'] at hs
    rw [Int.cast_neg]
    apply (mul_left_cancel₀ (show (2*Real.pi:ℝ)≠0 by positivity))
    linear_combination hs + L*hm
  · rintro ⟨m,rfl⟩
    exact ⟨by simpa only [zsmul_eq_mul] using I.periodX.zsmul m,
      by simpa only [zsmul_eq_mul] using I.periodY.zsmul m⟩

theorem WindingOneImmersion.least_positive_period {b L : ℝ} (I : WindingOneImmersion b L)
    (hL : 0<L) : IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} L := by
  refine ⟨⟨hL,I.periodX,I.periodY⟩,?_⟩
  rintro h ⟨hh,px,py⟩
  obtain ⟨m,em⟩ := (I.period_lattice hL h).mp ⟨px,py⟩
  rw [em] at hh ⊢
  have hm : (0:ℝ)<m := pos_of_mul_pos_left hh hL.le
  have hp : (0:ℤ)<m := by exact_mod_cast hm
  have one : (1:ℝ)≤m := by exact_mod_cast (show (1:ℤ)≤m by omega)
  simpa using mul_le_mul_of_nonneg_right one hL.le

end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.WindingOneImmersion.period_lattice
#print axioms SolitonClassification.Rotating.IntegerTarget.WindingOneImmersion.least_positive_period
