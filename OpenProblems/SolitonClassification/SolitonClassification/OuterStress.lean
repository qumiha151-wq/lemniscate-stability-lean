import SolitonClassification.FrozenStress
import Mathlib.Topology.Instances.Real.Lemmas

/-! Exact corrected derivatives in the moving physical outer problem.
    The transverse and radial components a,b are those of Z, with arbitrary
    length. The fast clock is r/δ and A=r² is the stress amplitude. -/
noncomputable section
set_option maxHeartbeats 2400000
namespace ClosedSimilarity.OuterStress
open FrozenStress (psi remJ)

structure Rates (δ s : ℝ) (r U w a b : ℝ → ℝ) where
  delta_pos : 0 < δ
  pos : 0 < r s
  oscillator : (U s^2/2)^2+w s^2=1
  dr : HasDerivAt r (-(w s*a s+U s^2/2*b s)*w s/(2*r s)) s
  dU : HasDerivAt U (w s*(r s/δ+U s*(w s*a s+U s^2/2*b s)/(2*r s^2))) s
  dw : HasDerivAt w (-U s^3/2*(r s/δ+U s*(w s*a s+U s^2/2*b s)/(2*r s^2))) s
  da : HasDerivAt a (U s^2/2-(w s*a s+U s^2/2*b s)*(U s^2/2)*b s/r s^2) s
  db : HasDerivAt b (-w s+(w s*a s+U s^2/2*b s)*(U s^2/2)*a s/r s^2) s

def Q (U w a b : ℝ) := -U*w*a/3-U^3*b/6
def impact (δ : ℝ) (r U w a b : ℝ → ℝ) (s : ℝ) :=
  r s*b s - δ*(psi (U s) (w s) (a s) (b s)/r s^2-U s)
def amplitude (δ : ℝ) (r U w a b : ℝ → ℝ) (s : ℝ) :=
  r s^2 - δ*(Q (U s) (w s) (a s) (b s)/r s)

def impactRemainder (A U w a b : ℝ) :=
  let p := w*a+U^2/2*b
  let ψa := U^3*a/3-U*w*b/2
  let ψb := -U^3*b/6-U*w*a/2
  remJ U w a b p + A*(w*U*p/2-U^2/2*ψa+w*ψb)

def amplitudeRemainder (A U w a b : ℝ) :=
  let u := U^2/2
  let p := w*a+u*b
  let Qa := -U*w/3
  let Qb := -U^3/6
  let Qφ := -(w^2-U^4/2)*a/3-U^2*w*b/2
  0 - (U*p*Qφ/2) + p*u*(b*Qa-a*Qb) - p*w*Q U w a b/2 - A*(u*Qa-w*Qb)

variable {δ s : ℝ} {r U w a b : ℝ → ℝ} (d : Rates δ s r U w a b)
include d

theorem impact_rate : HasDerivAt (impact δ r U w a b)
    (δ*impactRemainder (r s^2) (U s) (w s) (a s) (b s)/r s^4) s := by
  have ps := (((d.dU.pow 3).mul ((d.da.pow 2).sub ((d.db.pow 2).div_const 2))).div_const 6).sub
    ((((d.dU.mul d.dw).mul d.da).mul d.db).div_const 2)
  convert! (d.dr.mul d.db).sub (((ps.div (d.dr.pow 2) (pow_ne_zero _ d.pos.ne')).sub d.dU).const_mul δ) using 1
  dsimp [impactRemainder,remJ]
  try simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply]
  field_simp [d.pos.ne',d.delta_pos.ne']
  ring

theorem amplitude_rate : HasDerivAt (amplitude δ r U w a b)
    (-(2*a s/3)+δ*amplitudeRemainder (r s^2) (U s) (w s) (a s) (b s)/r s^3) s := by
  have hq := ((((d.dU.neg.mul d.dw).mul d.da).div_const 3)).sub (((d.dU.pow 3).mul d.db).div_const 6)
  convert! (d.dr.pow 2).sub ((hq.div d.dr d.pos.ne').const_mul δ) using 1
  have phase : -(2*a s/3) = -(w s*a s+U s^2/2*b s)*w s +
      ((w s^2-U s^4/2)*a s/3 + U s^2*w s*b s/2) := by
    linear_combination (2*a s/3)*d.oscillator
  rw [phase]
  dsimp [amplitudeRemainder,Q]
  try simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,Pi.neg_apply]
  field_simp [d.pos.ne',d.delta_pos.ne']
  ring

omit d in
private theorem uniform_remainders (M : ℝ) (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∀ x : Fin 5 → ℝ, (∀ i, |x i| ≤ M) →
      |impactRemainder (x 0) (x 1) (x 2) (x 3) (x 4)| ≤ C ∧
      |amplitudeRemainder (x 0) (x 1) (x 2) (x 3) (x 4)| ≤ C := by
  let f (x : Fin 5 → ℝ) := |impactRemainder (x 0) (x 1) (x 2) (x 3) (x 4)| +
    |amplitudeRemainder (x 0) (x 1) (x 2) (x 3) (x 4)|
  have hf : Continuous f := by dsimp [f,impactRemainder,amplitudeRemainder,remJ,Q]; fun_prop
  let l : Fin 5 → ℝ := fun _ => -M
  let h : Fin 5 → ℝ := fun _ => M
  have nonempty : (Set.Icc l h).Nonempty := Set.nonempty_Icc.mpr (fun _ => neg_le_self hM)
  obtain ⟨v,_,mx⟩ := isCompact_Icc.exists_isMaxOn nonempty hf.continuousOn
  refine ⟨f v,add_nonneg (abs_nonneg _) (abs_nonneg _),fun x hx => ?_⟩
  have hi : x ∈ Set.Icc l h := ⟨fun i => (abs_le.mp (hx i)).1,fun i => (abs_le.mp (hx i)).2⟩
  have bound := mx hi
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans bound,
    (le_add_of_nonneg_left (abs_nonneg _)).trans bound⟩

omit d in
/-- No lower bound on A occurs in the constant. The estimates therefore
    extend to a δ-dependent threshold in the subsequent stopping argument. -/
theorem uniform_rates (M : ℝ) : ∃ C ≥ 0, ∀ {δ s : ℝ} {r U w a b : ℝ → ℝ},
    Rates δ s r U w a b → r s^2 ≤ 1 → |a s| ≤ M → |b s| ≤ M →
    |deriv (impact δ r U w a b) s| ≤ C*δ/r s^4 ∧
    |deriv (amplitude δ r U w a b) s+2*a s/3| ≤ C*δ/r s^3 := by
  obtain ⟨C,hC,bc⟩ := uniform_remainders (max M 2) ((by norm_num : (0:ℝ) ≤ 2).trans (le_max_right _ _))
  refine ⟨C,hC,?_⟩
  intro δ s r U w a b d hr ha hb
  have osc := d.oscillator
  have usq : (U s)^2 ≤ 2 := by nlinarith [sq_nonneg (w s),sq_nonneg ((U s)^2/2-1)]
  have hu : |U s| ≤ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg (U s+1)],by nlinarith [sq_nonneg (U s-1)]⟩
  have hw : |w s| ≤ 2 := abs_le.mpr ⟨by nlinarith [sq_nonneg ((U s)^2/2),sq_nonneg (w s+1)],
    by nlinarith [sq_nonneg ((U s)^2/2),sq_nonneg (w s-1)]⟩
  let x : Fin 5 → ℝ := ![r s^2,U s,w s,a s,b s]
  have hx (i : Fin 5) : |x i| ≤ max M 2 := by
    fin_cases i
    · change |r s^2| ≤ max M 2
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (hr.trans (by norm_num : (1:ℝ) ≤ 2)).trans (le_max_right _ _)
    · exact hu.trans (le_max_right _ _)
    · exact hw.trans (le_max_right _ _)
    · exact ha.trans (le_max_left _ _)
    · exact hb.trans (le_max_left _ _)
  obtain ⟨h₁,h₂⟩ := bc x hx
  have cancel (q v : ℝ) : -q+v+q=v := by ring
  rw [(impact_rate d).deriv,(amplitude_rate d).deriv,cancel,
    abs_div,abs_mul,abs_of_pos d.delta_pos,abs_of_pos (pow_pos d.pos 4),
    abs_div,abs_mul,abs_of_pos d.delta_pos,abs_of_pos (pow_pos d.pos 3),mul_comm C δ]
  exact ⟨div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ d.delta_pos.le)
    (pow_nonneg d.pos.le _),div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ d.delta_pos.le)
    (pow_nonneg d.pos.le _)⟩

end ClosedSimilarity.OuterStress
#print axioms ClosedSimilarity.OuterStress.uniform_rates
