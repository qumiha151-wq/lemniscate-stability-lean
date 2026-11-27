import SolitonClassification.OuterStressOrbit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Drift of the direction of normalized elastic stress before it vanishes.
All vectors are expressed in a fixed Euclidean frame. The correction removes
the leading oscillation before taking absolute values. -/
noncomputable section
namespace ClosedSimilarity.OuterStress.Direction
open Set

def horizontal (U w θ : ℝ) := U^2/2*Real.cos θ-w*Real.sin θ
def vertical (U w θ : ℝ) := U^2/2*Real.sin θ+w*Real.cos θ
def spin (r U w a b : ℝ) := -(w*a+U^2/2*b)*(U^2/2)/r^2
def corrector (r U a : ℝ) := a*U^3/(6*r^3)

theorem components_unit {U w θ : ℝ} (osc : (U^2/2)^2+w^2=1) :
    horizontal U w θ ^2 + vertical U w θ ^2=1 := by
  have h := Real.cos_sq_add_sin_sq θ
  dsimp [horizontal,vertical]
  linear_combination ((U^2/2)^2+w^2)*h + osc

variable {δ s : ℝ} {r U w a b θ : ℝ → ℝ}

/-- The angular velocity of the true normalized stress in a fixed frame. -/
theorem component_rates (d : Rates δ s r U w a b) (dt : HasDerivAt θ (r s*U s/δ) s) :
    HasDerivAt (fun t => horizontal (U t) (w t) (θ t))
      (-spin (r s) (U s) (w s) (a s) (b s)*vertical (U s) (w s) (θ s)) s ∧
    HasDerivAt (fun t => vertical (U t) (w t) (θ t))
      (spin (r s) (U s) (w s) (a s) (b s)*horizontal (U s) (w s) (θ s)) s := by
  constructor
  · convert! (((d.dU.pow 2).div_const 2).mul dt.cos).sub (d.dw.mul dt.sin) using 1
    dsimp [horizontal,vertical,spin]
    field_simp [d.pos.ne',d.delta_pos.ne']
    ring
  · convert! (((d.dU.pow 2).div_const 2).mul dt.sin).add (d.dw.mul dt.cos) using 1
    dsimp [horizontal,vertical,spin]
    field_simp [d.pos.ne',d.delta_pos.ne']
    ring

def remainder (i U w a b : ℝ) :=
  let u := U^2/2
  let p := w*a+u*b
  u*U^3*i^3/6-p*u*b*U^3*i^5/6+a*U^3*w*p*i^5/2

theorem correction_rate (d : Rates δ s r U w a b) :
    HasDerivAt (fun t => δ*corrector (r t) (U t) (a t))
      (-spin (r s) (U s) (w s) (a s) (b s) - b s*(U s^2/2)^2/(r s)^2 +
        δ*remainder (1/r s) (U s) (w s) (a s) (b s)) s := by
  convert! ((((d.da.mul (d.dU.pow 3)).div ((d.dr.pow 3).const_mul 6)
    (mul_ne_zero (by norm_num) (pow_ne_zero 3 d.pos.ne')))).const_mul δ) using 1
  dsimp [corrector,spin,remainder]
  field_simp [d.pos.ne',d.delta_pos.ne']
  ring

def corrected (δ : ℝ) (r U w a θ : ℝ → ℝ) (t : ℝ) :=
  horizontal (U t) (w t) (θ t) - δ*corrector (r t) (U t) (a t)*vertical (U t) (w t) (θ t)

/-- Write b=δj for the transverse position component. The corrected
fixed-frame velocity has an exact factor δ and a polynomial remainder
in the bounded chart variables and reciprocal stress root. -/
def drift (i U w a b j X Y : ℝ) :=
  let u := U^2/2
  let p := w*a+u*b
  (j*u^2*i^2-remainder i U w a b)*Y + (a*U^3*i^3/6)*p*u*i^2*X

theorem corrected_rate (d : Rates δ s r U w a b) (dt : HasDerivAt θ (r s*U s/δ) s)
    {j : ℝ} (hj : b s = δ*j) :
    HasDerivAt (corrected δ r U w a θ)
      (δ*drift (1/r s) (U s) (w s) (a s) (b s) j
        (horizontal (U s) (w s) (θ s)) (vertical (U s) (w s) (θ s))) s := by
  obtain ⟨dx,dy⟩ := component_rates d dt
  convert! dx.sub ((correction_rate d).mul dy) using 1
  dsimp only [drift,corrector,spin]
  simp only [hj]
  field_simp [d.pos.ne']
  ring

private theorem polynomial_budget (M : ℝ) (hM : 0≤M) :
    ∃ C≥0, ∀ i U w a b j X Y : ℝ, |i|≤M → |U|≤M → |w|≤M → |a|≤M → |b|≤M →
      |j|≤M → |X|≤M → |Y|≤M → |drift i U w a b j X Y|≤C ∧ |a*U^3*i^3*Y/6|≤C := by
  let lo : Fin 8 → ℝ := fun _ => -M
  let hi : Fin 8 → ℝ := fun _ => M
  let F := fun z : Fin 8 → ℝ => |drift (z 0) (z 1) (z 2) (z 3) (z 4) (z 5) (z 6) (z 7)| +
    |z 3*(z 1)^3*(z 0)^3*z 7/6|
  have cont : Continuous F := by dsimp [F,drift,remainder]; fun_prop
  obtain ⟨v,_,mv⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (show lo≤hi from fun _ => neg_le_self hM)) cont.continuousOn
  refine ⟨F v,add_nonneg (abs_nonneg _) (abs_nonneg _),?_⟩
  intro i U w a b j X Y h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  let z : Fin 8 → ℝ := ![i,U,w,a,b,j,X,Y]
  have bounds (n : Fin 8) : |z n|≤M := by fin_cases n <;> assumption
  have mem : z∈Icc lo hi := ⟨fun n => (abs_le.mp (bounds n)).1,fun n => (abs_le.mp (bounds n)).2⟩
  have A := mv mem
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans A,
    (le_add_of_nonneg_left (abs_nonneg _)).trans A⟩

/-- A uniform uncorrected direction estimate on any bounded slow-time
interval on which the stress root stays away from zero and the transverse
position divided by δ is bounded. One can choose either axis as horizontal. -/
theorem horizontal_change_on_outer_interval (M : ℝ) (hM : 1≤M) :
    ∃ C≥0, ∀ {δ S T : ℝ} {r U w a b θ : ℝ → ℝ}, S≤T →
      (∀ t∈Icc S T, Rates δ t r U w a b ∧ HasDerivAt θ (r t*U t/δ) t ∧
        |1/r t|≤M ∧ |U t|≤M ∧ |w t|≤M ∧ |a t|≤M ∧ |b t|≤M ∧ |b t/δ|≤M) →
      |horizontal (U T) (w T) (θ T) - horizontal (U S) (w S) (θ S)| ≤
        δ*C*(T-S+2) := by
  obtain ⟨C,hC,budget⟩ := polynomial_budget M (by linarith)
  refine ⟨C,hC,?_⟩
  intro δ S T r U w a b θ st info
  let X := fun t => horizontal (U t) (w t) (θ t)
  let Y := fun t => vertical (U t) (w t) (θ t)
  let f := corrected δ r U w a θ
  have hδ := (info S (left_mem_Icc.mpr st)).1.delta_pos
  have atPoint (t : ℝ) (ht : t∈Icc S T) : DifferentiableAt ℝ f t ∧
      ‖deriv f t‖≤δ*C ∧ |X t-f t|≤δ*C := by
    obtain ⟨d,dt,hi,hU,hw,ha,hb,hj⟩ := info t ht
    have hu : X t^2+Y t^2=1 := components_unit d.oscillator
    have hx : |X t|≤1 := le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (Y t)]) zero_le_one
    have hy : |Y t|≤1 := le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (X t)]) zero_le_one
    have K := budget _ _ _ _ _ _ _ _ hi hU hw ha hb hj (hx.trans hM) (hy.trans hM)
    have df := corrected_rate d dt (j:=b t/δ) (by field_simp)
    refine ⟨df.differentiableAt,?_,?_⟩
    · change ‖deriv (corrected δ r U w a θ) t‖≤δ*C
      rw [df.deriv,Real.norm_eq_abs,abs_mul,abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_left K.1 hδ.le
    · have eq : X t-f t=δ*(a t*(U t)^3*(1/r t)^3*Y t/6) := by
        dsimp [X,Y,f,corrected,corrector]; field_simp [d.pos.ne']; ring
      rw [eq,abs_mul,abs_of_pos hδ]
      exact mul_le_mul_of_nonneg_left K.2 hδ.le
  have h₁ := atPoint T (right_mem_Icc.mpr st)
  have h₂ := atPoint S (left_mem_Icc.mpr st)
  have hd := (convex_Icc S T).norm_image_sub_le_of_norm_deriv_le
    (fun t ht => (atPoint t ht).1) (fun t ht => (atPoint t ht).2.1)
    (left_mem_Icc.mpr st) (right_mem_Icc.mpr st)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr st)] at hd
  have q := abs_sub_le (X T) (f T) (X S)
  have q' := abs_sub_le (f T) (f S) (X S)
  rw [abs_sub_comm (f S) (X S)] at q'
  change |X T-X S| ≤ _
  nlinarith only [q,q',h₁.2.2,h₂.2.2,hd]

end ClosedSimilarity.OuterStress.Direction
#print axioms ClosedSimilarity.OuterStress.Direction.horizontal_change_on_outer_interval
