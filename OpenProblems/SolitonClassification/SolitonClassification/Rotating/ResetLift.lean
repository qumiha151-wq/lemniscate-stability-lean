import SolitonClassification.Rotating.ResetAugmentedBounds
import SolitonClassification.Rotating.CertifiedResetFlow
noncomputable section
open Set
namespace SolitonClassification.Rotating.DyadicReset
abbrev d := Middle.den
def weightFactor : ℝ := 1/16384
def lift (p : Data) (t : ℝ) : Aug :=
  (path p d t,fun j => weightFactor • column p d j t)
def liftVelocity (p : Data) (t : ℝ) : Aug :=
  (velocity p d t,fun j => weightFactor • columnVelocity p d j t)

theorem lift_deriv (p : Data) (t : ℝ) : HasDerivAt (lift p) (liftVelocity p t) t := by
  apply (path_deriv p d t).prodMk
  apply hasDerivAt_pi.mpr
  exact fun j=>(column_deriv p d j t).const_smul weightFactor

theorem eval_cont (l : List ℤ) : Continuous (fun x => eval x l) := by
  induction l with
  | nil => exact continuous_const
  | cons a l ih => exact continuous_const.add (continuous_id.mul ih)

theorem liftVelocity_cont (p : Data) : Continuous (liftVelocity p) := by
  apply Continuous.prodMk
  · apply continuous_pi
    exact fun i => (eval_cont _).div_const _
  · apply continuous_pi
    intro j
    change Continuous (weightFactor • columnVelocity p d j)
    refine Continuous.const_smul ?_ weightFactor
    apply continuous_pi
    intro i
    by_cases hi : i.val=4
    · simp only [columnVelocity,if_pos hi]; exact continuous_const
    · simp only [columnVelocity,if_neg hi]; exact (eval_cont _).div_const _

theorem linear_smul (x u : State) (c : ℝ) : linear x (c • u)=c • linear x u := by
  rw [←field_fderiv_apply,ContinuousLinearMap.map_smul,field_fderiv_apply]

theorem lift_residual {p : Data} (C : Certified p) {t : ℝ} (ht : t∈Icc 0 1) :
    ‖liftVelocity p t-h • augmented (lift p t)‖≤eps := by
  rw [Prod.norm_def,max_le_iff]
  refine ⟨certified_state C ht,?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num [eps])).mpr
  intro j
  change ‖weightFactor • columnVelocity p d j t - h • linear _ (weightFactor • column p d j t)‖≤_
  rw [linear_smul,smul_comm h weightFactor,←smul_sub,norm_smul,Real.norm_eq_abs]
  exact ((mul_le_mul_of_nonneg_right (by norm_num [weightFactor] : |weightFactor|≤1) (norm_nonneg _)).trans
    (by simpa only [one_mul,lift] using certified_variation C ht j))

def Small (p : Data) := (∀i : Fin 5,(l1 (p i):ℤ)≤9*d) ∧
  (∀i : Fin 25,(l1 (p (6+i.val)):ℤ)≤16384*d)

theorem lift_inner {p : Data} (small : Small p) {t : ℝ} (ht : t∈Icc 0 1) : Inner (lift p t) := by
  have hp : 0<(d:ℝ) := by norm_num [d,Middle.den]
  have coord (i : Nat) (m : ℤ) (hm : (l1 (p i):ℤ)≤m*d) :
      |eval t (p i)/(d:ℝ)|≤(m:ℝ) := by
    rw [abs_div,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    exact (abs_eval _ (by rw [abs_of_nonneg ht.1];exact ht.2)).trans (by exact_mod_cast hm)
  constructor
  · intro i hi
    exact coord i 9 (small.1 ⟨i.val,hi⟩)
  · intro j i
    change |weightFactor*(columnOf d _ j i)|≤1
    unfold columnOf
    split
    · split <;> norm_num [weightFactor]
    · have hslot : 5*j.val+(if i.val=5 then 4 else i.val)<25 := by split <;> omega
      let m : Fin 25 := ⟨_,hslot⟩
      have bd := coord (6+m.val) 16384 (small.2 m)
      change |weightFactor*(eval t (p (6+5*j.val+(if i.val=5 then 4 else i.val)))/d)|≤1
      rw [abs_mul]
      have off : 6+5*j.val+(if i.val=5 then 4 else i.val)=6+m.val := by dsimp [m];omega
      rw [off]
      have cw : |weightFactor|=(1/16384:ℝ) := by norm_num [weightFactor]
      rw [cw]; linarith only [bd]

end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.lift_inner
#print axioms SolitonClassification.Rotating.DyadicReset.lift_residual
