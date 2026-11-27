import Migration.ProjectedAdjoint
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
open Set
namespace MigrationGeometry.Adjoint.Frame
variable {L : ℝ} (f : Frame 1 L)

def stressSize (s : ℝ) := Real.sqrt (1+(f.v s)^2+((f.k s)^2/2)^2)

theorem stressSize_pos (s : ℝ) : 0<f.stressSize s := by unfold stressSize; positivity
theorem stressSize_sq (s : ℝ) : (f.stressSize s)^2=1+(f.v s)^2+((f.k s)^2/2)^2 :=
  Real.sq_sqrt (by positivity)

theorem stressSize_d (s : ℝ) :
    HasDerivAt f.stressSize (-f.v s*f.p s/f.stressSize s) s := by
  have d := ((((f.vD s).pow 2).const_add 1).add ((((f.kD s).pow 2).div_const 2).pow 2)).sqrt
    (show 1+f.v s^2+(f.k s^2/2)^2≠0 by positivity)
  apply d.congr_deriv
  change _ = -f.v s*f.p s/Real.sqrt (1+f.v s^2+(f.k s^2/2)^2)
  simp only [Pi.add_apply,Pi.pow_apply]
  have hn : Real.sqrt (1+f.v s^2+(f.k s^2/2)^2)≠0 := (f.stressSize_pos s).ne'
  field_simp [hn]; ring

theorem stressSize_dominates (s : ℝ) : |f.v s|≤f.stressSize s ∧ (f.k s)^2/2≤f.stressSize s := by
  have h := f.stressSize_sq s
  have v := f.stressSize_pos s
  constructor
  · rw [← abs_of_pos v]
    apply sq_le_sq.mp
    linarith only [h,sq_nonneg ((f.k s)^2/2)]
  · nlinarith only [h,sq_nonneg (f.v s),v.le,sq_nonneg (f.k s)]

/-- Every entire unit-rate support profile in the radius-two disk has
    uniformly bounded stress, independent of its period. -/
theorem stressSize_disk_two (rad : ∀ s, (f.p s)^2+(f.q s)^2≤4) (a : ℝ) :
    f.stressSize a<1000 := by
  have pq (s : ℝ) : |f.p s|≤2 ∧ |f.q s|≤2 := by
    constructor <;> rw [← abs_of_pos (by norm_num : 0<(2:ℝ))]
    · apply sq_le_sq.mp; linarith only [rad s,sq_nonneg (f.q s)]
    · apply sq_le_sq.mp; linarith only [rad s,sq_nonneg (f.p s)]
  have diff : Differentiable ℝ f.stressSize := fun s => (f.stressSize_d s).differentiableAt
  have derivBound (s : ℝ) : |deriv f.stressSize s|≤2 := by
    rw [(f.stressSize_d s).deriv,abs_div,abs_mul,abs_neg,abs_of_pos (f.stressSize_pos s)]
    apply (div_le_iff₀ (f.stressSize_pos s)).mpr
    linarith only [mul_le_mul (f.stressSize_dominates s).1 (pq s).1 (abs_nonneg _) (f.stressSize_pos s).le]
  let w := f.stressSize a
  by_contra! big
  have wb : 1000≤w := big
  let b := a+w/8
  have ab : a≤b := by dsimp [b]; linarith
  have window (s : ℝ) (hs : s∈Icc a b) : 3*w/4≤f.stressSize s ∧ f.stressSize s≤5*w/4 := by
    have upper := image_sub_le_mul_sub_of_deriv_le diff (fun x => (abs_le.mp (derivBound x)).2) hs.1
    have lower := mul_sub_le_image_sub_of_le_deriv diff (fun x => (abs_le.mp (derivBound x)).1) hs.1
    have finish : s≤a+w/8 := hs.2
    change _≤f.stressSize s-w at lower
    change f.stressSize s-w≤_ at upper
    constructor <;> linarith only [lower,upper,finish]
  let G := fun s => f.k s*f.v s+4*w*f.virial s
  let D := fun s => (f.v s)^2-(f.k s)^4/2-f.k s*f.p s+4*w*((f.k s)^2/2-(f.p s)^2)
  have dG (s : ℝ) : HasDerivAt G (D s) s := by
    apply (((f.kD s).mul (f.vD s)).add ((f.virialD s).const_mul (4*w))).congr_deriv
    dsimp [D]; ring
  have cap (s : ℝ) (hs : s∈Icc a b) : (f.k s)^2≤5*w/2 ∧ |f.v s|≤5*w/4 := by
    have H := window s hs
    obtain ⟨v,k⟩ := f.stressSize_dominates s
    exact ⟨by linarith only [k,H.2],v.trans H.2⟩
  have slope (s : ℝ) (hs : s∈Icc a b) : w^2/2≤D s := by
    have h := cap s hs
    have p2 : (f.p s)^2≤4 := by linarith only [rad s,sq_nonneg (f.q s)]
    have en := f.stressSize_sq s
    have es := pow_le_pow_left₀ (by linarith : 0≤3*w/4) (window s hs).1 2
    have k4 := mul_nonneg (sub_nonneg.mpr h.1) (sq_nonneg (f.k s))
    have pk := sq_nonneg (f.k s/2-f.p s)
    have wp := mul_nonneg (by linarith : 0≤w) (sub_nonneg.mpr p2)
    dsimp [D]
    nlinarith only [es,en,k4,pk,wp,p2,mul_nonneg (show 0≤w-2 by linarith) (sq_nonneg (f.k s)),
      mul_nonneg (show 0≤w-1000 by linarith) (show 0≤w by linarith),wb]
  have ends (s : ℝ) (hs : s∈Icc a b) : |G s|≤23*w^2 := by
    obtain ⟨k,v⟩ := cap s hs
    have k1 : |f.k s|≤w := by
      have ww := mul_nonneg (show 0≤w-3 by linarith) (show 0≤w by linarith)
      rw [← abs_of_nonneg (show 0≤w by linarith)]
      apply sq_le_sq.mp
      nlinarith only [k,ww,wb]
    have wa : 0≤w := by linarith
    have vir : |f.virial s|≤5*w := by
      unfold virial
      refine (abs_add_le ..).trans ?_
      rw [abs_mul,abs_mul,abs_of_nonneg (show 0≤(f.k s)^2/2 by positivity)]
      linarith only [mul_le_mul v (pq s).1 (abs_nonneg _) (by positivity : 0≤5*w/4),
        mul_le_mul (show (f.k s)^2/2≤5*w/4 by linarith only [k]) (pq s).2
          (abs_nonneg _) (by positivity : 0≤5*w/4)]
    dsimp [G]
    refine (abs_add_le ..).trans ?_
    rw [abs_mul,abs_mul,abs_of_nonneg (show 0≤4*w by positivity)]
    nlinarith only [mul_le_mul k1 v (abs_nonneg _) wa,mul_le_mul_of_nonneg_left vir (show 0≤4*w by positivity),sq_nonneg w]
  have hdiff : Differentiable ℝ G := fun t => (dG t).differentiableAt
  have rise := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun t ht => (dG t).deriv.symm ▸ slope t (interior_subset ht)) a (left_mem_Icc.mpr ab)
    b (right_mem_Icc.mpr ab) ab
  have ef := (abs_le.mp (ends b (right_mem_Icc.mpr ab))).2
  have ei := (abs_le.mp (ends a (left_mem_Icc.mpr ab))).1
  change w^2/2*(a+w/8-a)≤G b-G a at rise
  have high := mul_nonneg (show 0≤w-1000 by linarith) (sq_nonneg w)
  nlinarith only [rise,ef,ei,high,sq_pos_of_pos (show 0<w by linarith)]

end MigrationGeometry.Adjoint.Frame
#print axioms MigrationGeometry.Adjoint.Frame.stressSize_disk_two
