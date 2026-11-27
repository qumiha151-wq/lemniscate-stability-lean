import SolitonClassification.PhysicalIncomingCrossing
import SolitonClassification.CentreDirectionWindow

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open OuterStress

/-- An actual incoming first-hit marker precedes any independently obtained
outer critical time, provided the fixed matching height dominates the fixed
critical radius. Only properties up to the chosen first hit are used. -/
theorem first_section_before_critical {b L C H τ T : ℝ} (bp : 0<b)
    (hL : 1≤L) (high : (1200*L)^2+2≤H) (tiny : b⁻¹≤1/(32*L))
    (hT : T∈Icc (1/2:ℝ) 10000)
    (crit : (centreData b bp).root T^3=L*b⁻¹)
    (strip : OuterStress.Data.CriticalStrip (centreData b bp) L C T)
    (before : ∀s∈Ico (1:ℝ) τ, H < -height (centreAt b s))
    (chart : ∀s∈Ico (1:ℝ) τ, regular (centreAt b s) ∧ 1≤ innerRoot (centreAt b s)) :
    τ≤T := by
  let δ := b⁻¹
  have dp : 0<δ := inv_pos.mpr bp
  let z := centreData b bp
  let x := centreAt b
  have lp : 0<L := by linarith
  have dz := solution_derivative 1 (![0,b,0,0] : Phase)
  have inits : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  have rootSq : z.root T^2=z.amplitude T := Real.sq_sqrt (Real.sqrt_nonneg _)
  have one : 1≤T := by
    by_contra! bad
    have tp : 0≤T := by linarith [hT.1]
    have ba := (z.centre_bounds dp inits.1 inits.2.1 inits.2.2.1 inits.2.2.2 tp).2
    have sq := pow_le_pow_left₀ tp bad.le 2
    have r : 1/2≤z.root T := le_of_sq_le_sq (by nlinarith) (Real.sqrt_nonneg _)
    have hi := (le_div_iff₀ (by positivity : 0<32*L)).mp tiny
    change z.root T^3=L*b⁻¹ at crit
    nlinarith only [crit,hi,pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) r 3]
  by_contra! late
  have htau : T∈Ico (1:ℝ) τ := ⟨one,late⟩
  obtain ⟨reg,far⟩ := chart T htau
  obtain ⟨_,_,_,al,_,cube,_,_⟩ := outer_chart dp _ dz T reg
  change z.along T=along (x T)*outerRadius δ (x T) at al
  change innerRoot (x T)^3*outerRadius δ (x T)*δ=z.root T^3 at cube
  have rp : 0<outerRadius δ (x T) := mul_pos (Real.sqrt_pos.mpr dp) (pow_pos (Real.rpow_pos_of_pos reg.1 _) _)
  have un := (unit_chart _ reg).2
  have ca : along (x T)≤1 := by nlinarith [sq_nonneg (across (x T)),sq_nonneg (along (x T)-1)]
  have st := (strip T ⟨hT.1,le_rfl⟩).1
  change 1/1200<z.along T at st
  have lower : 1/1200≤outerRadius δ (x T) := by linarith [mul_le_mul_of_nonneg_right ca rp.le]
  change 1≤ innerRoot (x T) at far
  have npos : 0≤ innerRoot (x T) := by linarith
  have eq := mul_right_cancel₀ dp.ne' (cube.trans crit)
  have up := mul_le_mul_of_nonneg_left lower (pow_nonneg npos 3)
  have n3 : innerRoot (x T)≤ innerRoot (x T)^3 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr far)
      (by nlinarith [far,sq_nonneg (innerRoot (x T))] : 0≤ innerRoot (x T)^2+innerRoot (x T))]
  have rootcap : innerRoot (x T)≤1200*L := by linarith
  have mag := pow_le_pow_left₀ npos rootcap 2
  have h := (abs_le.mp (height_error reg far)).2
  have first := before T htau
  change H < -height (x T) at first
  nlinarith only [first,h,mag,high,mul_le_mul_of_nonneg_left ca (sq_nonneg (innerRoot (x T)))]

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.first_section_before_critical

