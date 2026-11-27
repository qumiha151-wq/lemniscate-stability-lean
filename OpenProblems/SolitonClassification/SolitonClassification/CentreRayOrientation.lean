import SolitonClassification.CentreDirectionWindow
import SolitonClassification.CentreLaboratoryFrame

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data

/-- In the fixed laboratory frame of the initial tangent, every certified
outer flight ends close to the positive vertical ray. The same estimate applies
to any prefix ending at or after the entry time. -/
theorem critical_flight_orientation :
    ∃ L₀≥1, ∀ (C η : ℝ), 0<η → η≤1/2 → ∃ B≥1,
      ∀ {δ L T : ℝ} (z : Data δ) (θ : ℝ → ℝ), 0<δ → L₀≤L →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 → θ 0=0 →
      T∈Icc (1/2:ℝ) 10000 → CriticalStrip z L C T →
      (∀ s∈Icc 0 T, HasDerivAt θ (z.K s/δ) s) → B*δ≤1/2 →
      |z.labX θ T|≤B*δ+3825*η^2 ∧
      1/2400-B*δ-3825*η^2≤z.labY θ T := by
  obtain ⟨L₀,hL₀,split⟩ := split_critical_window
  obtain ⟨E,hE,early⟩ := centre_initial_across
  refine ⟨L₀,hL₀,?_⟩
  intro C η hη smallη
  let A := max E (C/η^3)
  have hA : 0≤A := hE.trans (le_max_left ..)
  let M := max (max 10000 (1/η)) A
  have m1 : (10000:ℝ)≤M := (le_max_left ..).trans (le_max_left ..)
  have mi : 1/η≤M := (le_max_right ..).trans (le_max_left ..)
  have ma : A≤M := le_max_right .. 
  obtain ⟨D,hD,drift⟩ := Direction.horizontal_change_on_outer_interval M (by linarith)
  let B := 1+10000*(10002*D)+A
  have B1 : 1≤B := by dsimp [B]; linarith
  refine ⟨B,B1,?_⟩
  intro δ L T z θ hd hl hk hv hp hq th0 ht strip dθ tiny
  obtain ⟨S,hS,above,elapsed⟩ := split z hd hl hk hv hp hq ht strip hη smallη
  have sn : 0≤S := by linarith [hS.1]
  let I := Icc (0:ℝ) S
  have iS : S∈I := right_mem_Icc.mpr sn
  have full (x : ℝ) (hx : x∈I) : x∈Icc 0 T := ⟨hx.1,hx.2.trans hS.2⟩
  have rp (x : ℝ) (hx : x∈I) : 0<z.root x := hη.trans_le (above x hx)
  have ap (x : ℝ) (hx : x∈I) : 0<z.amplitude x := Real.sqrt_pos.mp (rp x hx)
  have ac (x : ℝ) (hx : x∈I) : |z.across x|≤A*δ := by
    by_cases short : x≤1/2
    · exact (early z hd hk hv hp hq x ⟨hx.1,short⟩).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) hd.le)
    · have late := strip x ⟨le_of_not_ge short,(full x hx).2⟩
      have lo := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le (above x hx) 3) (abs_nonneg (z.across x))
      have bd := (le_div_iff₀ (pow_pos hη 3)).mpr (lo.trans late.2.2.2)
      rw [←div_mul_eq_mul_div] at bd
      exact bd.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hd.le)
  have dt (x : ℝ) (hx : x∈I) : HasDerivAt θ (z.root x*z.shape x/δ) x := by
    have k : z.root x*z.shape x=z.K x := by unfold shape; field_simp [(rp x hx).ne']
    rw [k]; exact dθ x (full x hx)
  let X := fun x => Direction.horizontal (z.shape x) (z.slope x) (θ x)
  let Y := fun x => Direction.vertical (z.shape x) (z.slope x) (θ x)
  have unit (x : ℝ) (hx : x∈I) : X x^2+Y x^2=1 :=
    Direction.components_unit (z.normalized_rates x (ap x hx) hd).oscillator
  have x0 : X 0=0 := by simp [X,Direction.horizontal,shape,hk,th0]
  have y0 : Y 0=1 := by norm_num [Y,Direction.vertical,slope,amplitude,th0,hv,hk]
  have xbound (t : ℝ) (it : t∈I) : |X t|≤(10002*D)*δ := by
    have q := @drift δ 0 t z.root z.shape z.slope z.along z.across θ it.1 (fun x hx => by
      have ix : x∈I := ⟨hx.1,hx.2.trans it.2⟩
      have rates := z.normalized_rates x (ap x ix) hd
      have o := rates.oscillator
      have U : |z.shape x|≤2 := le_of_sq_le_sq
        (by rw [sq_abs]; nlinarith [sq_nonneg (z.slope x),sq_nonneg ((z.shape x)^2/2-1)]) (by norm_num)
      have W : |z.slope x|≤1 := le_of_sq_le_sq
        (by rw [sq_abs]; nlinarith [sq_nonneg ((z.shape x)^2/2)]) zero_le_one
      have ab := z.support_component_bounds hd hk hv hp hq ⟨ix.1,(full x ix).2.trans ht.2⟩ (ap x ix)
      refine ⟨rates,dt x ix,?_,U.trans (by linarith),W.trans (by linarith),ab.1.trans m1,ab.2.trans m1,?_⟩
      · rw [abs_of_pos (one_div_pos.mpr (rp x ix))]
        exact (one_div_le_one_div_of_le hη (above x ix)).trans mi
      · rw [abs_div,abs_of_pos hd]
        exact ((div_le_iff₀ hd).mpr (ac x ix)).trans ma)
    change |X t-X 0|≤_ at q
    rw [x0,sub_zero] at q
    have cap : t≤10000 := (full t it).2.trans ht.2
    nlinarith only [q,mul_le_mul_of_nonneg_left cap (mul_nonneg hd.le hD)]
  have small (t : ℝ) (it : t∈I) : |X t|≤1/2 := by
    apply (xbound t it).trans
    apply le_trans _ tiny
    apply mul_le_mul_of_nonneg_right _ hd.le
    dsimp [B]; linarith
  have cy : ContinuousOn Y I := fun x hx =>
    (Direction.component_rates (z.normalized_rates x (ap x hx) hd) (dt x hx)).2.continuousAt.continuousWithinAt
  have ypos : 1/2≤Y S := by
    have pos : 0≤Y S := by
      by_contra! neg
      obtain ⟨x,hx,zero⟩ := intermediate_value_Icc' sn cy (show (0:ℝ)∈Icc (Y S) (Y 0) from ⟨neg.le,by linarith⟩)
      have ux := unit x hx
      rw [zero] at ux
      nlinarith [(abs_le.mp (small x hx)).1,(abs_le.mp (small x hx)).2,sq_le_sq' (abs_le.mp (small x hx)).1 (abs_le.mp (small x hx)).2]
    have sq := pow_le_pow_left₀ (abs_nonneg _) (small S iS) 2
    rw [sq_abs] at sq
    nlinarith [unit S iS]
  have yabs : |Y S|≤1 := le_of_sq_le_sq (by rw [sq_abs]; nlinarith [unit S iS,sq_nonneg (X S)]) zero_le_one
  have xabs : |X S|≤1 := (small S iS).trans (by norm_num)
  have ab := z.support_component_bounds hd hk hv hp hq ⟨sn,(full S iS).2.trans ht.2⟩ (ap S iS)
  obtain ⟨frameX,frameY⟩ := z.lab_stress_frame θ (ap S iS)
  change z.labX θ S=z.along S*X S-z.across S*Y S at frameX
  change z.labY θ S=z.along S*Y S+z.across S*X S at frameY
  have xS : |z.labX θ S|≤B*δ := by
    rw [frameX]
    have sum := abs_sub_le (z.along S*X S) 0 (z.across S*Y S)
    simp only [sub_zero,zero_sub,abs_neg,abs_mul] at sum
    have e := mul_le_mul ab.1 (xbound S iS) (abs_nonneg _) (by norm_num : (0:ℝ)≤10000)
    have f := mul_le_mul (ac S iS) yabs (abs_nonneg _) (mul_nonneg hA hd.le)
    dsimp [B]; nlinarith only [sum,e,f,hd]
  have yS : 1/2400-B*δ≤z.labY θ S := by
    have up := (strip S hS).1
    have proj := mul_le_mul (le_of_lt up) ypos (by norm_num : (0:ℝ)≤1/2) (by linarith)
    have err := neg_abs_le (z.across S*X S)
    rw [abs_mul] at err
    have f := mul_le_mul (ac S iS) xabs (abs_nonneg _) (mul_nonneg hA hd.le)
    rw [frameY]; dsimp [B]
    nlinarith only [proj,err,f,hd,mul_nonneg hD hd.le]
  have flight := z.lab_lipschitz hS.2 hd (fun x hx => dθ x ⟨sn.trans hx.1,hx.2⟩)
  have chord := abs_sub_le (z.labX θ T) (z.labX θ S) 0
  simp only [sub_zero] at chord
  exact ⟨by linarith [flight.1],by linarith [(abs_le.mp flight.2).1]⟩

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.critical_flight_orientation
