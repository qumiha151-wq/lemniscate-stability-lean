import SolitonClassification.OuterDescentBudget
import SolitonClassification.OuterRadiusBarrier

noncomputable section
set_option maxHeartbeats 2000000
open Set
namespace ClosedSimilarity.OuterStress

private theorem keep_strict {S T : ℝ} {f : ℝ → ℝ} (_st : S≤T)
    (cont : ContinuousOn f (Icc S T)) (start : 0<f S)
    (improve : ∀ u ∈ Icc S T, (∀x ∈ Icc S u, 0≤f x) → 0<f u) :
    ∀ t ∈ Icc S T, 0<f t := by
  intro t ht
  by_contra! h
  have ne : ∃y∈Icc S t, f y=0 := intermediate_value_Icc' ht.1
    (cont.mono (Icc_subset_Icc_right ht.2)) (show (0:ℝ)∈Icc (f t) (f S) from ⟨h,start.le⟩)
  let zeros := {x ∈ Icc S t | f x=0}
  have compact : IsCompact zeros := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_eq (cont.mono (Icc_subset_Icc_right ht.2)) continuousOn_const)
    (fun _ hx => hx.1)
  obtain ⟨u,hu,first⟩ := compact.exists_isMinOn
    (show zeros.Nonempty from by obtain ⟨y,hy,eq⟩ := ne; exact ⟨y,hy,eq⟩) continuous_id.continuousOn
  have inside : u∈Icc S T := ⟨hu.1.1,hu.1.2.trans ht.2⟩
  have atU := improve u inside (fun x hx => by
    by_contra! neg
    obtain ⟨y,hy,eq⟩ := intermediate_value_Icc' hx.1 (cont.mono (Icc_subset_Icc_right (hx.2.trans inside.2)))
      (show (0:ℝ)∈Icc (f x) (f S) from ⟨neg.le,start.le⟩)
    have yy : u≤y := first (show y∈zeros from ⟨⟨hy.1,(hy.2.trans hx.2).trans hu.1.2⟩,eq⟩)
    have same : y=x := le_antisymm hy.2 (hx.2.trans yy)
    exact neg.ne (same ▸ eq))
  exact atU.ne' hu.2

namespace Data
variable {δ : ℝ} (z : Data δ)

private theorem continuous_amplitude : Continuous z.amplitude := by
  have K := continuous_iff_continuousAt.mpr (fun x => (z.dK x).continuousAt)
  have V := continuous_iff_continuousAt.mpr (fun x => (z.dV x).continuousAt)
  exact ((((K.pow 2).div_const 2).pow 2).add (V.pow 2)).sqrt

/-- With only the central initial values prescribed, every sufficiently large
    marker reaches the first critical stress layer while remaining radially
    aligned. The asserted slope and error bounds are independent of L and δ. -/
theorem reaches_critical_layer :
    ∃ L₀≥1, ∃ C≥1, ∀ L≥L₀, ∀ {δ : ℝ} (z : Data δ), 0<δ → δ≤1/(32*L) →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      ∃ T ∈ Icc (1/2:ℝ) 10000, z.root T^3=L*δ ∧
        ∀ s ∈ Icc (1/2:ℝ) T, 1/1200 < z.along s ∧ z.amplitude s<2 ∧
          L*δ≤z.root s^3 ∧ |z.across s| * z.root s^3≤C*δ := by
  obtain ⟨E,hE,entry⟩ := centre_entry
  obtain ⟨Lmin,Lone,C,Co,descent⟩ := critical_descent 10000 (1/1200) E (by norm_num) hE
  let L₀ := max Lmin (1000000000000*C)
  refine ⟨L₀,Lone.trans (le_max_left ..),C,Co,?_⟩
  intro L large δ z hd tiny hk hv hp hq
  have Lpos : 0<L := (by linarith : 0<Lmin).trans_le ((le_max_left ..).trans large)
  have dl : δ*L≤1/32 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ)<32*L)).mp tiny; linarith
  have small : δ≤1/32 := by
    have L1 : 1≤L := Lone.trans ((le_max_left ..).trans large)
    linarith [mul_le_mul_of_nonneg_left L1 hd.le]
  obtain ⟨initA,_,initJ,Alow,Ahi⟩ := entry z hd small hk hv hp hq
  let S := (1/2:ℝ)
  let R := fun x => z.root x^3
  have cR : Continuous R := (z.continuous_amplitude.sqrt).pow 3
  have initial : L*δ<R S := by
    have sq : z.root S^2=z.amplitude S := Real.sq_sqrt (Real.sqrt_nonneg _)
    have rl : 1/2≤z.root S := le_of_sq_le_sq (by change 1/2≤z.amplitude S at Alow; nlinarith) (Real.sqrt_nonneg _)
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rl 3
    dsimp [R]; linarith
  have protect (T : ℝ) (ht : T ∈ Icc S 10000) (above : ∀x ∈ Icc S T, L*δ≤R x) :
      ∀ x ∈ Icc S T, 1/1200 < z.along x ∧ z.amplitude x<2 ∧ |z.across x| * R x≤C*δ := by
    let I := Icc S T
    let f := fun x => min (z.along x-1/1200) (2-z.amplitude x)
    have amp (x : ℝ) (hx : x∈I) : 0<z.amplitude x := by
      have r : 0<R x := (mul_pos Lpos hd).trans_le (above x hx)
      have rs : z.root x^2=z.amplitude x := Real.sq_sqrt (Real.sqrt_nonneg _)
      dsimp [R] at r
      by_contra! bad
      have zero : z.root x=0 := by nlinarith [sq_nonneg (z.root x)]
      simp [zero] at r
    have cont : ContinuousOn f I := by
      have cA := z.continuous_amplitude.continuousOn (s:=I)
      have a : ContinuousOn z.along I := fun x hx => (z.normalized_rates x (amp x hx) hd).da.continuousAt.continuousWithinAt
      exact (a.sub continuousOn_const).inf (continuousOn_const.sub cA)
    have s0 : 0<f S := lt_min (by dsimp [S]; linarith) (by dsimp [S]; linarith)
    have step (u : ℝ) (hu : u∈I) (all : ∀x ∈ Icc S u, 0≤f x) (v : ℝ) (hv' : v∈Icc S u) :
        15*z.root v^2/16+(1/1200/3)*(v-S)≤17*z.root S^2/16 ∧ |z.across v| * R v≤C*δ := by
      apply descent hv'.1 _ initJ
      intro x hx
      have xu : x∈Icc S u := ⟨hx.1,hx.2.trans hv'.2⟩
      have xi : x∈I := ⟨hx.1,xu.2.trans hu.2⟩
      have f0 := le_min_iff.mp (all x xu)
      have xx : 0≤x := (by norm_num [S] : (0:ℝ)≤S).trans hx.1
      have cap := (z.centre_bounds hd hk hv hp hq xx).1
      have fr := z.radius_sq x (amp x xi)
      have bd : x≤10000 := xi.2.trans ht.2
      have xx2 := pow_le_pow_left₀ xx bd 2
      have rs : z.root x^2=z.amplitude x := Real.sq_sqrt (amp x xi).le
      refine ⟨z.normalized_rates x (amp x xi) hd,by linarith [f0.2],?_,?_,by linarith [f0.1],?_⟩
      · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
      · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
      · exact (mul_le_mul_of_nonneg_right ((le_max_left ..).trans large) hd.le).trans (above x xi)
    have strict := keep_strict ht.1 cont s0 (fun u hu all => by
      have atU := step u hu all u (right_mem_Icc.mpr hu.1)
      have transverse (x : ℝ) (hx : x∈Icc S u) : |z.across x|≤1/1000000000000 := by
        have xi : x∈I := ⟨hx.1,hx.2.trans hu.2⟩
        have cL := (le_max_right Lmin (1000000000000*C)).trans large
        have pR : 0<R x := (mul_pos Lpos hd).trans_le (above x xi)
        have GR := (mul_le_mul_of_nonneg_right cL hd.le).trans (above x xi)
        exact (le_of_mul_le_mul_right (by linarith [(step u hu all x hx).2]) pR)
      have first := z.radius_during_descent hd hu.1 (fun x hx => by
        have xi : x∈I := ⟨hx.1,hx.2.trans hu.2⟩
        have f0 := (le_min_iff.mp (all x hx)).1
        exact ⟨amp x xi,by linarith,transverse x hx⟩)
      have iS : S∈I := left_mem_Icc.mpr ht.1
      have frS := z.radius_sq S (amp S iS)
      have frU := z.radius_sq u (amp u hu)
      have rS : z.root S^2=z.amplitude S := Real.sq_sqrt (amp S iS).le
      have rU : z.root u^2=z.amplitude u := Real.sq_sqrt (amp u hu).le
      change z.p S^2+z.q S^2 - 2*(1/1000000000000)*(u-S) ≤ z.p u^2+z.q u^2 at first
      have b2 := pow_le_pow_left₀ (abs_nonneg _) (transverse u (right_mem_Icc.mpr hu.1)) 2
      rw [sq_abs] at b2
      have a2 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/288) (show 1/288≤z.along S from initA) 2
      have xpos := (le_min_iff.mp (all u (right_mem_Icc.mpr hu.1))).1
      change 0≤z.along u-1/1200 at xpos
      have ubd := hu.2.trans ht.2
      have sq : (1/1200:ℝ)^2<z.along u^2 := by dsimp [S] at first; dsimp [S] at frS a2; nlinarith [sq_nonneg (z.across S)]
      apply lt_min
      · have a := lt_of_pow_lt_pow_left₀ 2 (by linarith : 0≤z.along u) sq
        linarith
      · have hU : S≤u := hu.1
        have cap : z.amplitude S≤3/2 := Ahi
        have d := atU.1
        rw [rU,rS] at d
        have g : 0≤(1/1200/3:ℝ)*(u-S) := mul_nonneg (by norm_num) (sub_nonneg.mpr hU)
        have left := (le_add_of_nonneg_right g).trans d
        have right : 17*z.amplitude S/16 ≤ 17*(3/2:ℝ)/16 := by gcongr
        have H := left.trans right
        exact sub_pos.mpr (by linarith only [H]))
    intro x hx
    obtain ⟨ha,hb⟩ := lt_min_iff.mp (strict x hx)
    refine ⟨by linarith,by linarith,?_⟩
    exact (step x hx (fun u hu => (strict u ⟨hu.1,hu.2.trans hx.2⟩).le) x (right_mem_Icc.mpr hx.1)).2
  have full : S≤10000 := by norm_num [S]
  have reaches : ∃t∈Icc S 10000, R t≤L*δ := by
    by_contra! no
    have above (x : ℝ) (hx : x∈Icc S 10000) := (no x hx).le
    have stable := protect 10000 (right_mem_Icc.mpr full) above
    have data (x : ℝ) (hx : x∈Icc S 10000) :
        Rates δ x z.root z.shape z.slope z.along z.across ∧ z.root x^2≤2 ∧
        |z.along x|≤10000 ∧ |z.across x|≤10000 ∧ 1/1200≤z.along x ∧ Lmin*δ≤z.root x^3 := by
      obtain ⟨ha,sm,_⟩ := stable x hx
      have rs : z.root x^2=z.amplitude x := Real.sq_sqrt (Real.sqrt_nonneg _)
      have H := (mul_pos Lpos hd).trans (no x hx)
      have rpos : 0<z.root x := by
        by_contra! nr
        have r0 : z.root x=0 := le_antisymm nr (Real.sqrt_nonneg _)
        simp [R,r0] at H
      have Apos : 0<z.amplitude x := rs ▸ sq_pos_of_pos rpos
      have nn : 0≤x := (by norm_num [S] : 0≤S).trans hx.1
      have pq := (z.centre_bounds hd hk hv hp hq nn).1
      have fr := z.radius_sq x Apos
      have cap := pow_le_pow_left₀ nn hx.2 2
      refine ⟨z.normalized_rates x Apos hd,rs.trans_le sm.le,?_,?_,ha.le,?_⟩
      · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
      · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
      · exact (mul_le_mul_of_nonneg_right ((le_max_left ..).trans large) hd.le).trans (above x hx)
    have elapsed := (descent full data initJ).1
    have rS : z.root S^2=z.amplitude S := Real.sq_sqrt (Real.sqrt_nonneg _)
    rw [rS] at elapsed
    dsimp [S] at elapsed
    nlinarith [sq_nonneg (z.root 10000)]
  obtain ⟨t,ht,hlo⟩ := reaches
  obtain ⟨v,hv',eq⟩ := intermediate_value_Icc' ht.1 cR.continuousOn
    (show L*δ∈Icc (R t) (R S) from ⟨hlo,initial.le⟩)
  let zeros := {x ∈ Icc S 10000 | R x=L*δ}
  have compact : IsCompact zeros := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_eq cR.continuousOn continuousOn_const) (fun _ hx => hx.1)
  obtain ⟨u,hu,first⟩ := compact.exists_isMinOn
    (show zeros.Nonempty from ⟨v,⟨hv'.1,hv'.2.trans ht.2⟩,eq⟩) continuous_id.continuousOn
  have above (x : ℝ) (hx : x∈Icc S u) : L*δ≤R x := by
    by_contra! bad
    obtain ⟨y,hy,hit⟩ := intermediate_value_Icc' hx.1 cR.continuousOn
      (show L*δ∈Icc (R x) (R S) from ⟨bad.le,initial.le⟩)
    have uy : u≤y := first (show y∈zeros from ⟨⟨hy.1,(hy.2.trans hx.2).trans hu.1.2⟩,hit⟩)
    exact bad.ne ((le_antisymm hy.2 (hx.2.trans uy)) ▸ hit)
  refine ⟨u,hu.1,hu.2,?_⟩
  intro s hs
  obtain ⟨a,b,c⟩ := protect u hu.1 above s hs
  exact ⟨a,b,above s hs,c⟩

end Data
end ClosedSimilarity.OuterStress

namespace ClosedSimilarity.GlobalSupport
open OuterStress MeasureTheory

/-- The stopping time and transverse budget apply to each actual physical
    centre shot of sufficiently large slope, with unrestricted real b. -/
theorem physical_critical_entry :
    ∃ L₀≥1, ∃ C≥1, ∀ L≥L₀, ∀ b : ℝ, (hb : 32*L≤b) →
      0<b ∧ ∃ T ∈ Icc (1:ℝ) 10000, ∃ p : 0<b,
        let z := centreData b p
        z.root T^3=L/b ∧ 1/1200<z.along T ∧ L*|z.across T|^3 ≤ C^3/L^2 ∧
        b/8 ≤ ∫ t in (0:ℝ)..T, Angle.spin b⁻¹ z.root z.shape z.slope z.along z.across t := by
  obtain ⟨K,k1,C,c1,all⟩ := OuterStress.Data.reaches_critical_layer
  refine ⟨max K 40000,k1.trans (le_max_left ..),C,c1,?_⟩
  intro L large b hb
  have kL := (le_max_left K 40000).trans large
  have cap := (le_max_right K 40000).trans large
  have Lp : 0<L := by linarith
  have bp : 0<b := by linarith
  have b32 : 32≤b := by linarith
  let δ := b⁻¹
  let z := centreData b bp
  have hd : 0<δ := inv_pos.mpr bp
  have tiny : δ≤1/(32*L) := by
    dsimp [δ]; rw [←one_div]
    exact one_div_le_one_div_of_le (by positivity) hb
  have zero : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨T,tm,hit,seg⟩ := all L kL z hd tiny zero.1 zero.2.1 zero.2.2.1 zero.2.2.2
  have Tpos : 0≤T := by linarith [tm.1]
  have T1 : 1≤T := by
    by_contra! bad
    have a := (z.centre_bounds hd zero.1 zero.2.1 zero.2.2.1 zero.2.2.2 Tpos).2
    have sq := pow_le_pow_left₀ Tpos bad.le 2
    have rr : z.root T^2=z.amplitude T := Real.sq_sqrt (Real.sqrt_nonneg _)
    have rlo : 1/2≤z.root T := le_of_sq_le_sq (by nlinarith) (Real.sqrt_nonneg _)
    have c := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rlo 3
    have v := (le_div_iff₀ (by positivity : 0<32*L)).mp tiny
    nlinarith
  have term := seg T (right_mem_Icc.mpr tm.1)
  have cD := term.2.2.2
  rw [hit] at cD
  have frac : |z.across T| ≤ C/L := (le_div_iff₀ Lp).mpr
    (le_of_mul_le_mul_right (by linarith : (|z.across T| * L)*δ≤C*δ) hd)
  have bound := pow_le_pow_left₀ (abs_nonneg _) frac 3
  have qbound : L*|z.across T|^3≤C^3/L^2 := by
    calc _ ≤ L*(C/L)^3 := mul_le_mul_of_nonneg_left bound Lp.le
         _ = _ := by field_simp
  have start := physical_centre_winding b32
  let g := Angle.spin δ z.root z.shape z.slope z.along z.across
  have data (x : ℝ) (hx : x∈Icc (0:ℝ) T) : Rates δ x z.root z.shape z.slope z.along z.across := by
    apply z.normalized_rates x _ hd
    rcases le_total x 1 with h | h
    · have a := (z.centre_bounds hd zero.1 zero.2.1 zero.2.2.1 zero.2.2.2 hx.1).2
      nlinarith [pow_le_pow_left₀ hx.1 h 2]
    · have hl := (seg x ⟨by linarith,hx.2⟩).2.2.1
      have r3 := (mul_pos Lp hd).trans_le hl
      have r : 0<z.root x := lt_of_pow_lt_pow_left₀ 3 (Real.sqrt_nonneg _) (by simpa using r3)
      exact (sq_pos_of_pos r).trans_eq (Real.sq_sqrt (Real.sqrt_nonneg _))
  have integrable : IntervalIntegrable g volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le Tpos]
    exact fun x hx => (Angle.spin_continuousAt (data x hx)).continuousWithinAt
  have nonnegative : 0≤∫ t in (1:ℝ)..T, g t := by
    apply intervalIntegral.integral_nonneg T1
    intro x hx
    have full : x∈Icc (0:ℝ) T := ⟨by linarith [hx.1],hx.2⟩
    have d := data x full
    have h := seg x ⟨by linarith [hx.1],hx.2⟩
    have Apos : 0<z.amplitude x := Real.sqrt_pos.mp d.pos
    have fr := z.radius_sq x Apos
    have pq := (z.centre_bounds hd zero.1 zero.2.1 zero.2.2.1 zero.2.2.2 full.1).1
    have xx := pow_le_pow_left₀ full.1 (hx.2.trans tm.2) 2
    have lo := Angle.spin_lower d (M:=10000)
      (le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]) (by norm_num))
      (le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]) (by norm_num))
      ((mul_le_mul_of_nonneg_right (by linarith : 4*10000≤L) hd.le).trans h.2.2.1)
    exact (div_nonneg d.pos.le (by positivity)).trans lo
  have add := intervalIntegral.integral_add_adjacent_intervals
    (integrable.mono_set (show uIcc 0 1 ⊆ uIcc 0 T by simpa [uIcc_of_le Tpos,uIcc_of_le zero_le_one] using Icc_subset_Icc_right T1))
    (integrable.mono_set (show uIcc 1 T ⊆ uIcc 0 T by simpa [uIcc_of_le Tpos,uIcc_of_le T1] using Icc_subset_Icc_left zero_le_one))
  refine ⟨bp,T,⟨T1,tm.2⟩,bp,by simpa only [div_eq_mul_inv,δ] using hit,term.1,qbound,?_⟩
  have lower : b/8≤∫ t in (0:ℝ)..1, g t := start.2
  linarith

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.physical_critical_entry
