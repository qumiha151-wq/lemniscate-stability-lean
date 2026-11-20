import SolitonClassification.CentreCriticalLayer
import SolitonClassification.OuterIncomingSection

noncomputable section
set_option maxHeartbeats 2000000
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set OuterStress

def centreAt (b t : ℝ) : Phase := solution 1 ![0,b,0,0] (t/Real.sqrt b⁻¹)

/-- From the centre data alone, every sufficiently late shot crosses a fixed
    high incoming section. On the entire approach the physical radius stays
    large and the stress direction stays aligned. All crossings have impact
    bounded by K/H, with K independent of H and of the marker b. -/
theorem physical_centre_incoming_crossing :
    ∃ K>0, ∃ H₀≥2, ∀ H≥H₀, ∃ B>0, ∀ b≥B, ∃ T∈Icc (1:ℝ) 10000,
      (H < -height (centreAt b 1) ∧ -height (centreAt b T) < H) ∧
      (∃ t∈Icc (1:ℝ) T, -height (centreAt b t)=H) ∧
      ∀ t∈Icc (1:ℝ) T,
        regular (centreAt b t) ∧ 1 ≤ innerRoot (centreAt b t) ∧
        1/12000000 ≤ along (centreAt b t) ∧
        (1/scale (centreAt b t)^4)^3 ≤ 1200^4*(b⁻¹)^2 ∧
        (-height (centreAt b t)=H → |impact (centreAt b t)| ≤ K/H) := by
  obtain ⟨L₀,hL₀,C,hC,enter⟩ := OuterStress.Data.reaches_critical_layer
  let L := max L₀ 40000
  have large : L₀≤L := le_max_left .. 
  have capL : 40000≤L := le_max_right ..
  have lp : 0<L := by linarith
  let N := 1200*L
  have np : 1≤N := by dsimp [N]; linarith
  refine ⟨2*C*1200^2,by positivity, N^2+3,by linarith [sq_nonneg N],?_⟩
  intro H hH
  have Hbig : 2≤H := by linarith [sq_nonneg N]
  let G := 12000000*(H+3)
  have gp : 1≤G := by dsimp [G]; linarith
  let B := max (32*L) (80000*G^3)
  refine ⟨B,lt_of_lt_of_le (by positivity : 0<32*L) (le_max_left ..),?_⟩
  intro b big
  have bL := (le_max_left (32*L) (80000*G^3)).trans big
  have bG := (le_max_right (32*L) (80000*G^3)).trans big
  have bp : 0<b := by linarith
  let δ := b⁻¹
  have dp : 0<δ := inv_pos.mpr bp
  let z := centreData b bp
  let x := centreAt b
  have dz := solution_derivative 1 (![0,b,0,0] : Phase)
  have tiny : δ≤1/(32*L) := by
    dsimp [δ]; rw [←one_div]; exact one_div_le_one_div_of_le (by positivity) bL
  have inits : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  have bound {t : ℝ} (ht : 0≤t) := z.centre_bounds dp inits.1 inits.2.1 inits.2.2.1 inits.2.2.2 ht
  obtain ⟨T,hT,endval,seg⟩ := enter L large z dp tiny inits.1 inits.2.1 inits.2.2.1 inits.2.2.2
  have rootSq (t : ℝ) : z.root t^2=z.amplitude t := Real.sq_sqrt (Real.sqrt_nonneg _)
  have one : 1≤T := by
    by_contra! bad
    have tp : 0≤T := by linarith [hT.1]
    have ba := (bound tp).2
    have sq := pow_le_pow_left₀ tp bad.le 2
    have r : 1/2≤z.root T := le_of_sq_le_sq (by nlinarith [rootSq T]) (Real.sqrt_nonneg _)
    have hi := (le_div_iff₀ (by positivity : 0<32*L)).mp tiny
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) r 3]
  have rd (t : ℝ) (ht : t∈Icc (1:ℝ) T) :
      regular (x t) ∧ 1 ≤ innerRoot (x t) ∧ 1/1200≤outerRadius δ (x t) ∧
      outerRadius δ (x t)≤10000 ∧ 1/12000000≤along (x t) ∧
      innerRoot (x t)^3 * outerRadius δ (x t)*δ=z.root t^3 ∧
      |impact (x t)| * (innerRoot (x t))^2*(outerRadius δ (x t))^2≤C ∧
      (1/scale (x t)^4)^3 ≤ 1200^4*δ^2 := by
    have st := seg t ⟨by linarith [ht.1],ht.2⟩
    have reg : regular (x t) := regular_of_outer_along dp _ dz (by change 0<z.along t; linarith [st.1])
    obtain ⟨_,_,_,al,_,cube,impactEq,epsEq⟩ := outer_chart dp _ dz t reg
    change z.along t=along (x t)*outerRadius δ (x t) at al
    change innerRoot (x t)^3*outerRadius δ (x t)*δ=z.root t^3 at cube
    change impact (x t)*innerRoot (x t)^2*outerRadius δ (x t)^2*δ=z.across t*z.root t^3 at impactEq
    change (1/scale (x t)^4)^3*outerRadius δ (x t)^4=δ^2 at epsEq
    have rp : 0<outerRadius δ (x t) := mul_pos (Real.sqrt_pos.mpr dp) (pow_pos (Real.rpow_pos_of_pos reg.1 _) _)
    have npos : 0 ≤ innerRoot (x t) := div_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos reg.1 _).le
    have rad := radius_identity dp _ dz t
    change outerRadius δ (x t)^2=z.p t^2+z.q t^2 at rad
    have pq := (bound (by linarith [ht.1] : 0≤t)).1
    have high : outerRadius δ (x t)≤10000 := by
      apply le_of_sq_le_sq _ (by norm_num)
      linarith [pow_le_pow_left₀ (by linarith [ht.1] : 0≤t) (ht.2.trans hT.2) 2]
    have un := (unit_chart _ reg).2
    have ca : along (x t)≤1 := by nlinarith [sq_nonneg (across (x t)),sq_nonneg (along (x t)-1)]
    have lower : 1/1200≤outerRadius δ (x t) := by
      linarith [mul_le_mul_of_nonneg_right ca rp.le,st.1]
    have align : 1/12000000≤along (x t) := by
      apply le_of_mul_le_mul_right (show (1/12000000:ℝ)*outerRadius δ (x t) ≤ along (x t)*outerRadius δ (x t) from ?_) rp
      rw [←al]; linarith [st.1]
    have r3 := (le_of_mul_le_mul_right (st.2.2.1.trans_eq cube.symm) dp)
    have far : 1 ≤ innerRoot (x t) := by
      by_contra! hn
      have hh := pow_le_pow_left₀ npos hn.le 3
      norm_num at hh
      linarith [mul_le_mul_of_nonneg_right hh rp.le]
    have mag := congrArg abs impactEq
    simp only [abs_mul,abs_of_nonneg (sq_nonneg (innerRoot (x t))),
      abs_of_nonneg (sq_nonneg (outerRadius δ (x t))),abs_of_pos dp,
      abs_of_nonneg (pow_nonneg (show 0≤z.root t from Real.sqrt_nonneg _) 3)] at mag
    have outer := le_of_mul_le_mul_right (mag.trans_le st.2.2.2) dp
    have ep : 0≤(1/scale (x t)^4)^3 := by positivity
    have pow := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/1200) lower 4
    have eps := mul_le_mul_of_nonneg_left pow ep
    rw [epsEq] at eps
    exact ⟨reg,far,lower,high,align,cube,outer,by norm_num at eps ⊢; linarith⟩
  have a := rd 1 (left_mem_Icc.mpr one)
  have e := rd T (right_mem_Icc.mpr one)
  have r1 : 1/2≤z.root 1 := le_of_sq_le_sq (by nlinarith [(bound (by norm_num : (0:ℝ)≤1)).2,rootSq 1]) (Real.sqrt_nonneg _)
  have first : G ≤ innerRoot (x 1) := by
    have cc := a.2.2.2.2.2.1
    have b8 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) r1 3
    have d : δ*b=1 := inv_mul_cancel₀ bp.ne'
    have dx := congrArg (fun v : ℝ => v*b) cc
    change innerRoot (x 1)^3*outerRadius δ (x 1)*δ*b = z.root 1^3*b at dx
    rw [mul_assoc (innerRoot (x 1)^3 * outerRadius δ (x 1)),d,mul_one] at dx
    have q := mul_le_mul_of_nonneg_right b8 bp.le
    have cap := mul_le_mul_of_nonneg_left a.2.2.2.1 (pow_nonneg (by linarith [a.2.1] : 0 ≤ innerRoot (x 1)) 3)
    by_contra! bad
    have low := pow_lt_pow_left₀ bad (by linarith only [a.2.1] : 0 ≤ innerRoot (x 1)) (by decide : 3≠0)
    nlinarith only [dx,q,bG,cap,low]
  have endN : innerRoot (x T)≤N := by
    have cs := e.2.2.2.2.2.1.trans endval
    have eq := mul_right_cancel₀ dp.ne' cs
    have cap := mul_le_mul_of_nonneg_left e.2.2.1 (pow_nonneg (by linarith [e.2.1] : 0 ≤ innerRoot (x T)) 3)
    have nc : innerRoot (x T) ≤ innerRoot (x T)^3 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr e.2.1)
        (by nlinarith [e.2.1,sq_nonneg (innerRoot (x T))] : 0 ≤ innerRoot (x T)^2+innerRoot (x T))]
    dsimp [N]; linarith
  have top : H+2 ≤ innerRoot (x 1)^2*along (x 1) := by
    have c := mul_le_mul_of_nonneg_left a.2.2.2.2.1 (sq_nonneg (innerRoot (x 1)))
    have n := a.2.1
    dsimp [G] at first
    nlinarith only [c,first,mul_nonneg (by linarith : 0 ≤ innerRoot (x 1)-1) (by linarith : 0 ≤ innerRoot (x 1))]
  have bottom : innerRoot (x T)^2+2≤H := by
    linarith [pow_le_pow_left₀ (by linarith [e.2.1]) endN 2]
  have cont : Continuous x := by
    have time : Continuous (fun t : ℝ => ((t/Real.sqrt b⁻¹,(1,(![0,b,0,0]:Phase))) : ℝ × GlobalSupport.Data)) :=
      (continuous_id.div_const _).prodMk continuous_const
    exact continuous_solution.comp time
  obtain ⟨t,ht,hit⟩ := crossing_on_strip one cont.continuousOn (fun u hu => ⟨(rd u hu).1,(rd u hu).2.1⟩)
    (by linarith : H+1 ≤ _) (by linarith : _+1≤H)
  have ea := (abs_le.mp (height_error a.1 a.2.1)).1
  have ee := (abs_le.mp (height_error e.1 e.2.1)).2
  have un := (unit_chart _ e.1).2
  have al : along (x T)≤1 := by nlinarith [sq_nonneg (across (x T)),sq_nonneg (along (x T)-1)]
  refine ⟨T,⟨one,hT.2⟩,⟨by linarith,by linarith [mul_le_mul_of_nonneg_left al (sq_nonneg (innerRoot (x T)))]⟩,
    ⟨t,ht,hit⟩,?_⟩
  intro t ht
  have h := rd t ht
  refine ⟨h.1,h.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.2,fun level => ?_⟩
  have final := impact_at_level h.1 h.2.1 (by norm_num : 0<(1/1200:ℝ)) h.2.2.1 Hbig level h.2.2.2.2.2.2.1
  convert final using 1; ring

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.physical_centre_incoming_crossing
