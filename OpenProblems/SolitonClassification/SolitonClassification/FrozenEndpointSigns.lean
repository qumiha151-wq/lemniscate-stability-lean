import SolitonClassification.FrozenStressOrbit

/-! Rational boxes for the four original coordinates imply the precise
    signed corrected-impact margins used in the frozen scattering argument. -/
noncomputable section
namespace ClosedSimilarity.FrozenStress.EndpointSigns
open Set

private theorem linear_box {x c l h L H : ℝ} (xmem : x ∈ Icc l h)
    (lo : c*l ∈ Icc L H) (hi : c*h ∈ Icc L H) : c*x ∈ Icc L H := by
  rcases le_total 0 c with pos | neg
  · exact ⟨lo.1.trans (mul_le_mul_of_nonneg_left xmem.1 pos),
      (mul_le_mul_of_nonneg_left xmem.2 pos).trans hi.2⟩
  · exact ⟨hi.1.trans (mul_le_mul_of_nonpos_left xmem.2 neg),
      (mul_le_mul_of_nonpos_left xmem.1 neg).trans lo.2⟩

private theorem product_box {x y a b c d L H : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ends : a*c ∈ Icc L H ∧ b*c ∈ Icc L H ∧ a*d ∈ Icc L H ∧ b*d ∈ Icc L H) :
    x*y ∈ Icc L H := by
  apply linear_box hy
  · rw [mul_comm]
    apply linear_box hx
    · simpa only [mul_comm c] using ends.1
    · simpa only [mul_comm c] using ends.2.1
  · rw [mul_comm]
    apply linear_box hx
    · simpa only [mul_comm d] using ends.2.2.1
    · simpa only [mul_comm d] using ends.2.2.2

private theorem sum_box {x y a b c d L H : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ends : L ≤ a+c ∧ b+d ≤ H) : x+y ∈ Icc L H :=
  ⟨ends.1.trans (add_le_add hx.1 hy.1),(add_le_add hx.2 hy.2).trans ends.2⟩

private theorem diff_box {x y a b c d L H : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc c d)
    (ends : L ≤ a-d ∧ b-c ≤ H) : x-y ∈ Icc L H :=
  ⟨ends.1.trans (sub_le_sub hx.1 hy.2),(sub_le_sub hx.2 hy.1).trans ends.2⟩

private theorem recip_box {x a b L H : ℝ} (hx : x ∈ Icc a b)
    (ends : 0<a ∧ 0≤L ∧ 0≤H ∧ L*b≤1 ∧ 1≤H*a) : 1/x ∈ Icc L H := by
  have xp := ends.1.trans_le hx.1
  exact ⟨(le_div_iff₀ xp).mpr ((mul_le_mul_of_nonneg_left hx.2 ends.2.1).trans ends.2.2.2.1),
    (div_le_iff₀ xp).mpr (ends.2.2.2.2.trans (mul_le_mul_of_nonneg_left hx.1 ends.2.2.1))⟩

private theorem root_box {x a b L H : ℝ} (hx : x ∈ Icc a b)
    (ends : 0≤a ∧ 0≤H ∧ L^2≤a ∧ b≤H^2) : Real.sqrt x ∈ Icc L H := by
  have sq := Real.sq_sqrt (ends.1.trans hx.1)
  have hp := Real.sqrt_nonneg x
  exact ⟨by nlinarith [ends.2.2.1,hx.1],by nlinarith [ends.2.1,ends.2.2.2,hx.2]⟩

theorem negative_box (z : Orbit) (s : ℝ)
    (hk : z.k s ∈ Icc (3.41349:ℝ) (3.41352))
    (hv : z.v s ∈ Icc (12.12777:ℝ) (12.12781))
    (hp : z.p s ∈ Icc (-0.91168:ℝ) (-0.91164))
    (hq : z.q s ∈ Icc (-0.41097:ℝ) (-0.41093))
    : 13 < -z.radial s ∧ -0.10 < correctedImpact z.root z.shape z.slope z.along z.across s ∧ correctedImpact z.root z.shape z.slope z.along z.across s < -0.09 ∧
      |z.root s * z.across s| < 0.25 := by
  let k := z.k s
  let v := z.v s
  let p := z.p s
  let q := z.q s
  let two := (2:ℝ)
  have htwo : two ∈ Icc (2:ℝ) (2) := ⟨le_rfl,le_rfl⟩
  let six := (6:ℝ)
  have hsix : six ∈ Icc (6:ℝ) (6) := ⟨le_rfl,le_rfl⟩
  let kk := k^2
  have hkk : kk ∈ Icc (11.6519139:ℝ) (11.6521188) := by
    rw [show kk=k*k by exact pow_two k]
    exact product_box hk hk (by norm_num [Set.mem_Icc])
  let invu0 := 1/two
  have hinvu0 : invu0 ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let u0 := kk/two
  have hu0 : u0 ∈ Icc (5.8259569:ℝ) (5.8260594) := by
    rw [show u0=kk*invu0 by exact div_eq_mul_one_div kk two]
    exact product_box hkk hinvu0 (by norm_num [Set.mem_Icc])
  let uu0 := u0^2
  have huu0 : uu0 ∈ Icc (33.9417738:ℝ) (33.9429682) := by
    rw [show uu0=u0*u0 by exact pow_two u0]
    exact product_box hu0 hu0 (by norm_num [Set.mem_Icc])
  let vv := v^2
  have hvv : vv ∈ Icc (147.0828051:ℝ) (147.0837754) := by
    rw [show vv=v*v by exact pow_two v]
    exact product_box hv hv (by norm_num [Set.mem_Icc])
  let squareA := uu0+vv
  have hsquareA : squareA ∈ Icc (181.0245789:ℝ) (181.0267436) := sum_box huu0 hvv (by norm_num)
  let A := Real.sqrt squareA
  have hA : A ∈ Icc (13.4545374:ℝ) (13.454618) := root_box hsquareA (by norm_num)
  let r := Real.sqrt A
  have hr : r ∈ Icc (3.6680427:ℝ) (3.6680538) := root_box hA (by norm_num)
  let uq := u0*q
  have huq : uq ∈ Icc (-2.3943357:ℝ) (-2.3940604) := product_box hu0 hq (by norm_num [Set.mem_Icc])
  let vp := v*p
  have hvp : vp ∈ Icc (-11.0566819:ℝ) (-11.0561602) := product_box hv hp (by norm_num [Set.mem_Icc])
  let rad := uq+vp
  have hrad : rad ∈ Icc (-13.4510176:ℝ) (-13.4502206) := sum_box huq hvp (by norm_num)
  let up := u0*p
  have hup : up ∈ Icc (-5.3115019:ℝ) (-5.3111753) := product_box hu0 hp (by norm_num [Set.mem_Icc])
  let vq := v*q
  have hvq : vq ∈ Icc (-4.9841661:ℝ) (-4.9836645) := product_box hv hq (by norm_num [Set.mem_Icc])
  let trans := up-vq
  have htrans : trans ∈ Icc (-0.3278374:ℝ) (-0.3270092) := diff_box hup hvq (by norm_num)
  let inva := 1/A
  have hinva : inva ∈ Icc (0.0743239:ℝ) (0.0743244) := recip_box hA (by norm_num)
  let a := rad/A
  have ha : a ∈ Icc (-0.9997389:ℝ) (-0.9996728) := by
    rw [show a=rad*inva by exact div_eq_mul_one_div rad A]
    exact product_box hrad hinva (by norm_num [Set.mem_Icc])
  let invb := 1/A
  have hinvb : invb ∈ Icc (0.0743239:ℝ) (0.0743244) := recip_box hA (by norm_num)
  let b := trans/A
  have hb : b ∈ Icc (-0.0243664:ℝ) (-0.0243045) := by
    rw [show b=trans*invb by exact div_eq_mul_one_div trans A]
    exact product_box htrans hinvb (by norm_num [Set.mem_Icc])
  let invshape := 1/r
  have hinvshape : invshape ∈ Icc (0.2726241:ℝ) (0.272625) := recip_box hr (by norm_num)
  let shape := k/r
  have hshape : shape ∈ Icc (0.9305996:ℝ) (0.9306109) := by
    rw [show shape=k*invshape by exact div_eq_mul_one_div k r]
    exact product_box hk hinvshape (by norm_num [Set.mem_Icc])
  let invw := 1/A
  have hinvw : invw ∈ Icc (0.0743239:ℝ) (0.0743244) := recip_box hA (by norm_num)
  let w := v/A
  have hw : w ∈ Icc (0.9013831:ℝ) (0.9013923) := by
    rw [show w=v*invw by exact div_eq_mul_one_div v A]
    exact product_box hv hinvw (by norm_num [Set.mem_Icc])
  let shape2 := shape^2
  have hshape2 : shape2 ∈ Icc (0.8660156:ℝ) (0.8660367) := by
    rw [show shape2=shape*shape by exact pow_two shape]
    exact product_box hshape hshape (by norm_num [Set.mem_Icc])
  let shape3 := shape^3
  have hshape3 : shape3 ∈ Icc (0.8059137:ℝ) (0.8059432) := by
    rw [show shape3=shape2*shape by exact pow_succ shape 2]
    exact product_box hshape2 hshape (by norm_num [Set.mem_Icc])
  let aa := a^2
  have haa : aa ∈ Icc (0.9993457:ℝ) (0.9994779) := by
    rw [show aa=a*a by exact pow_two a]
    exact product_box ha ha (by norm_num [Set.mem_Icc])
  let bb := b^2
  have hbb : bb ∈ Icc (0.0005907:ℝ) (0.0005938) := by
    rw [show bb=b*b by exact pow_two b]
    exact product_box hb hb (by norm_num [Set.mem_Icc])
  let invhalfbb := 1/two
  have hinvhalfbb : invhalfbb ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let halfbb := bb/two
  have hhalfbb : halfbb ∈ Icc (0.0002953:ℝ) (0.0002969) := by
    rw [show halfbb=bb*invhalfbb by exact div_eq_mul_one_div bb two]
    exact product_box hbb hinvhalfbb (by norm_num [Set.mem_Icc])
  let g := aa-halfbb
  have hg : g ∈ Icc (0.9990488:ℝ) (0.9991826) := diff_box haa hhalfbb (by norm_num)
  let cubic := shape3*g
  have hcubic : cubic ∈ Icc (0.8051471:ℝ) (0.8052845) := product_box hshape3 hg (by norm_num [Set.mem_Icc])
  let invtermA := 1/six
  have hinvtermA : invtermA ∈ Icc (0.1666666:ℝ) (0.1666667) := recip_box hsix (by norm_num)
  let termA := cubic/six
  have htermA : termA ∈ Icc (0.1341911:ℝ) (0.1342142) := by
    rw [show termA=cubic*invtermA by exact div_eq_mul_one_div cubic six]
    exact product_box hcubic hinvtermA (by norm_num [Set.mem_Icc])
  let sw := shape*w
  have hsw : sw ∈ Icc (0.8388267:ℝ) (0.8388455) := product_box hshape hw (by norm_num [Set.mem_Icc])
  let swa := sw*a
  have hswa : swa ∈ Icc (-0.8386265:ℝ) (-0.8385522) := product_box hsw ha (by norm_num [Set.mem_Icc])
  let swab := swa*b
  have hswab : swab ∈ Icc (0.0203805:ℝ) (0.0204344) := product_box hswa hb (by norm_num [Set.mem_Icc])
  let invtermB := 1/two
  have hinvtermB : invtermB ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let termB := swab/two
  have htermB : termB ∈ Icc (0.0101902:ℝ) (0.0102172) := by
    rw [show termB=swab*invtermB by exact div_eq_mul_one_div swab two]
    exact product_box hswab hinvtermB (by norm_num [Set.mem_Icc])
  let corr := termA-termB
  have hcorr : corr ∈ Icc (0.1239739:ℝ) (0.124024) := diff_box htermA htermB (by norm_num)
  let raw := r*b
  have hraw : raw ∈ Icc (-0.0893773:ℝ) (-0.0891499) := product_box hr hb (by norm_num [Set.mem_Icc])
  let r2 := r^2
  have hr2 : r2 ∈ Icc (13.4545372:ℝ) (13.4546187) := by
    rw [show r2=r*r by exact pow_two r]
    exact product_box hr hr (by norm_num [Set.mem_Icc])
  let invscaledCorr := 1/r2
  have hinvscaledCorr : invscaledCorr ∈ Icc (0.0743239:ℝ) (0.0743244) := recip_box hr2 (by norm_num)
  let scaledCorr := corr/r2
  have hscaledCorr : scaledCorr ∈ Icc (0.0092142:ℝ) (0.0092181) := by
    rw [show scaledCorr=corr*invscaledCorr by exact div_eq_mul_one_div corr r2]
    exact product_box hcorr hinvscaledCorr (by norm_num [Set.mem_Icc])
  let value := raw-scaledCorr
  have hvalue : value ∈ Icc (-0.0985954:ℝ) (-0.0983641) := diff_box hraw hscaledCorr (by norm_num)
  have E : correctedImpact z.root z.shape z.slope z.along z.across s = value := rfl
  have R : z.radial s = rad := rfl
  have I : z.root s * z.across s = raw := rfl
  rw [E,R,I,abs_lt]
  exact ⟨by linarith [hrad.2],by linarith [hvalue.1],by linarith [hvalue.2],by linarith [hraw.1],by linarith [hraw.2]⟩

theorem positive_box (z : Orbit) (s : ℝ)
    (hk : z.k s ∈ Icc (-2.8735:ℝ) (-2.87346))
    (hv : z.v s ∈ Icc (12.04546:ℝ) (12.0455))
    (hp : z.p s ∈ Icc (-0.83545:ℝ) (-0.83541))
    (hq : z.q s ∈ Icc (-0.54962:ℝ) (-0.54958))
    : 12 < -z.radial s ∧ 0.8 < correctedImpact z.root z.shape z.slope z.along z.across s := by
  let k := z.k s
  let v := z.v s
  let p := z.p s
  let q := z.q s
  let two := (2:ℝ)
  have htwo : two ∈ Icc (2:ℝ) (2) := ⟨le_rfl,le_rfl⟩
  let six := (6:ℝ)
  have hsix : six ∈ Icc (6:ℝ) (6) := ⟨le_rfl,le_rfl⟩
  let kk := k^2
  have hkk : kk ∈ Icc (8.2567723:ℝ) (8.2570023) := by
    rw [show kk=k*k by exact pow_two k]
    exact product_box hk hk (by norm_num [Set.mem_Icc])
  let invu0 := 1/two
  have hinvu0 : invu0 ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let u0 := kk/two
  have hu0 : u0 ∈ Icc (4.1283861:ℝ) (4.1285012) := by
    rw [show u0=kk*invu0 by exact div_eq_mul_one_div kk two]
    exact product_box hkk hinvu0 (by norm_num [Set.mem_Icc])
  let uu0 := u0^2
  have huu0 : uu0 ∈ Icc (17.0435717:ℝ) (17.0445222) := by
    rw [show uu0=u0*u0 by exact pow_two u0]
    exact product_box hu0 hu0 (by norm_num [Set.mem_Icc])
  let vv := v^2
  have hvv : vv ∈ Icc (145.0931066:ℝ) (145.0940703) := by
    rw [show vv=v*v by exact pow_two v]
    exact product_box hv hv (by norm_num [Set.mem_Icc])
  let squareA := uu0+vv
  have hsquareA : squareA ∈ Icc (162.1366783:ℝ) (162.1385925) := sum_box huu0 hvv (by norm_num)
  let A := Real.sqrt squareA
  have hA : A ∈ Icc (12.7332901:ℝ) (12.7333654) := root_box hsquareA (by norm_num)
  let r := Real.sqrt A
  have hr : r ∈ Icc (3.5683735:ℝ) (3.5683842) := root_box hA (by norm_num)
  let uq := u0*q
  have huq : uq ∈ Icc (-2.2691069:ℝ) (-2.2688784) := product_box hu0 hq (by norm_num [Set.mem_Icc])
  let vp := v*p
  have hvp : vp ∈ Icc (-10.063413:ℝ) (-10.0628977) := product_box hv hp (by norm_num [Set.mem_Icc])
  let rad := uq+vp
  have hrad : rad ∈ Icc (-12.3325199:ℝ) (-12.3317761) := sum_box huq hvp (by norm_num)
  let up := u0*p
  have hup : up ∈ Icc (-3.4491564:ℝ) (-3.448895) := product_box hu0 hp (by norm_num [Set.mem_Icc])
  let vq := v*q
  have hvq : vq ∈ Icc (-6.6204478:ℝ) (-6.6199439) := product_box hv hq (by norm_num [Set.mem_Icc])
  let trans := up-vq
  have htrans : trans ∈ Icc (3.1707875:ℝ) (3.1715528) := diff_box hup hvq (by norm_num)
  let inva := 1/A
  have hinva : inva ∈ Icc (0.0785338:ℝ) (0.0785343) := recip_box hA (by norm_num)
  let a := rad/A
  have ha : a ∈ Icc (-0.9685259:ℝ) (-0.9684612) := by
    rw [show a=rad*inva by exact div_eq_mul_one_div rad A]
    exact product_box hrad hinva (by norm_num [Set.mem_Icc])
  let invb := 1/A
  have hinvb : invb ∈ Icc (0.0785338:ℝ) (0.0785343) := recip_box hA (by norm_num)
  let b := trans/A
  have hb : b ∈ Icc (0.2490139:ℝ) (0.2490757) := by
    rw [show b=trans*invb by exact div_eq_mul_one_div trans A]
    exact product_box htrans hinvb (by norm_num [Set.mem_Icc])
  let invshape := 1/r
  have hinvshape : invshape ∈ Icc (0.2802388:ℝ) (0.2802398) := recip_box hr (by norm_num)
  let shape := k/r
  have hshape : shape ∈ Icc (-0.8052691:ℝ) (-0.8052549) := by
    rw [show shape=k*invshape by exact div_eq_mul_one_div k r]
    exact product_box hk hinvshape (by norm_num [Set.mem_Icc])
  let invw := 1/A
  have hinvw : invw ∈ Icc (0.0785338:ℝ) (0.0785343) := recip_box hA (by norm_num)
  let w := v/A
  have hw : w ∈ Icc (0.9459757:ℝ) (0.945985) := by
    rw [show w=v*invw by exact div_eq_mul_one_div v A]
    exact product_box hv hinvw (by norm_num [Set.mem_Icc])
  let shape2 := shape^2
  have hshape2 : shape2 ∈ Icc (0.6484354:ℝ) (0.6484584) := by
    rw [show shape2=shape*shape by exact pow_two shape]
    exact product_box hshape hshape (by norm_num [Set.mem_Icc])
  let shape3 := shape^3
  have hshape3 : shape3 ∈ Icc (-0.5221836:ℝ) (-0.5221557) := by
    rw [show shape3=shape2*shape by exact pow_succ shape 2]
    exact product_box hshape2 hshape (by norm_num [Set.mem_Icc])
  let aa := a^2
  have haa : aa ∈ Icc (0.937917:ℝ) (0.9380425) := by
    rw [show aa=a*a by exact pow_two a]
    exact product_box ha ha (by norm_num [Set.mem_Icc])
  let bb := b^2
  have hbb : bb ∈ Icc (0.0620079:ℝ) (0.0620388) := by
    rw [show bb=b*b by exact pow_two b]
    exact product_box hb hb (by norm_num [Set.mem_Icc])
  let invhalfbb := 1/two
  have hinvhalfbb : invhalfbb ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let halfbb := bb/two
  have hhalfbb : halfbb ∈ Icc (0.0310039:ℝ) (0.0310194) := by
    rw [show halfbb=bb*invhalfbb by exact div_eq_mul_one_div bb two]
    exact product_box hbb hinvhalfbb (by norm_num [Set.mem_Icc])
  let g := aa-halfbb
  have hg : g ∈ Icc (0.9068976:ℝ) (0.9070386) := diff_box haa hhalfbb (by norm_num)
  let cubic := shape3*g
  have hcubic : cubic ∈ Icc (-0.4736407:ℝ) (-0.4735417) := product_box hshape3 hg (by norm_num [Set.mem_Icc])
  let invtermA := 1/six
  have hinvtermA : invtermA ∈ Icc (0.1666666:ℝ) (0.1666667) := recip_box hsix (by norm_num)
  let termA := cubic/six
  have htermA : termA ∈ Icc (-0.0789402:ℝ) (-0.0789235) := by
    rw [show termA=cubic*invtermA by exact div_eq_mul_one_div cubic six]
    exact product_box hcubic hinvtermA (by norm_num [Set.mem_Icc])
  let sw := shape*w
  have hsw : sw ∈ Icc (-0.7617725:ℝ) (-0.7617515) := product_box hshape hw (by norm_num [Set.mem_Icc])
  let swa := sw*a
  have hswa : swa ∈ Icc (0.7377267:ℝ) (0.7377964) := product_box hsw ha (by norm_num [Set.mem_Icc])
  let swab := swa*b
  have hswab : swab ∈ Icc (0.1837042:ℝ) (0.1837672) := product_box hswa hb (by norm_num [Set.mem_Icc])
  let invtermB := 1/two
  have hinvtermB : invtermB ∈ Icc (0.5:ℝ) (0.5) := recip_box htwo (by norm_num)
  let termB := swab/two
  have htermB : termB ∈ Icc (0.0918521:ℝ) (0.0918836) := by
    rw [show termB=swab*invtermB by exact div_eq_mul_one_div swab two]
    exact product_box hswab hinvtermB (by norm_num [Set.mem_Icc])
  let corr := termA-termB
  have hcorr : corr ∈ Icc (-0.1708238:ℝ) (-0.1707756) := diff_box htermA htermB (by norm_num)
  let raw := r*b
  have hraw : raw ∈ Icc (0.8885746:ℝ) (0.8887978) := product_box hr hb (by norm_num [Set.mem_Icc])
  let r2 := r^2
  have hr2 : r2 ∈ Icc (12.7332894:ℝ) (12.7333658) := by
    rw [show r2=r*r by exact pow_two r]
    exact product_box hr hr (by norm_num [Set.mem_Icc])
  let invscaledCorr := 1/r2
  have hinvscaledCorr : invscaledCorr ∈ Icc (0.0785338:ℝ) (0.0785344) := recip_box hr2 (by norm_num)
  let scaledCorr := corr/r2
  have hscaledCorr : scaledCorr ∈ Icc (-0.0134156:ℝ) (-0.0134116) := by
    rw [show scaledCorr=corr*invscaledCorr by exact div_eq_mul_one_div corr r2]
    exact product_box hcorr hinvscaledCorr (by norm_num [Set.mem_Icc])
  let value := raw-scaledCorr
  have hvalue : value ∈ Icc (0.9019862:ℝ) (0.9022134) := diff_box hraw hscaledCorr (by norm_num)
  have E : correctedImpact z.root z.shape z.slope z.along z.across s = value := rfl
  have R : z.radial s = rad := rfl
  rw [E,R]
  exact ⟨by linarith [hrad.2],by linarith [hvalue.1]⟩

end ClosedSimilarity.FrozenStress.EndpointSigns
#print axioms ClosedSimilarity.FrozenStress.EndpointSigns.negative_box
#print axioms ClosedSimilarity.FrozenStress.EndpointSigns.positive_box
