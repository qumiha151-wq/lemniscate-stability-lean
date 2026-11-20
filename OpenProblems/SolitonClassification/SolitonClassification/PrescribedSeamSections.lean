import SolitonClassification.MovingSeamLipschitz
import SolitonClassification.MovingSeamPhysical
import SolitonClassification.ContinuousPhysicalRadius

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam

/-- Family of returned seam shots at one corrected height, indexed by
    curvature and by the actual incoming value of the inverse radius. -/
structure PrescribedSection (a b H E : ℝ) where
  drive : Icc a b × Icc (0:ℝ) E → ℝ
  flight : Icc a b × Icc (0:ℝ) E → ℝ
  continuous_drive : Continuous drive
  continuous_flight : Continuous flight
  late : ∀x, 20<flight x
  frozen : ∀x : Icc a b × Icc (0:ℝ) E, (x.2:ℝ)=0 → drive x=0
  parameter : ∀x : Icc a b × Icc (0:ℝ) E,
    drive x * radiusFactor x.1 (drive x) (-flight x) = x.2
  incoming : ∀x : Icc a b × Icc (0:ℝ) E, -height (shot (drive x) x.1 (-flight x))=H
  regular_incoming : ∀x : Icc a b × Icc (0:ℝ) E, regular (shot (drive x) x.1 (-flight x))
  continuous_impact : Continuous (fun x : Icc a b × Icc (0:ℝ) E => impact (shot (drive x) x.1 (-flight x)))
  physical : ∀x : Icc a b × Icc (0:ℝ) E, 0<(x.2:ℝ) → ∃l>0, l^4*drive x=1 ∧
    let f := solution 1 (restore l ![(x.1:ℝ),0,1,0])
    ReflectedArc.RadialLayer.eps f (-flight x/l)=x.2 ∧ -height (f (-flight x/l))=H ∧
    impact (f (-flight x/l))=impact (shot (drive x) x.1 (-flight x))

theorem prescribed_seam_sections (a b : ℝ) :
    ∃H₀, ∀H≥H₀, ∃ E>0, Nonempty (PrescribedSection a b H E) := by
  classical
  obtain ⟨S,hS,H₀,w⟩ := moving_seam_time a b
  refine ⟨H₀,?_⟩
  intro H hH
  obtain ⟨T,st,D,hD,K,hK,τ,cτ,hit,lip,safe⟩ := w H hH
  have tp : 0<T := by linarith
  let D' := min D (1/(2*(1+T)))
  have dp : 0<D' := lt_min hD (by positivity)
  have dsmall : D'*T ≤ 1/2 := by
    have lim : D'≤1/(2*(1+T)) := min_le_right .. 
    have le := (le_div_iff₀ (by positivity : 0<2*(1+T))).mp lim
    nlinarith only [le,dp]
  have shrink {r : ℝ} (hr : r∈Icc (0:ℝ) D') : r∈Icc (0:ℝ) D := ⟨hr.1,hr.2.trans (min_le_left ..)⟩
  let time := fun c d : ℝ => if hc : c∈Icc a b then
    if hd : d∈Icc (0:ℝ) D then -τ (⟨c,hc⟩,⟨d,hd⟩) else 0 else 0
  have atTime (c : Icc a b) (d : Icc (0:ℝ) D) : time c d = -τ (c,d) := by
    dsimp only [time]
    rw [dif_pos c.property,dif_pos d.property]
  let liftD := fun r : Icc (0:ℝ) D' => (⟨r,shrink r.property⟩ : Icc (0:ℝ) D)
  have ctime : Continuous (fun z : Icc a b × Icc (0:ℝ) D' => time z.1 z.2) := by
    have cf : Continuous liftD := continuous_subtype_val.subtype_mk _
    exact (cτ.neg.comp (continuous_fst.prodMk (cf.comp continuous_snd))).congr
      (fun z => (atTime z.1 (liftD z.2)).symm)
  have bounded (c : ℝ) (hc : c∈Icc a b) (r : ℝ) (hr : r∈Icc (0:ℝ) D') : |time c r|≤T := by
    let x : Icc a b × Icc (0:ℝ) D := (⟨c,hc⟩,⟨r,shrink hr⟩)
    rw [show time c r = -τ x from atTime x.1 x.2,abs_neg,abs_of_nonneg (by linarith [(hit x).1.1])]
    exact (hit x).1.2.le
  have times (c : ℝ) (hc : c∈Icc a b) (p : ℝ) (hp : p∈Icc (0:ℝ) D')
      (q : ℝ) (hq : q∈Icc (0:ℝ) D') : |time c p-time c q|≤K*|p-q| := by
    let c' : Icc a b := ⟨c,hc⟩
    let p' : Icc (0:ℝ) D := ⟨p,shrink hp⟩
    let q' : Icc (0:ℝ) D := ⟨q,shrink hq⟩
    rw [show time c p= -τ (c',p') from atTime c' p', show time c q= -τ (c',q') from atTime c' q',neg_sub_neg,abs_sub_comm]
    exact lip c' p' q'
  obtain ⟨B,⟨bPos,bLe⟩,g,cg,data⟩ :=
    continuous_prescribed_seam_scales (C:=Icc a b) isCompact_Icc dp tp.le hK dsmall time ctime bounded times
  let E := B*(1/4)
  let X := Icc a b × Icc (0:ℝ) E
  let j := fun z : X => (⟨g z,shrink ⟨(data z).1.1,(data z).1.2.trans bLe⟩⟩ : Icc (0:ℝ) D)
  let x := fun z : X => (z.1,j z)
  have cj : Continuous j := cg.subtype_mk _
  have cx : Continuous x := continuous_fst.prodMk cj
  let F := fun z : X => τ (x z)
  have fc : Continuous F := cτ.comp cx
  have tim (z : X) : time z.1 (g z)= -F z := atTime z.1 (j z)
  have hF (z : X) : height (shot (g z) z.1 (F z)) = H := (hit (x z)).2.1
  have eqI (z : X) : impact (shot (g z) z.1 (-F z)) = impact (shot (g z) z.1 (F z)) :=
    (negative_section _ _ _ _ (hF z)).2.1
  have cs : Continuous (fun z : X => shot (g z) z.1 (F z)) :=
    continuous_shot cg (continuous_subtype_val.comp continuous_fst) fc
  have ci : Continuous (fun z : X => impact (shot (g z) z.1 (F z))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ContinuousAt.comp (f:=fun y : X => shot (g y) y.1 (F y)) (x:=z)
      (impact_continuousAt (safe (x z) _ (Ioo_subset_Icc_self (hit (x z)).1)).1) cs.continuousAt
  refine ⟨E,by dsimp [E]; positivity,⟨⟨g,F,cg,fc,fun z => hS.trans_lt (hit (x z)).1.1,?_,?_,
    fun z => (negative_section _ _ _ _ (hF z)).1,?_,ci.congr (fun z => (eqI z).symm),?_⟩⟩⟩
  · intro z hz
    exact ((data z).2.2.1 0 ⟨le_rfl,bPos.le⟩ (by simp [hz])).symm
  · intro z
    simpa only [tim] using (data z).2.1
  · intro z
    have reg := (safe (x z) _ (Ioo_subset_Icc_self (hit (x z)).1)).1
    rw [shot_reflection]
    simpa [regular,radiusSquared,stressSquared,reverse] using reg
  · intro z hp
    obtain ⟨l,hl,eq,eps⟩ := (data z).2.2.2 hp
    rw [tim] at eps
    obtain ⟨heightEq,impEq,_⟩ := physical_incoming_crossing hl eq (hF z)
    exact ⟨l,hl,eq,eps,heightEq,impEq.trans (eqI z).symm⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.prescribed_seam_sections
