import SolitonClassification.Rotating.IntegerFinalPhysicalEvolution
import SolitonClassification.Rotating.IntegerCrossingArcs

namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric DyadicReset
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000


private theorem reconstruct_trace {T : ℝ} (hT : 0<T) (z : ℝ→State)
    (hd : ∀s∈Icc (-T) T, HasDerivAt z (field (z s)) s)
    (hm : z T=z (-T)+angleVector (-2*Real.pi)) :
    ∃ I : WindingOneImmersion (z 0 4) (2*T), I.k 0=z 0 0 ∧
      I.x 0*deriv I.x 0+I.y 0*deriv I.y 0=z 0 3 ∧
      ∀s∈Icc (-T) T, (I.x s,I.y s)=framePosition (z s) ∧ I.k s=z s 0 ∧ I.theta s=z s 5 := by
  obtain ⟨Z,hZ,dZ,agrees,hol⟩ := extend_matched_segment hT z hd hm
  have hz : Z 0=z 0 := agrees 0 ⟨by linarith, hT.le⟩
  have dz (i : Fin 6) (s : ℝ) : HasDerivAt (fun u => Z u i) (field (Z s) i) s := by
    exact ((ContinuousLinearMap.proj i : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (dZ s))
  have cb (s : ℝ) : Z s 4=z 0 4 := by
    have df (u : ℝ) : HasDerivAt (fun t => Z t 4) 0 u := dz 4 u
    have eq := is_const_of_deriv_eq_zero (fun u => (df u).differentiableAt) (fun u => (df u).deriv) s 0
    simpa only [hz] using eq
  let k := fun s => Z s 0
  let v := fun s => 8*Z s 1
  let p := fun s => Z s 2
  let q := fun s => Z s 3
  let th := fun s => Z s 5
  let x := ClosedSimilarity.profileX p q th
  let y := ClosedSimilarity.profileY p q th
  have dk (s : ℝ) : HasDerivAt k (v s) s := dz 0 s
  have dv (s : ℝ) : HasDerivAt v (-(k s)^3/2-p s-z 0 4*q s) s := by
    convert! (dz 1 s).const_mul 8 using 1
    dsimp [field,k,p,q]
    rw [cb]
    ring
  have dp (s : ℝ) : HasDerivAt p (-k s*q s) s := dz 2 s
  have dq (s : ℝ) : HasDerivAt q (1+k s*p s) s := dz 3 s
  have dt (s : ℝ) : HasDerivAt th (k s) s := dz 5 s
  have per (i : Fin 6) (hi : i≠5) : Function.Periodic (fun s => Z s i) (2*T) := by
    intro s
    simpa [angleVector,hi] using congrFun (hol s) i
  have ht (s : ℝ) : th (s+2*T)=th s-2*Real.pi := by
    have h := congrFun (hol s) 5
    simpa [th,angleVector,sub_eq_add_neg] using h
  obtain ⟨px,py⟩ := ClosedSimilarity.profile_periodic p q th (2*T) (-1)
    (per 2 (by decide)) (per 3 (by decide)) (fun s => by simpa [sub_eq_add_neg] using ht s)
  have cs (i : Fin 6) : ContDiff ℝ (⊤ : ℕ∞) (fun s => Z s i) :=
    (contDiff_apply ℝ ℝ i).comp hZ
  have sp : ContDiff ℝ (⊤ : ℕ∞) p := cs 2
  have sq : ContDiff ℝ (⊤ : ℕ∞) q := cs 3
  have st : ContDiff ℝ (⊤ : ℕ∞) th := cs 5
  have dx (s : ℝ) : HasDerivAt x (Real.cos (th s)) s :=
    ClosedSimilarity.profileX_hasDerivAt k p q th s (dp s) (dq s) (dt s)
  have dy (s : ℝ) : HasDerivAt y (Real.sin (th s)) s :=
    ClosedSimilarity.profileY_hasDerivAt k p q th s (dp s) (dq s) (dt s)
  refine ⟨⟨x,y,k,th,(sq.mul st.cos).sub (sp.mul st.sin),(sq.mul st.sin).add (sp.mul st.cos),
    px,py,dt,ht,dx,dy,?_,?_,?_⟩,congrFun hz 0,?_,?_⟩
  · exact fun s => ClosedSimilarity.profile_unit_speed k p q th s (dp s) (dq s) (dt s)
  · exact ClosedSimilarity.profile_signed_curvature k p q th dp dq dt
  · intro s
    rw [(dx s).deriv,(dy s).deriv]
    exact ClosedSimilarity.profile_soliton_equation _ k v p q th dk dv s
  · change x 0*deriv x 0+y 0*deriv y 0=z 0 3
    rw [(dx 0).deriv,(dy 0).deriv]
    exact (ClosedSimilarity.tangent_support p q th 0).trans (congrFun hz 3)

  · intro s hs
    change framePosition (Z s)=framePosition (z s) ∧ Z s 0=z s 0 ∧ Z s 5=z s 5
    rw [agrees s hs]
    exact ⟨rfl,rfl,rfl⟩

set_option backward.isDefEq.respectTransparency false

private theorem retained_cube_parameters {c : Parameters} (hc : c∈cube) :
    30<c 2 ∧ c 2<31 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<c 0 ∧ 0<c 3 := by
  have hn : ‖c-center‖≤1/(10:ℝ)^30 := hc
  have he (i : Fin 5) : |c i-(centerQ i:ℝ)|≤1/(10:ℝ)^30 :=
    (norm_le_pi_norm (c-center) i).trans hn
  have limits (i : Fin 5) (l u : ℚ)
      (h₁ : l+1/10^30<centerQ i) (h₂ : centerQ i<u-1/10^30) :
      (l:ℝ)<c i ∧ c i<(u:ℝ) := by
    have a := (Rat.cast_lt (K:=ℝ)).mpr h₁
    have b := (Rat.cast_lt (K:=ℝ)).mpr h₂
    push_cast at a b
    have v := abs_le.mp (he i)
    constructor <;> linarith [v.1,v.2]
  have tt := limits 2 30 31 (by decide +kernel) (by decide +kernel)
  have bb := limits 4 (1/10) (11/100) (by decide +kernel) (by decide +kernel)
  have kk := limits 0 7 8 (by decide +kernel) (by decide +kernel)
  have aa := limits 3 0 1 (by decide +kernel) (by decide +kernel)
  push_cast at tt bb kk aa
  exact ⟨tt.1,tt.2,bb.1,bb.2,kk.1,aa.1⟩

/-- Given the physical two-arm enclosure and the original initial value
problem on each candidate segment, the contraction produces a genuine closed
unit-speed plane immersion. Its local curvature exceeds seven, its signed
angle increment is negative, and its rotation term is nonzero at the origin
of the arclength parametrization. -/
private theorem matched_immersion
    (Φ : ℝ×State → State) (DΦ : ℝ×State → (ℝ×State) →L[ℝ] State)
    (hp : ArmBounds Φ DΦ (forwardEndpointInput phase) plusQ plusColumn)
    (hm : ArmBounds Φ DΦ (backwardEndpointInput phase) minusQ minusColumn)
    (actual : ∀c∈cube,∀s∈Icc (-(c 2)) (c 2), Φ (s,shootingInitial phase c)=wideFlow (s,shootingInitial phase c))
    (initial : ∀c∈cube, Φ (0,shootingInitial phase c)=shootingInitial phase c)
    (ode : ∀c∈cube, ∀s∈Icc (-(c 2)) (c 2), HasDerivAt
      (fun u => Φ (u,shootingInitial phase c)) (field (Φ (s,shootingInitial phase c))) s) :
    ∃ c∈cube, ∃ I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) ∧
      ∀s∈Icc (-(c 2)) (c 2), (I.x s,I.y s)=segmentPosition c s ∧ I.k s=wideFlow (s,shootingInitial phase c) 0 ∧ I.theta s=wideFlow (s,shootingInitial phase c) 5 := by
  obtain ⟨c,hc,zero,_⟩ := unique_root_of_arm_bounds Φ DΦ hp hm
  obtain ⟨T0,T1,b0,b1,k0,u0⟩ := retained_cube_parameters hc
  let T := c 2
  have hT : 0<T := by dsimp [T]; linarith
  let z := fun s : ℝ => Φ (s,shootingInitial phase c)
  have ini : z 0=shootingInitial phase c := initial c hc
  have iv (i : Fin 6) := congrFun (ini.trans (shootingInitial_apply phase c)) i
  have ib : z 0 4=c 4 := iv 4
  have ik : z 0 0=c 0 := iv 0
  have iq : z 0 3=c 3*phase 1 := iv 3
  have dz (s : ℝ) (hs : s∈Icc (-T) T) : HasDerivAt z (field (z s)) s :=
    ode c hc s hs
  have bp : z T 4=z (-T) 4 := by
    have hd (s : ℝ) (hs : s∈Icc (-T) T) : HasDerivAt (fun u => z u 4) 0 s :=
      (ContinuousLinearMap.proj (4:Fin 6) : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (dz s hs)
    have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f:=fun s => z s 4) (f':=fun _ => (0:ℝ)) (a:= -T) (b:=T)
      (fun x hx => hd x (by simpa [uIcc_of_le (by linarith : -T≤T)] using hx))
      (intervalIntegrable_const)
    exact sub_eq_zero.mp (by simpa using eq.symm)
  have rh := (residual_zero_iff Φ c).mp zero
  change z T 0=z (-T) 0 ∧ z T 1=z (-T) 1 ∧ z T 2=z (-T) 2 ∧
    z T 3=z (-T) 3 ∧ z T 5-z (-T) 5= -2*Real.pi at rh
  obtain ⟨h0,h1,h2,h3,h5⟩ := rh
  have matched : z T=z (-T)+angleVector (-2*Real.pi) := by
    ext i
    fin_cases i <;> simp [angleVector,h0,h1,h2,h3,bp]
    linarith
  have pack := reconstruct_trace hT z dz matched
  rw [ib] at pack
  obtain ⟨I,ki,qi,arc⟩ := pack
  have negative : ∃s, I.k s<0 := by
    by_contra! hn
    have mono : Monotone I.theta := monotone_of_deriv_nonneg
      (fun s => (I.angleDerivative s).differentiableAt)
      (fun s => by rw [(I.angleDerivative s).deriv]; exact hn s)
    have m := mono (show 0≤0+2*T by linarith)
    rw [I.turning] at m
    linarith [Real.pi_pos]
  have sign : phase 1<0 := by norm_num [phase,phaseQ]
  refine ⟨c,hc,I,by linarith,by linarith,b0,b1,by rwa [ki,ik],negative,?_,I.least_positive_period (by linarith),?_,?_⟩
  · rw [qi,iq]
    exact mul_ne_zero (by linarith) (mul_ne_zero (ne_of_gt u0) (ne_of_lt sign))
  · intro w wx wy
    apply convexHull_mono _ (square_in_shooting_arc hc w wx wy)
    rintro point ⟨s,hs,rfl⟩
    have hseg : s∈Icc (-T) T := ⟨by dsimp [T]; linarith [hs.1,sample_times.2.2.1],by dsimp [T]; linarith [hs.2,sample_times.2.2.2]⟩
    refine ⟨s,(arc s hseg).1.trans ?_⟩
    exact congrArg framePosition (actual c hc s hseg)
  · intro s hs
    obtain ⟨coord,curv,angle⟩ := arc s hs
    have same : z s=wideFlow (s,shootingInitial phase c) := actual c hc s hs
    exact ⟨coord.trans (congrArg framePosition same),curv.trans (congrFun same 0),angle.trans (congrFun same 5)⟩
private theorem retained_scaled_box {n : ℤ} {T : PolynomialTape n 4000} {q : Fin 6→ℚ}
    {cols : ParameterMatrix} (data : TapeNumbers T q cols) {c : Parameters} (hc : c∈cube)
    {endt η : ℝ} (distT : |endt-4000*step n|≤1/10^30) (hη : η∈unitCell) :
    StateBox (wideFlow (η*endt,shootingInitial phase c)) := by
  let a := shootingInitial phase c
  have cnt : (0:ℕ)<4000 := by decide
  obtain ⟨i,hi,t,ht,he⟩ := CrossingCharts.covered_cell 4000 cnt (4000*η) (by nlinarith [hη.1])
    (by norm_num; linarith [hη.2])
  have transfer := fixed_time_shooting_bounds T data.stepSmall data.origin a
    (in_arm_ball data hc) i hi t ht
  have p := transfer.2.2.1
  have st : ((i:ℝ)+t)*step n=η*(4000*step n) := by rw [←he]; ring
  rw [st] at p
  have dt : |η*endt-η*(4000*step n)|≤1/10^30 := by
    rw [←mul_sub,abs_mul,abs_of_nonneg hη.1]
    exact (mul_le_mul hη.2 distT (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have time := lipschitzWith_iff_norm_sub_le.mp (wide_time_lip a) (η*endt) (η*(4000*step n))
  rw [Real.norm_eq_abs] at time
  norm_num only [NNReal.coe_ofNat] at time
  have dis : ‖wideFlow (η*endt,a)-path (T.data i) d t‖≤1 :=
    (norm_sub_le_norm_sub_add_norm_sub _ (wideFlow (η*(4000*step n),a)) _).trans (by linarith)
  intro j hj
  have inner := (lift_inner (T.small i hi) ht).1 j hj
  change |path (T.data i) d t j|≤9 at inner
  have diff := (coordinate_bound (wideFlow (η*endt,a)-path (T.data i) d t) j).trans dis
  change |wideFlow (η*endt,a) j-path (T.data i) d t j|≤1 at diff
  have tri := abs_add_le (wideFlow (η*endt,a) j-path (T.data i) d t j) (path (T.data i) d t j)
  rw [sub_add_cancel] at tri
  change |wideFlow (η*endt,a) j|≤10
  linarith

/-- Only the two signed finite tapes and their identifiable boundary rows are
inputs. Thus all analytic, geometric and irrational-target implications for
one complete winding are accounted for before the remaining rows are replayed. -/
private theorem immersion_from_tapes
    (P : PolynomialTape Middle.hn 4000) (M : PolynomialTape (-Middle.hn) 4000)
    (p0 : P.node 0=initialNode) (m0 : M.node 0=initialNode)
    (pn : ∀j : ℕ,(P.data 3999 j).sum=(plusNode[j]?).getD 0)
    (mn : ∀j : ℕ,(M.data 3999 j).sum=(minusNode[j]?).getD 0) :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) ∧
      ∀s∈Icc (-(c 2)) (c 2), (I.x s,I.y s)=segmentPosition c s ∧ I.k s=wideFlow (s,shootingInitial phase c) 0 ∧ I.theta s=wideFlow (s,shootingInitial phase c) 5 := by
  have pos := plus_numbers P p0 pn
  have neg := minus_numbers M m0 mn
  have err (c : Parameters) (hc : c∈cube) : |c 2-center 2|≤1/10^30 :=
    (norm_le_pi_norm (c-center) 2).trans (show ‖c-center‖≤1/(10:ℝ)^30 from hc)
  have opposite (c : Parameters) (hc : c∈cube) : |-(c 2)-(-(center 2))|≤1/10^30 := by
    rw [show -(c 2)-(-(center 2))= -(c 2-center 2) by ring,abs_neg]
    exact err c hc
  have pArm := arm_from_tape P pos (forwardEndpointInput phase) (fun _ => rfl)
    half_step err
  have mArm := arm_from_tape M neg (backwardEndpointInput phase) (fun _ => rfl)
    minus_half_step opposite
  apply matched_immersion wideFlow selectedDerivative pArm mArm
      (fun _ _ _ _ => rfl)
      (fun c _ => wideFlow_zero (shootingInitial phase c))
  intro c hc s hs
  have T0 : 0<c 2 := by
    have he := (abs_le.mp (err c hc)).1
    have hq : (30:ℚ)<centerQ 2 := by decide +kernel
    have hreal : (30:ℝ)<center 2 := by
      simpa only [center,Rat.cast_ofNat] using (Rat.cast_lt (K:=ℝ)).mpr hq
    linarith
  have box : StateBox (wideFlow (s,shootingInitial phase c)) := by
    by_cases h : 0≤s
    · have hη : s/c 2∈unitCell :=
        ⟨div_nonneg h T0.le,(div_le_one T0).mpr hs.2⟩
      have e := retained_scaled_box pos hc (endt:=c 2) (η:=s/c 2) (by rw [←half_step]; exact err c hc) hη
      simpa only [div_mul_cancel₀ _ T0.ne'] using e
    · have hη : (-s)/c 2∈unitCell :=
        ⟨div_nonneg (by linarith) T0.le,(div_le_one T0).mpr (by linarith [hs.1])⟩
      have e := retained_scaled_box neg hc (endt:= -(c 2)) (η:=(-s)/c 2)
        (by rw [←minus_half_step]; exact opposite c hc) hη
      simpa only [mul_neg,div_mul_cancel₀ _ T0.ne',neg_neg] using e
  simpa only [wideField,wideClip_id box] using wideFlow_time (shootingInitial phase c) s

theorem exists_retained_immersion :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) ∧
      ∀s∈Icc (-(c 2)) (c 2), (I.x s,I.y s)=segmentPosition c s ∧ I.k s=wideFlow (s,shootingInitial phase c) 0 ∧ I.theta s=wideFlow (s,shootingInitial phase c) 5 := by
  obtain ⟨pi,mi,pe,me⟩ := actual_grid_ends
  apply immersion_from_tapes CompletePlus.tape CompleteMinus.tape
    ((CompletePlus.range 0 (by decide)).1.trans pi) ((CompleteMinus.range 0 (by decide)).1.trans mi)
  · intro j
    change (packedData (CompletePlus.atRow 3999).input j).sum=_
    rw [packed_sum,(CompletePlus.atRow 3999).endpoints.2,(CompletePlus.range 3999 (by decide)).2,pe]
  · intro j
    change (packedData (CompleteMinus.atRow 3999).input j).sum=_
    rw [packed_sum,(CompleteMinus.atRow 3999).endpoints.2,(CompleteMinus.range 3999 (by decide)).2,me]

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.exists_retained_immersion
