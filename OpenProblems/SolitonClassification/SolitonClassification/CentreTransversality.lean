import SolitonClassification.MovingSeamPhysical
import SolitonClassification.MovingSeamSlab

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open FrozenStress

private theorem unit_orbit (x : Phase) (unit : radiusSquared x=1) :
    ∃ z : Orbit, coords z = solution 0 x := by
  let f := solution 0 x
  have hf (s : ℝ) := hasDerivAt_pi.mp (solution_derivative 0 x s)
  have dk (s : ℝ) : HasDerivAt (fun u => f u 0) (f s 1) s := hf s 0
  have dv (s : ℝ) : HasDerivAt (fun u => f u 1) (-(f s 0)^3/2-f s 2) s := hf s 1
  have dp (s : ℝ) : HasDerivAt (fun u => f u 2) (-f s 0*f s 3) s := hf s 2
  have dq (s : ℝ) : HasDerivAt (fun u => f u 3) (f s 0*f s 2) s := by simpa [f,rhs] using hf s 3
  have U (s : ℝ) : f s 2^2+f s 3^2=1 := by
    have h (t : ℝ) : HasDerivAt (fun u => f u 2^2+f u 3^2) 0 t := by
      convert! ((dp t).pow 2).add ((dq t).pow 2) using 1; ring
    have e := is_const_of_deriv_eq_zero (fun u => (h u).differentiableAt) (fun u => (h u).deriv) s 0
    simpa only [f,solution_zero] using e.trans (by simpa [f,solution_zero,radiusSquared] using unit)
  refine ⟨⟨_,_,_,_,dk,dv,dp,dq,U⟩,?_⟩
  funext t i; fin_cases i <;> rfl

/-- Every normalized unit-position state of large stress has a positive
    outgoing corrected-height rate in the frozen clock. -/
theorem frozen_unit_rate {x : Phase} (unit : radiusSquared x=1) (ha : 12≤amplitude x) :
    1/4 ≤ heightRate (0,x) := by
  obtain ⟨z,eq⟩ := unit_orbit x unit
  have state : coords z 0=x := (congrFun eq 0).trans (solution_zero _ _)
  have hA : 12≤z.amplitude 0 := by change 12≤amplitude (coords z 0); rwa [state]
  have reg : regular x := ⟨by rw [unit]; norm_num,Real.sqrt_pos.mp (show 0<amplitude x by linarith)⟩
  have heights : (fun s => height (solution 0 x s))=z.outgoingHeight := by
    funext s
    rw [←eq]
    have hs : scale (coords z s)=1 := by simp [scale,radiusSquared,coords,z.unit s]
    have hA' : amplitude (coords z s)=z.amplitude s := rfl
    have hR : root (coords z s)=z.root s := rfl
    simp only [height,Orbit.outgoingHeight,correctedOutgoing,shape,slope,along,across,hs,hA',hR,
      div_one,one_pow,mul_one,neg_mul]
    rfl
  have h := rate_eq 0 x 0 (by simpa only [solution_zero] using reg)
  rw [heights,solution_zero] at h
  rw [←h.deriv]
  exact (z.large_amplitude_height hA).2

/-- A uniform rate margin on every compact instantaneous stress band, with
    arbitrary radial alignment, curvature phase and transverse stress. -/
theorem unit_rate_band (B : ℝ) :
    ∃ ε>0, ∀ x : Phase, radiusSquared x=1 → 12≤amplitude x → amplitude x≤B →
      ∀ d : ℝ, |d|<ε → 1/8<heightRate (d,x) := by
  let K : Set Phase := {x | radiusSquared x=1 ∧ 12≤amplitude x ∧ amplitude x≤B}
  have rc : Continuous radiusSquared := by unfold radiusSquared; fun_prop
  have ac : Continuous amplitude := by unfold amplitude stressSquared; fun_prop
  have closed : IsClosed K := (isClosed_eq rc continuous_const).inter
    ((isClosed_le continuous_const ac).inter (isClosed_le ac continuous_const))
  let M := 2*|B|+2
  have comp : IsCompact K := (isCompact_Icc (a:=fun _ : Fin 4 => -M) (b:=fun _ => M)).of_isClosed_subset closed (by
    intro x hx
    obtain ⟨unit,big,cap⟩ := hx
    have A : amplitude x^2 = (x 0^2/2)^2+x 1^2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
    change x 2^2+x 3^2=1 at unit
    have nn : 0≤amplitude x := Real.sqrt_nonneg _
    have av : |x 1|≤amplitude x := le_of_sq_le_sq
      (by rw [sq_abs]; nlinarith [sq_nonneg (x 0^2/2)]) nn
    have ak : x 0^2/2≤amplitude x := le_of_sq_le_sq (by nlinarith [sq_nonneg (x 1)]) nn
    have k : |x 0|≤M := by
      dsimp [M]; nlinarith [sq_nonneg (|x 0|-1),sq_abs (x 0),le_abs_self B]
    have v : |x 1|≤M := by dsimp [M]; linarith [le_abs_self B,abs_nonneg B]
    have p : |x 2|≤M := by
      apply le_trans (le_of_sq_le_sq (b:=1) (by rw [sq_abs]; nlinarith [sq_nonneg (x 3)]) zero_le_one)
      dsimp [M]; linarith [abs_nonneg B]
    have q : |x 3|≤M := by
      apply le_trans (le_of_sq_le_sq (b:=1) (by rw [sq_abs]; nlinarith [sq_nonneg (x 2)]) zero_le_one)
      dsimp [M]; linarith [abs_nonneg B]
    have coords (i : Fin 4) : |x i|≤M := by fin_cases i <;> assumption
    exact ⟨fun i => (abs_le.mp (coords i)).1,fun i => (abs_le.mp (coords i)).2⟩)
  let : CompactSpace K := isCompact_iff_compactSpace.mp comp
  have all : ∀ᶠ d in 𝓝 (0:ℝ), ∀x : K, 1/8<heightRate (d,x.1) := by
    apply tube (P := fun u : K×ℝ => 1/8<heightRate (u.2,u.1.1))
    intro x
    obtain ⟨unit,big,_⟩ := x.property
    have reg : regular x.1 := ⟨by rw [unit]; norm_num,Real.sqrt_pos.mp (show 0<amplitude x.1 by linarith)⟩
    have ev := (rate_continuousAt (u:=(0,x.1)) reg).tendsto.eventually
      (lt_mem_nhds (show 1/8<heightRate (0,x.1) by linarith [frozen_unit_rate unit big]))
    have h : Continuous (fun u : K×ℝ => (u.2,u.1.1)) :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    exact (h.tendsto (x,(0:ℝ))).eventually ev
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp all
  refine ⟨ε,hε,?_⟩
  intro x unit big cap d small
  exact hball (by simpa using small) (⟨x,unit,big,cap⟩ : K)

/-- Freeze the units at a point of the physical trajectory. The derivative
    in physical arclength is exactly l times the derivative in frozen units. -/
theorem restored_rate {l d : ℝ} (hl : 0<l) (scale_eq : l^4*d=1) (y : Phase)
    (hy : regular y) (hx : regular (restore l y)) :
    heightRate (1,restore l y) = heightRate (d,y)*l := by
  have left := rate_eq 1 (restore l y) 0 (by simpa only [solution_zero] using hx)
  have right := rate_eq d y 0 (by simpa only [solution_zero] using hy)
  rw [solution_zero] at left right
  have clk : HasDerivAt (fun t : ℝ => l*t) l 0 := by simpa using (hasDerivAt_id (0:ℝ)).const_mul l
  have de : HasDerivAt (fun t => height (solution d y (l*t))) (heightRate (d,y)*l) 0 :=
    (show HasDerivAt (fun s => height (solution d y s)) (heightRate (d,y)) (l*0) by simpa using right).comp 0 clk
  have same : (fun t => height (solution 1 (restore l y) t)) = fun t => height (solution d y (l*t)) := by
    funext t
    rw [physical_support_conjugacy scale_eq]
    exact (restore_invariants hl _).2.2.2.2.2.2.1
  rw [←same] at de
  exact left.unique de

theorem regular_physical_rate_band (B : ℝ) :
    ∃ ε>0, ∀ x : Phase, regular x →
      12≤(root x/scale x)^2 → (root x/scale x)^2≤B → 1/(scale x)^4<ε →
      scale x/8 < heightRate (1,x) := by
  obtain ⟨ε,pε,rate⟩ := unit_rate_band B
  refine ⟨ε,pε,?_⟩
  intro x hx lo hi small
  let l := scale x
  have lp : 0<l := Real.rpow_pos_of_pos hx.1 _
  let y := restore l⁻¹ x
  have lsq : l^6=radiusSquared x := by
    dsimp [l,scale]; rw [←Real.rpow_natCast _ 6,←Real.rpow_mul hx.1.le]; norm_num
  have back : restore l y=x := by
    funext i; fin_cases i <;> simp [y,restore,lp.ne']
  have unit : radiusSquared y=1 := by
    have s : radiusSquared y=(l⁻¹)^6*radiusSquared x := by simp [y,radiusSquared,restore]; ring
    rw [s,←lsq]; field_simp [lp.ne']
  have r := (restore_invariants (inv_pos.mpr lp) x).2.1
  have amp : amplitude y = (root x/scale x)^2 := by
    rw [←Real.sq_sqrt (show 0≤amplitude y from Real.sqrt_nonneg _)]
    change root (restore l⁻¹ x)^2=_
    rw [r]; dsimp [l]; ring
  have reg : regular y := ⟨by rw [unit]; norm_num,Real.sqrt_pos.mp (by change 0<amplitude y; linarith)⟩
  let d := 1/l^4
  have de : 0<d := by dsimp [d]; positivity
  have rbound := rate y unit (amp ▸ lo) (amp ▸ hi) d (by simpa only [abs_of_pos de] using small)
  have he := restored_rate lp (d:=d) (by dsimp [d]; field_simp) y reg (back ▸ hx)
  rw [back] at he
  rw [he]
  simpa only [div_eq_mul_inv,mul_comm,one_mul,l] using mul_lt_mul_of_pos_right rbound lp

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.unit_rate_band
