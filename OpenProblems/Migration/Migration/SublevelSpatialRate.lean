import Migration.SublevelMoments

noncomputable section
open MeasureTheory Set
namespace MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The arclength mean of the actual elastic force is half the cubic
curvature integral, by periodicity of the first curvature derivative. -/
theorem bending_force_mean :
    (∫ s in 0..c.period,c.force s)=(∫ s in 0..c.period,c.curvature s^3)/2 := by
  have f := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => c.curvature₁_deriv s) (c.curvature₂_continuous.intervalIntegrable ..)
  have eq : c.curvature₁ c.period=c.curvature₁ 0 := by simpa using c.curvature₁_periodic 0
  rw [eq,sub_self] at f
  simp only [force]
  rw [intervalIntegral.integral_add (f:=c.curvature₂) (g:=fun s => c.curvature s^3/2)
    (c.curvature₂_continuous.intervalIntegrable ..)
    (((c.curvature_continuous.pow 3).div_const 2).intervalIntegrable ..),
    intervalIntegral.integral_div,f,zero_add]

/-- The two signed moment estimates follow simultaneously from a genuine
nonnegative product rate, without prescribing either moment by hand. -/
theorem bending_moment_inputs {μ R : ℝ} (hR : 0≤R)
    (mean : (∫ s in 0..c.period,c.curvature s)=c.period*μ)
    (scale : c.period*R^2=2*c.energy)
    (rate : c.period*c.dissipation≤c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)) :
    2*(∫ s in 0..c.period,c.curvature s^3) ≤ (2*c.energy)*(μ+R) ∧
    4*Real.pi^2*(2*c.energy) ≤ 2*c.period^2*(∫ s in 0..c.period,c.curvature s*c.force s) := by
  let L := c.period
  let E := c.energy
  let J := ∫ s in 0..c.period,c.curvature s*c.force s
  let C := ∫ s in 0..c.period,c.curvature s^3
  let b := E/(2*L)
  have hp : 0<L := c.period_pos
  have ep : 0<E := c.energy_pos
  have bpos : 0≤b := by dsimp [b]; positivity
  have eb : 2*b*L=E := by dsimp [b]; field_simp
  change L*c.dissipation≤E*J at rate
  have mj : c.dissipation≤2*b*J := by
    apply le_of_mul_le_mul_left (a:=L) _ hp
    calc L*c.dissipation≤E*J := rate
         _ = L*(2*b*J) := by rw [←eb]; ring
  have sr := c.growthResidual_square
  change (∫ s in 0..c.period,c.growthResidual s^2)=c.dissipation-2*b*J+b^2*(2*E) at sr
  have bounded : (∫ s in 0..c.period,c.growthResidual s^2)≤b^2*(2*E) := by linarith
  have cs := interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ)) continuous_const
    c.growthResidual_continuous c.period_pos.le
  have sc : (∫ s in 0..c.period,c.growthResidual s)^2 ≤ L*(∫ s in 0..c.period,c.growthResidual s^2) := by
    simpa [L] using cs
  have meanResidual : (∫ s in 0..c.period,c.growthResidual s)=C/2-b*(L*μ) := by
    unfold growthResidual
    rw [intervalIntegral.integral_sub (c.force_continuous.intervalIntegrable ..)
      ((c.curvature_continuous.const_mul _).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,mean,c.bending_force_mean]
  rw [meanResidual] at sc
  have square : (C/2-b*(L*μ))^2≤(b*L*R)^2 := by
    calc
      _ ≤ L*(b^2*(2*E)) := sc.trans (mul_le_mul_of_nonneg_left bounded hp.le)
      _ = _ := by change c.period*(b^2*(2*c.energy))=(b*c.period*R)^2; rw [←scale]; ring
  have up := le_of_sq_le_sq square (show 0≤b*L*R by positivity)
  constructor
  · change 2*C≤(2*E)*(μ+R)
    linarith only [up,congrArg (fun z => z*μ) eb,congrArg (fun z => z*R) eb]
  · have sv := c.sharp_virial
    change 4*Real.pi^2*E^2 ≤ c.dissipation*L^3 at sv
    change 4*Real.pi^2*(2*E)≤2*L^2*J
    apply le_of_mul_le_mul_left (a:=E) _ ep
    linarith only [sv,mul_le_mul_of_nonneg_right rate (sq_nonneg L)]

end MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
namespace MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Strict sign on an actual once-turning arclength slice. Only initial
geometric input and the free elastic spatial operator occur in the statement. -/
theorem bending_one_turn_strict
    (turning : (∫ s in 0..c.period,c.curvature s)=2*Real.pi)
    (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  by_contra! bad
  let L := c.period
  let B := 2*c.energy
  let μ := 2*Real.pi/L
  let R := Real.sqrt (B/L)
  let σ := R/μ
  let d := L*B-4*Real.pi^2
  let u := fun s => c.curvature s-μ
  let V := ∫ s in 0..L,u s^2
  let I₃ := ∫ s in 0..L,u s^3
  let I₄ := ∫ s in 0..L,u s^4
  let J := ∫ s in 0..L,c.curvature s*c.force s
  have lp : 0<L := c.period_pos
  have bp : 0<B := by dsimp [B]; exact mul_pos (by norm_num) c.energy_pos
  have mp : 0<μ := by dsimp [μ]; positivity
  have rp : 0<R := Real.sqrt_pos_of_pos (div_pos bp lp)
  have sp : 0<σ := div_pos rp mp
  have turn : L*μ=2*Real.pi := by dsimp [μ]; field_simp
  have rms : L*R^2=B := by
    dsimp only [R]; rw [Real.sq_sqrt (div_nonneg bp.le lp.le)]; field_simp
  have rs : μ*σ=R := by dsimp [σ]; field_simp
  have energy : B=L*μ^2*σ^2 := by rw [←rms,←rs]; ring
  have mean : (∫ s in 0..c.period,c.curvature s)=L*μ := turning.trans turn.symm
  obtain ⟨avg,m2,m3,m4⟩ := BendingSublevel.centered_moments c.curvature_continuous mean
  change (∫ s in 0..L,u s)=0 at avg
  change (∫ s in 0..L,c.curvature s^2)=L*μ^2+V at m2
  change (∫ s in 0..L,c.curvature s^3)=L*μ^3+3*μ*V+I₃ at m3
  change (∫ s in 0..L,c.curvature s^4)=L*μ^4+6*μ^2*V+4*μ*I₃+I₄ at m4
  have bend : B=L*μ^2+V := by
    change 2*((∫ s in 0..L,c.curvature s^2)/2)=L*μ^2+V
    linarith only [m2]
  have tSq : (L*μ)^2=4*Real.pi^2 := by rw [turn]; ring
  have dV : L*V=d := by
    change L*V=L*B-4*Real.pi^2
    rw [bend,←tSq]; ring
  have dpos : 0<d := by
    change 0<L*B-4*Real.pi^2
    change 4*Real.pi^2<B*L at above
    linarith only [above]
  have dcap : d≤36 := by
    change L*B-4*Real.pi^2≤36
    change B*L≤4*Real.pi^2+36 at below
    linarith only [below]
  have vp : 0<V := pos_of_mul_pos_right (dV.symm ▸ dpos) lp.le
  have variance : V=L*μ^2*(σ^2-1) := by linarith only [energy,bend]
  have ratio : 4*Real.pi^2*(σ^2-1)=d := by rw [←dV,variance,←tSq]; ring
  have mass : 2*Real.pi*V=d*μ := by rw [←dV,←turn]; ring
  have s1 : 1≤σ := by
    have ss : 0<σ^2-1 := pos_of_mul_pos_right (show 0<4*Real.pi^2*(σ^2-1) by rwa [ratio]) (by positivity)
    by_contra! h
    nlinarith only [ss,mul_pos (sub_pos.mpr h) (show 0<σ+1 by linarith)]
  have qp := BendingSublevel.positive_gradient_of_variance c μ avg vp
  have gn := BendingSublevel.curvature_fourth_moment c μ avg
  change 3*I₄^2≤V^3*c.curvatureGradientSquare at gn
  obtain ⟨cub,vir⟩ := c.bending_moment_inputs rp.le mean rms bad
  change 2*(∫ s in 0..L,c.curvature s^3)≤B*(μ+R) at cub
  rw [m3,bend,←rs] at cub
  have cub' : 2*(L*μ^3+3*μ*V+I₃)≤(L*μ^2+V)*μ*(1+σ) := by linarith only [cub]
  change 4*Real.pi^2*B≤2*L^2*J at vir
  rw [←tSq] at vir
  have jlow : μ^2*B≤2*J := by
    apply le_of_mul_le_mul_left (a:=L^2) _ (sq_pos_of_pos lp)
    linarith only [vir]
  have jexact := c.curvature_gradient_identity
  change c.curvatureGradientSquare=(∫ s in 0..L,c.curvature s^4)/2-J at jexact
  rw [m4] at jexact
  rw [bend] at jlow
  exact BendingSublevel.incompatible_nondecreasing_slice dcap mp s1 vp qp ratio mass variance cub'
    (by linarith only [jlow,jexact]) gn

end MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
namespace MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Reflection reverses signed curvature and leaves the free elastic product
rate and both norms unchanged. -/
def bendingReflection : ClosedFrenetCurve where
  period := c.period
  period_pos := c.period_pos
  curve := fun s => star (c.curve s)
  tangent := fun s => star (c.tangent s)
  curvature := fun s => -c.curvature s
  curvature₁ := fun s => -c.curvature₁ s
  curvature₂ := fun s => -c.curvature₂ s
  curve_periodic := fun s => congrArg star (c.curve_periodic s)
  tangent_periodic := fun s => congrArg star (c.tangent_periodic s)
  curvature_periodic := fun s => congrArg Neg.neg (c.curvature_periodic s)
  curvature₁_periodic := fun s => congrArg Neg.neg (c.curvature₁_periodic s)
  curve_deriv := fun s => (c.curve_deriv s).star
  tangent_deriv := by
    intro s
    apply (c.tangent_deriv s).star.congr_deriv
    simp [star_mul]
    ring
  curvature_deriv := fun s => (c.curvature_deriv s).neg
  curvature₁_deriv := fun s => (c.curvature₁_deriv s).neg
  curvature₂_continuous := c.curvature₂_continuous.neg
  tangent_unit := fun s => by simp [c.tangent_unit]

theorem bending_reflection_energy : c.bendingReflection.energy=c.energy := by
  simp [energy,bendingReflection]

theorem bending_reflection_force (s : ℝ) : c.bendingReflection.force s= -c.force s := by
  dsimp [force,bendingReflection]
  ring

theorem bending_reflection_dissipation : c.bendingReflection.dissipation=c.dissipation := by
  change (∫ s in 0..c.period,c.bendingReflection.force s^2)=∫ s in 0..c.period,c.force s^2
  simp only [c.bending_reflection_force,neg_sq]

theorem bending_negative_turn_strict
    (turning : (∫ s in 0..c.period,c.curvature s)= -(2*Real.pi))
    (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  have t : (∫ s in 0..c.bendingReflection.period,c.bendingReflection.curvature s)=2*Real.pi := by
    change (∫ s in 0..c.period,-c.curvature s)=_
    rw [intervalIntegral.integral_neg,turning,neg_neg]
  have h := c.bendingReflection.bending_one_turn_strict t
    (by rwa [c.bending_reflection_energy]) (by rwa [c.bending_reflection_energy])
  rw [c.bending_reflection_energy,c.bending_reflection_dissipation] at h
  simp only [c.bending_reflection_force] at h
  change c.energy*(∫ s in 0..c.period,(-c.curvature s)*(-c.force s))<c.period*c.dissipation at h
  simpa only [neg_mul_neg] using h

end MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
namespace MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- Closing the tangent forces quantization of its signed curvature integral. -/
theorem curvature_turns_integer :
    ∃ n : ℤ, (∫ s in 0..c.period,c.curvature s)=(n:ℝ)*(2*Real.pi) := by
  let K := ∫ s in 0..c.period,c.curvature s
  have turn := c.tangent_eq_exp_integral_curvature 0 c.period
  have per : c.tangent c.period=c.tangent 0 := by simpa using c.tangent_periodic 0
  rw [per] at turn
  have nz : c.tangent 0≠0 := by
    intro h
    have := c.tangent_unit 0
    rw [h,norm_zero] at this
    norm_num at this
  have ex : Complex.exp ((K:ℂ)*Complex.I)=1 := by
    apply mul_right_cancel₀ nz
    simpa only [one_mul] using turn.symm
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp ex
  refine ⟨n,?_⟩
  have ei := congrArg Complex.im hn
  simpa [Complex.mul_im,Complex.mul_re,K] using ei

/-- A zero signed turning angle costs at least 8π² in the physical
length times the integral of squared curvature. -/
theorem zero_turn_product_floor
    (zero : (∫ s in 0..c.period,c.curvature s)=0) : 8*Real.pi^2≤2*c.energy*c.period := by
  let L := c.period
  let θ := fun x => ∫ s in 0..x,c.curvature s
  let S := fun s => Complex.exp (((θ s/2:ℝ):ℂ)*Complex.I)
  let v := fun s => S s*((c.curvature s/2:ℝ):ℂ)*Complex.I
  have lp : 0<L := c.period_pos
  have dθ (s : ℝ) : HasDerivAt θ (c.curvature s) s :=
    intervalIntegral.integral_hasDerivAt_right (c.curvature_continuous.intervalIntegrable 0 s)
      c.curvature_continuous.stronglyMeasurable.stronglyMeasurableAtFilter c.curvature_continuous.continuousAt
  have ds (s : ℝ) : HasDerivAt S (v s) s := by
    apply (((((dθ s).div_const 2).ofReal_comp).mul_const Complex.I).cexp).congr_deriv
    dsimp [v,S]
    ring
  have cs := continuous_iff_continuousAt.mpr (fun s => (ds s).continuousAt)
  have cv : Continuous v := (cs.mul (Complex.continuous_ofReal.comp
    (c.curvature_continuous.div_const 2))).mul continuous_const
  have unit (s : ℝ) : ‖S s‖=1 := by simp [S,Complex.norm_exp]
  have s0 : S 0=1 := by simp [S,θ]
  have sL : S L=1 := by simp [S,θ,L,zero]
  have comp (s : ℝ) : S s^2*c.tangent 0=c.tangent s := by
    rw [c.tangent_eq_exp_integral_curvature 0 s]
    dsimp only [S]
    rw [pow_two,←Complex.exp_add]
    push_cast
    congr 2
    ring
  have nonzero : c.tangent 0≠0 := by
    intro h
    have hw := c.tangent_unit 0
    simp [h] at hw
  have square : (∫ s in 0..L,S s^2)=0 := by
    apply mul_right_cancel₀ nonzero
    rw [zero_mul,←intervalIntegral.integral_mul_const]
    simp_rw [comp]
    exact c.tangent_integral_zero
  let m := (∫ s in 0..L,S s)/(L:ℂ)
  have floor := BendingSublevel.spinor_variance lp cs unit square
  change L≤2*(∫ s in 0..L,‖S s-m‖^2) at floor
  have cm : (∫ s in 0..L,S s-m)=0 := by
    rw [intervalIntegral.integral_sub (cs.intervalIntegrable ..) intervalIntegrable_const,
      intervalIntegral.integral_const,sub_zero,Complex.real_smul]
    dsimp only [m]
    have lm : (L:ℂ)≠0 := by exact_mod_cast lp.ne'
    field_simp
    ring
  have wir := MigrationGeometry.Flow.LowBending.periodic_wirtinger lp (fun s => S s-m) v
    (by rw [sL,s0]) (fun s => (ds s).sub_const m) cv cm
  have vn (s : ℝ) : ‖v s‖^2=(1/4:ℝ)*c.curvature s^2 := by
    simp only [v,norm_mul,unit,one_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    ring
  simp_rw [vn] at wir
  rw [intervalIntegral.integral_const_mul] at wir
  have he : (∫ s in 0..L,c.curvature s^2)=2*c.energy := by unfold energy; ring
  rw [he] at wir
  apply le_of_mul_le_mul_left (a:=L) _ lp
  change L*(8*Real.pi^2)≤L*(2*c.energy*L)
  linarith only [mul_le_mul_of_nonneg_left floor (sq_nonneg (2*Real.pi)),wir]

/-- Every slice in the defect-36 sublevel has signed turning angle ±2π. -/
theorem low_product_turning
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    (∫ s in 0..c.period,c.curvature s)=2*Real.pi ∨
      (∫ s in 0..c.period,c.curvature s)= -(2*Real.pi) := by
  obtain ⟨n,h⟩ := c.curvature_turns_integer
  have cs := MigrationGeometry.Flow.LowBending.interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ))
    continuous_const c.curvature_continuous c.period_pos.le
  have cc : (∫ s in 0..c.period,c.curvature s)^2≤2*c.energy*c.period := by
    unfold energy
    have bound : (∫ s in 0..c.period,c.curvature s)^2≤c.period*(∫ s in 0..c.period,c.curvature s^2) := by
      simpa using cs
    linarith only [bound]
  have pgt : 9<Real.pi^2 := by nlinarith only [Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have nz : n≠0 := by
    rintro rfl
    simp only [Int.cast_zero,zero_mul] at h
    linarith only [c.zero_turn_product_floor h,below,pgt]
  rw [h] at cc
  have small : (n:ℝ)^2<4 := by
    by_contra! large
    nlinarith only [cc,below,mul_le_mul_of_nonneg_right large (sq_nonneg (2*Real.pi)),pgt]
  have nsq : n^2<4 := by exact_mod_cast small
  have vals : n=1 ∨ n= -1 := by
    have hi : n<2 := by nlinarith only [nsq,sq_nonneg (n-2)]
    have lo : -2<n := by nlinarith only [nsq,sq_nonneg (n+2)]
    omega
  rcases vals with rfl|rfl
  · left; simpa using h
  · right; simpa using h

end MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
namespace MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

theorem bending_sublevel_strict (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  rcases c.low_product_turning below with pos|neg
  · exact c.bending_one_turn_strict pos above below
  · exact c.bending_negative_turn_strict neg above below

end MigrationGeometry.Flow.LowBending.ClosedFrenetCurve
