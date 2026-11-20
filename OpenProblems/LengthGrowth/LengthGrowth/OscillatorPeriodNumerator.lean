import LengthGrowth.OscillatorMean

/-! Positivity of the original full-angle quartic period numerator, expressed
in the midpoint and half-width of two turning values. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory
set_option maxHeartbeats 650000

def orbitOffset (c r : ℝ) := 2*c^2+r^2-1
def rawTerm (c r y : ℝ) := (c+y)/√((2*c+y)^2+orbitOffset c r)

private theorem raw_cont {c r : ℝ} (hd : 0<orbitOffset c r) : Continuous (rawTerm c r) := by
  unfold rawTerm
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact (sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg _) hd)).ne'

private theorem split_radicals {c x y : ℝ} (hc : 0≤c) (hcu : c≤1/2)
    (hx : x^2=scale c) :
    (x+y)/√(q c y+4*x*y)+(x-y)/√(q c y-4*x*y) =
      x*weight c y*factor c y := by
  let P := q c y+4*x*y
  let M := q c y-4*x*y
  have hep : 0<offset c := by linarith [(parameters hc hcu).2.2.1]
  have hp : 0<P := by
    dsimp [P,q]
    nlinarith only [hx,hep,sq_nonneg (2*x+y)]
  have hm : 0<M := by
    dsimp [M,q]
    nlinarith only [hx,hep,sq_nonneg (2*x-y)]
  let U := √P
  let V := √M
  have hu : 0<U := sqrt_pos.mpr hp
  have hv : 0<V := sqrt_pos.mpr hm
  have u2 : U^2=P := sq_sqrt hp.le
  have v2 : V^2=M := sq_sqrt hm.le
  have ed : discr c y=P*M := by
    dsimp [discr,P,M,q]
    rw [← hx]
    ring
  have es : √(discr c y)=U*V := by rw [ed,sqrt_mul hp.le]
  have hQ := (discr_positive hc hcu y).2
  have hD := (discr_positive hc hcu y).1
  have ed' : discr c y=U^2*V^2 := by rw [u2,v2,ed]
  have w : weight c y=1/U+1/V := by
    have e : 2*q c y/discr c y+2/√(discr c y)=(1/U+1/V)^2 := by
      rw [es,ed']
      field_simp [hu.ne',hv.ne']
      dsimp only [P,M] at u2 v2
      nlinarith only [u2,v2]
    unfold weight
    rw [e,Real.sqrt_sq (by positivity)]
  have hden : 0<q c y+U*V := by positivity
  change (x+y)/U+(x-y)/V=_
  rw [w]
  dsimp only [factor]
  rw [es]
  field_simp [hu.ne',hv.ne',hden.ne']
  dsimp only [P,M] at u2 v2
  linear_combination -y*V*u2+y*U*v2

theorem low_pair {c r y : ℝ} (hc : 0<c) (hcu : c≤1/2) (hr : 0<r)
    (turn : 2*c*r^2 = 1+c-2*c^3) :
    rawTerm c r (r*y)+rawTerm c r (-(r*y)) =
      (c/r)*weight c y*factor c y := by
  have hd : den c=2*c*r^2 := by unfold den; linarith only [turn]
  have ht : (c/r)^2=scale c := by
    unfold scale
    rw [hd]
    field_simp [hc.ne',hr.ne']
  have he : orbitOffset c r/r^2=offset c := by
    unfold orbitOffset offset
    rw [hd]
    field_simp [hc.ne',hr.ne']
    linarith only [turn]
  have ratio (v : ℝ) : rawTerm c r (r*v) =
      (c/r+v)/√(q c v+4*(c/r)*v) := by
    have rad : (2*c+r*v)^2+orbitOffset c r = r^2*(q c v+4*(c/r)*v) := by
      unfold q
      rw [← ht,← he]
      field_simp [hr.ne']
      ring
    unfold rawTerm
    rw [rad,Real.sqrt_mul (sq_nonneg r),Real.sqrt_sq hr.le]
    rw [show c+r*v=r*(c/r+v) by field_simp [hr.ne']]
    exact mul_div_mul_left _ _ hr.ne'
  rw [show -(r*y)=r*(-y) by ring,ratio y,ratio (-y)]
  have qneg : q c (-y)=q c y := by simp [q]
  rw [qneg,show q c y+4*(c/r)*(-y)=q c y-4*(c/r)*y by ring,← sub_eq_add_neg]
  exact split_radicals hc.le hcu ht

theorem high_pair {c r y : ℝ} (hc : 1/2≤c) (hy : 0≤y) (hy' : y≤r)
    (hd : 0<orbitOffset c r) : 0≤rawTerm c r y+rawTerm c r (-y) := by
  let A := √((2*c+y)^2+orbitOffset c r)
  let B := √((2*c-y)^2+orbitOffset c r)
  have ap : 0<(2*c+y)^2+orbitOffset c r := by positivity
  have bp : 0<(2*c-y)^2+orbitOffset c r := by positivity
  have ha : 0<A := sqrt_pos.mpr ap
  have hb : 0<B := sqrt_pos.mpr bp
  have a2 : A^2 = (2*c+y)^2+orbitOffset c r := sq_sqrt ap.le
  have b2 : B^2 = (2*c-y)^2+orbitOffset c r := sq_sqrt bp.le
  change 0≤(c+y)/A+(c+-y)/√((2*c+-y)^2+orbitOffset c r)
  rw [← sub_eq_add_neg,← sub_eq_add_neg (2*c)]
  change 0≤(c+y)/A+(c-y)/B
  by_cases hcy : y≤c
  · exact add_nonneg (div_nonneg (by linarith) ha.le) (div_nonneg (by linarith) hb.le)
  have h4 : 1≤4*c^2 := by nlinarith [sq_nonneg (c-1/2)]
  have hy2 := pow_le_pow_left₀ hy hy' 2
  have hpoly : 0≤4*c*y*(4*c^2+r^2-1-y^2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hy) (by linarith)
  have sq : ((y-c)*A)^2≤((c+y)*B)^2 := by
    rw [mul_pow,mul_pow,a2,b2]
    dsimp [orbitOffset]
    nlinarith only [hpoly]
  have hcross := le_of_sq_le_sq sq (mul_nonneg (by linarith) hb.le)
  have hfrac := (div_le_div_iff₀ hb ha).mpr hcross
  rw [show c-y=-(y-c) by ring,neg_div]
  linarith only [hfrac]

theorem period_numerator_pos {c r : ℝ} (hc : 0<c) (hc' : c<1) (hr : 0<r)
    (turn : 2*c*r^2=1+c-2*c^3) :
    0 < ∫ θ in 0..π, (c+r*cos θ)/√((2*c+r*cos θ)^2+(2*c^2+r^2-1)) := by
  have hd : 0<orbitOffset c r := by
    have e : 2*c*orbitOffset c r=2*c^3+(1-c) := by unfold orbitOffset; nlinarith only [turn]
    have p : 0<2*c*orbitOffset c r := by rw [e]; positivity
    exact (mul_pos_iff_of_pos_left (by positivity : 0<2*c)).mp p
  let g : ℝ → ℝ := fun θ => rawTerm c r (r*cos θ)
  let p : ℝ → ℝ := fun θ => rawTerm c r (r*cos θ)+rawTerm c r (-(r*cos θ))
  have cg : Continuous g := (raw_cont hd).comp (continuous_cos.const_mul r)
  have cg' : Continuous (fun θ => rawTerm c r (-(r*cos θ))) :=
    (raw_cont hd).comp (continuous_cos.const_mul r).neg
  have cp : Continuous p := cg.add cg'
  have flip : (fun x => g (π-x))=(fun x => rawTerm c r (-(r*cos x))) := by
    funext x
    simp [g,cos_pi_sub]
  have sub := intervalIntegral.integral_comp_sub_left (a:=0) (b:=π/2) g π
  rw [flip,show π-π/2=π/2 by ring,sub_zero] at sub
  have hsum := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (cg.intervalIntegrable 0 (π/2)) (cg.intervalIntegrable (π/2) π)
  have pair_eq : (∫ θ in 0..π/2,p θ) = ∫ θ in 0..π,g θ := by
    exact (intervalIntegral.integral_add (cg.intervalIntegrable 0 (π/2))
         (cg'.intervalIntegrable 0 (π/2))).trans (by rw [sub,hsum])
  change 0<∫ θ in 0..π,g θ
  rw [← pair_eq]
  by_cases hlow : c≤1/2
  · have ep : p=(fun θ => (c/r)*angular c θ) := by
      funext θ
      rw [show p θ=_ from low_pair hc hlow hr turn]
      dsimp [angular]
      ring
    rw [ep,intervalIntegral.integral_const_mul]
    exact mul_pos (div_pos hc hr) (lt_trans (by positivity) (angular_mean_lower hc.le hlow))
  · have hn (θ : ℝ) (hθ : θ∈Ioc 0 (π/2)) : 0≤p θ := by
      apply high_pair (by linarith) (mul_nonneg hr.le (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos,hθ.1],hθ.2⟩))
        (by simpa using mul_le_mul_of_nonneg_left (cos_le_one θ) hr.le) hd
    have pos : 0<p (π/2) := by
      simp only [p,cos_pi_div_two,mul_zero,neg_zero,rawTerm,add_zero]
      positivity
    have strict := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (f:=fun _ : ℝ => (0:ℝ)) (g:=p) (show 0<π/2 by positivity)
      continuous_const.continuousOn cp.continuousOn hn
      ⟨π/2,⟨by positivity,le_rfl⟩,pos⟩
    simpa only [intervalIntegral.integral_zero] using strict

def quarticPotential (x : ℝ) := (x^4-x^2-2*x)/8

/-- Two distinct turning values at one potential energy give all hypotheses
of the period numerator theorem directly. -/
theorem period_numerator_pos_of_equal_potential {c r : ℝ} (hr : 0<r)
    (he : quarticPotential (c+r)=quarticPotential (c-r)) :
    0 < ∫ θ in 0..π, (c+r*cos θ)/√((2*c+r*cos θ)^2+(2*c^2+r^2-1)) := by
  have ej : r*(2*c*r^2-(1+c-2*c^3))=0 := by
    dsimp [quarticPotential] at he
    nlinarith only [he]
  have turn := sub_eq_zero.mp ((mul_eq_zero.mp ej).resolve_left hr.ne')
  have poly : 0<2*c^2+2*c+1 := by nlinarith [sq_nonneg (c+1/2)]
  have fact : 2*c*r^2=(1-c)*(2*c^2+2*c+1) := by linarith only [turn]
  have hc : 0<c := by
    by_contra! h
    have lhs := mul_nonpos_of_nonpos_of_nonneg (by linarith only [h] : 2*c≤0) (sq_nonneg r)
    have rhs := mul_pos (by linarith only [h] : 0<1-c) poly
    linarith only [fact,lhs,rhs]
  have h1 : c<1 := by
    have lhs : 0<2*c*r^2 := by positivity
    rw [fact] at lhs
    linarith only [(mul_pos_iff_of_pos_right poly).mp lhs]
  exact period_numerator_pos hc h1 hr turn

end LengthGrowth.OscillatorMean

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms `LengthGrowth.OscillatorMean.period_numerator_pos_of_equal_potential) do
    unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
      throwError "Unexpected axiom {ax} in complete period numerator"
  logInfo "OSCILLATOR_PERIOD_AUDIT: original full-angle period numerator for all admissible turning data."
