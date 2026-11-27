import LengthGrowth.ActualFlow.MulticoverLengthWindow

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Topology Set
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- In the initial multicover sublevel the leading physical-time constant
is that of the expanding circle with the same signed turning multiplicity. -/
theorem multicover_sharp_length_limit (hf : c.IsNormalFEF)
    (turn : 6≤c.initialAbsoluteTurning) (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) :
    Tendsto (fun t => c.length t^4/t) atTop (𝓝 (2*c.initialAbsoluteTurning^4)) := by
  let H := c.normalizedProduct
  let S := fun t => c.length t^4
  let M := c.initialLengthEnvelope
  let P := c.initialAbsoluteTurning^2/2
  let R := 2*c.initialAbsoluteTurning^4
  let i := fun x : ℝ => x⁻¹
  let q := fun x => S (x^2)*(i x)^2
  have hi : Tendsto i atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hs : Tendsto (fun x : ℝ => x^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hH : Tendsto H atTop (𝓝 P) := by
    have h := ((c.multicover_oscillation_limit hf turn initial).add_const (c.initialAbsoluteTurning^2)).div_const 2
    convert h using 1
    · funext t; dsimp only [H,multicoverOscillation]; ring
    · simp [P]
  have diff : Tendsto (fun x => H x-H (x^2)) atTop (𝓝 0) := by
    simpa only [sub_self,Function.comp_apply] using hH.sub (hH.comp hs)
  have sq0 : Tendsto (fun x => S x*(i x)^2) atTop (𝓝 0) := by
    have up : Tendsto (fun x => M*((i x)^2+i x)) atTop (𝓝 0) := by
      simpa only [zero_pow (by decide : 2≠0),zero_add,mul_zero] using ((hi.pow 2).add hi).const_mul M
    apply squeeze_zero' _ _ up
    · exact Eventually.of_forall (fun x => mul_nonneg (by dsimp [S]; positivity) (sq_nonneg _))
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      have bound := mul_le_mul_of_nonneg_right (c.multicover_envelope hf turn initial hx.le) (sq_nonneg (i x))
      have inv : (1+x)*(i x)^2=(i x)^2+i x := by dsimp [i]; field_simp
      change S x*(i x)^2≤M*(1+x)*(i x)^2 at bound
      rwa [mul_assoc,inv] at bound
  let f := fun x => 1-i x
  let j := fun x => 1+(i x)^2
  have lf : Tendsto f atTop (𝓝 1) := by simpa [f] using (tendsto_const_nhds (x:=(1:ℝ))).sub hi
  have lj : Tendsto j atTop (𝓝 1) := by simpa [j] using (tendsto_const_nhds (x:=(1:ℝ))).add (hi.pow 2)
  have sqrtlim : Tendsto (fun x=>Real.sqrt (c.multicoverOscillation x)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp (c.multicover_oscillation_limit hf turn initial)
  have speedlim : Tendsto c.multiLowerSpeed atTop (𝓝 R):=by
    change Tendsto (fun x:ℝ=>R/(1+Real.sqrt (c.multicoverOscillation x))^4) atTop (𝓝 R)
    have h:=(tendsto_const_nhds (x:=R)).div (((tendsto_const_nhds (x:=(1:ℝ))).add sqrtlim).pow 4) (by norm_num)
    simpa only [Pi.div_def,multiLowerSpeed,R,add_zero,one_pow,div_one] using h
  let low := fun x => S x*(i x)^2+c.multiLowerSpeed x*f x-(8*M)*j x*(H x-H (x^2))
  let high := fun η x => S x*(i x)^2+(2*(2*H x)^2+4*η)*f x+
    ((2*H 0/η)*M)*j x*(H x-H (x^2))
  have lLow : Tendsto low atTop (𝓝 R) := by
    simpa only [low,mul_one,zero_add,mul_zero,sub_zero] using
      (sq0.add (speedlim.mul lf)).sub ((lj.const_mul (8*M)).mul diff)
  have lHi (η : ℝ) : Tendsto (high η) atTop (𝓝 (R+4*η)) := by
    have lim := (sq0.add (((((hH.const_mul 2).pow 2).const_mul 2).add_const (4*η)).mul lf)).add
      ((lj.const_mul ((2*H 0/η)*M)).mul diff)
    have val : 0+(2*(2*P)^2+4*η)*1+(2*H 0/η*M)*1*0=R+4*η := by dsimp only [P,R]; ring
    exact val ▸ lim
  have squeeze (η : ℝ) (hp : 0<η) : ∀ᶠ x in atTop, low x≤q x ∧ q x≤high η x := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    have xp : 0<x := by linarith
    have lt : x<x^2 := by nlinarith only [mul_pos xp (sub_pos.mpr hx)]
    have window := c.multi_length_window hf turn initial xp.le lt hp
    dsimp only at window
    have i0 : 0≤(i x)^2 := sq_nonneg _
    have a := mul_le_mul_of_nonneg_right window.1 i0
    have b := mul_le_mul_of_nonneg_right window.2 i0
    have w1 : (x^2-x)*(i x)^2=f x := by dsimp only [i,f]; field_simp
    have w2 : (1+x^2)*(i x)^2=j x := by dsimp only [i,j]; field_simp; ring
    change (c.multiLowerSpeed x*(x^2-x)-8*(M*(1+x^2))*(H x-H (x^2)))*(i x)^2≤(S (x^2)-S x)*(i x)^2 at a
    change (S (x^2)-S x)*(i x)^2≤((2*(2*H x)^2+4*η)*(x^2-x)+
      (2*H 0/η)*(M*(1+x^2))*(H x-H (x^2)))*(i x)^2 at b
    constructor
    · dsimp only [low,q]; rw [←w1,←w2]; linarith only [a]
    · dsimp only [high,q]; rw [←w1,←w2]; linarith only [b]
  have hq : Tendsto q atTop (𝓝 R) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [(tendsto_order.mp lLow).1 a ha,squeeze 1 (by norm_num)] with x hx hx'
      exact hx.trans_le hx'.1
    · intro a ha
      let η := (a-R)/8
      have hp : 0<η := by dsimp [η]; linarith
      have lim : R+4*η<a := by dsimp [η]; linarith
      filter_upwards [(lHi η).eventually_lt_const lim,squeeze η hp] with x hx hx'
      exact hx'.2.trans_lt hx
  have final := hq.comp Real.tendsto_sqrt_atTop
  change Tendsto _ atTop (𝓝 R)
  apply final.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  dsimp only [Function.comp_apply,q,i,S]
  rw [inv_pow,Real.sq_sqrt ht.le,div_eq_mul_inv]

theorem winding_sharp_length_limit (hf : c.IsNormalFEF) (m:ℕ) (hm:1≤m)
    (turn : c.initialAbsoluteTurning=2*Real.pi*(m:ℝ))
    (initial : 2*c.normalizedProduct 0-(2*Real.pi*(m:ℝ))^2≤12*Real.pi*(m:ℝ)/5+9/25) :
    Tendsto (fun t=>c.length t^4/t) atTop (𝓝 (2*(2*Real.pi*(m:ℝ))^4)) := by
  have m1 : (1:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have six : 6≤c.initialAbsoluteTurning:=by rw [turn];nlinarith only [m1,Real.pi_gt_three,mul_nonneg Real.pi_pos.le (sub_nonneg.mpr m1)]
  have cap : c.rootBending 0≤c.initialAbsoluteTurning+3/5:=by
    rw [turn]
    have a:=c.rootBending_sq (le_refl 0)
    have b : 0≤2*Real.pi*(m:ℝ):=by positivity
    nlinarith only [a,b,initial]
  simpa only [turn] using c.multicover_sharp_length_limit hf six cap
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_sharp_length_limit
