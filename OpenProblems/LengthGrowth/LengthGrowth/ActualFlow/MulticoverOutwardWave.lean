import LengthGrowth.ActualFlow.MulticoverOutwardAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
namespace LengthGrowth.Multicover.Outward

/-- The integral on every interval differs from its mean times the interval
length by at most one fixed constant. -/
def Mean (f : Fn) (a:ℝ) := ∃B:ℝ,∀x y:ℝ,|(∫s in x..y,f s)-(y-x)*a|≤B

theorem mean_const (a:ℝ) : Mean (ContinuousMap.const ℝ a) a:=by
  refine ⟨0,fun x y=>?_⟩
  simp [smul_eq_mul]

theorem Mean.add {f g:Fn} {a b:ℝ} (hf:Mean f a) (hg:Mean g b) : Mean (f+g) (a+b):=by
  obtain ⟨C,hC⟩:=hf
  obtain ⟨D,hD⟩:=hg
  refine ⟨C+D,fun x y=>?_⟩
  change |(∫s in x..y,f s+g s)-(y-x)*(a+b)|≤C+D
  rw [intervalIntegral.integral_add (f.continuous.intervalIntegrable ..) (g.continuous.intervalIntegrable ..)]
  calc
    _=|((∫s in x..y,f s)-(y-x)*a)+((∫s in x..y,g s)-(y-x)*b)|:=by congr 1;ring
    _≤_ := (abs_add_le ..).trans (add_le_add (hC x y) (hD x y))

theorem Mean.scale {f:Fn} {a:ℝ} (hf:Mean f a) (k:ℝ):Mean (k • f) (k*a):=by
  obtain ⟨C,hC⟩:=hf
  refine ⟨|k| *C,fun x y=>?_⟩
  change |(∫s in x..y,k*f s)-(y-x)*(k*a)|≤_
  rw [intervalIntegral.integral_const_mul,show k*(∫s in x..y,f s)-(y-x)*(k*a)=k*((∫s in x..y,f s)-(y-x)*a) by ring,abs_mul]
  exact mul_le_mul_of_nonneg_left (hC x y) (abs_nonneg _)

def harmonic (n:ℝ) : Fn:=⟨fun s=>Real.cos (n*(3/4*s)),by fun_prop⟩

theorem harmonic_mean (n:ℝ) (hn:n≠0) : Mean (harmonic n) 0:=by
  let w:=n*(3/4)
  have nz : w≠0:=by dsimp [w];positivity
  refine ⟨2/|w|,fun x y=>?_⟩
  have der (s:ℝ) : HasDerivAt (fun t=>Real.sin (w*t)/w) (harmonic n s) s:=by
    apply (((hasDerivAt_id s).const_mul w).sin.div_const w).congr_deriv
    change Real.cos (w*s)*(w*1)/w=Real.cos (n*(3/4*s))
    rw [show n*(3/4*s)=w*s by dsimp [w];ring]
    field_simp
  have eq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=x) (b:=y) (fun s _=>der s)
    ((harmonic n).continuous.intervalIntegrable x y)
  rw [eq,mul_zero,sub_zero,←sub_div,abs_div]
  apply div_le_div_of_nonneg_right _ (abs_nonneg _)
  exact abs_le.mpr ⟨by linarith only [Real.neg_one_le_sin (w*y),Real.sin_le_one (w*x)],by linarith only [Real.sin_le_one (w*y),Real.neg_one_le_sin (w*x)]⟩

def wave : Fn:=(3/2:ℝ) • harmonic 1

def waveForce : Fn:=(27/64:ℝ) • (harmonic 1+harmonic 3)

theorem wave_second_force (s:ℝ) : deriv (deriv (fun s=>wave s)) s+(wave s)^3/2=waveForce s:=by
  let t:=3/4*s
  have dt (x:ℝ):HasDerivAt (fun y:ℝ=>3/4*y) (3/4) x:=by simpa using (hasDerivAt_id x).const_mul (3/4:ℝ)
  have dx (x:ℝ) : HasDerivAt (fun s=>wave s) (-(9/8)*Real.sin (3/4*x)) x:=by
    change HasDerivAt (fun s=>3/2*Real.cos (1*(3/4*s))) _ x
    simp only [one_mul]
    apply (((dt x).cos).const_mul (3/2:ℝ)).congr_deriv
    ring
  rw [show deriv (fun s=>wave s)=(fun x=> -(9/8)*Real.sin (3/4*x)) by funext x;exact (dx x).deriv]
  rw [((dt s).sin.const_mul (-(9/8):ℝ)).deriv]
  change -(9/8)*(Real.cos t*(3/4))+((3/2)*Real.cos (1*t))^3/2=(27/64)*(Real.cos (1*t)+Real.cos (3*t))
  rw [one_mul,Real.cos_three_mul];ring

private theorem modes (s:ℝ) :
    (harmonic 1 s)^2=(1+harmonic 2 s)/2 ∧ harmonic 1 s*harmonic 3 s=(harmonic 2 s+harmonic 4 s)/2 ∧
    (harmonic 3 s)^2=(1+harmonic 6 s)/2:=by
  let t:=3/4*s
  change Real.cos (1*t)^2=(1+Real.cos (2*t))/2 ∧ Real.cos (1*t)*Real.cos (3*t)=(Real.cos (2*t)+Real.cos (4*t))/2 ∧
    Real.cos (3*t)^2=(1+Real.cos (6*t))/2
  rw [one_mul]
  constructor
  · rw [Real.cos_two_mul];ring
  constructor
  · rw [show 2*t=3*t-t by ring,show 4*t=3*t+t by ring,Real.cos_sub,Real.cos_add];ring
  · rw [show 6*t=2*(3*t) by ring,Real.cos_two_mul];ring

def waveMoments : Integrals:=⟨0,9/8,81/256,729/4096⟩

theorem wave_means :
    Mean wave waveMoments.turn ∧ Mean (wave^2) waveMoments.square ∧
    Mean (wave*waveForce) waveMoments.rate ∧ Mean (waveForce^2) waveMoments.diss:=by
  let one:=ContinuousMap.const ℝ (1:ℝ)
  have h1:=harmonic_mean 1 (by norm_num)
  have h2:=harmonic_mean 2 (by norm_num)
  have h4:=harmonic_mean 4 (by norm_num)
  have h6:=harmonic_mean 6 (by norm_num)
  have ho : Mean one 1:=mean_const 1
  refine ⟨?_,?_,?_,?_⟩
  · simpa [wave,waveMoments] using h1.scale (3/2)
  · have eq : wave^2=(9/8:ℝ) • (one+harmonic 2):=by
      ext s
      simp only [wave,ContinuousMap.pow_apply,ContinuousMap.smul_apply,ContinuousMap.add_apply,smul_eq_mul]
      change ((3/2:ℝ)*harmonic 1 s)^2=9/8*(1+harmonic 2 s)
      linarith only [(modes s).1]
    rw [eq];simpa [waveMoments] using (ho.add h2).scale (9/8)
  · have eq : wave*waveForce=(81/256:ℝ) • (one+(2:ℝ) • harmonic 2+harmonic 4):=by
      ext s
      change ((3/2:ℝ)*harmonic 1 s)*(27/64*(harmonic 1 s+harmonic 3 s))=81/256*(1+2*harmonic 2 s+harmonic 4 s)
      linarith only [(modes s).1,(modes s).2.1]
    rw [eq];simpa [waveMoments] using ((ho.add (h2.scale 2)).add h4).scale (81/256)
  · have eq : waveForce^2=(729/4096:ℝ) • (one+(3/2:ℝ) • harmonic 2+harmonic 4+(1/2:ℝ) • harmonic 6):=by
      ext s
      change (27/64*(harmonic 1 s+harmonic 3 s))^2=729/4096*(1+3/2*harmonic 2 s+harmonic 4 s+1/2*harmonic 6 s)
      linarith only [(modes s).1,(modes s).2.1,(modes s).2.2]
    rw [eq];simpa [waveMoments] using (((ho.add (h2.scale (3/2))).add h4).add (h6.scale (1/2))).scale (729/4096)

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.wave_means
