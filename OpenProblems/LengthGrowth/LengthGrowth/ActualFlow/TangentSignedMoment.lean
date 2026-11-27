import LengthGrowth.ActualFlow.TangentFourierMoment
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Set Real MeasureTheory
theorem coeff_add {f g : ℝ→ℂ} (cf : Continuous f) (cg : Continuous g) (n : ℤ) :
    coeff (fun x=>f x+g x) n=coeff f n+coeff g n := by
  have ci (z : ℝ→ℂ) (cz : Continuous z) : IntervalIntegrable
      (fun x : ℝ=>fourier (-n) (x : AddCircle ((1:ℝ)-0)) • z x) volume 0 1 :=
    (show Continuous (fun x : ℝ=>fourier (-n) (x : AddCircle ((1:ℝ)-0)) • z x) by fun_prop).intervalIntegrable _ _
  simp only [coeff,fourierCoeffOn_eq_integral,smul_add]
  rw [intervalIntegral.integral_add (ci f cf) (ci g cg),smul_add]
/-- The signed first moment is the geometric signed turning integral of
the actual unit circle-valued tangent, normalized to arclength period one. -/
theorem signed_moment {T V : ℝ→ℂ} {K : ℝ→ℝ} (T' : ∀x,HasDerivAt T (V x) x)
    (cV : Continuous V) (per : T 1=T 0) (unit : ∀x,‖T x‖=1)
    (frenet : ∀x,V x=(K x:ℂ)*Complex.I*T x) :
    HasSum (fun n : ℤ=>omega n*energy T n) (∫u in 0..1,K u) := by
  have cT : Continuous T:=continuous_iff_continuousAt.mpr fun x=>(T' x).continuousAt
  let G (s : ℝ) := fun x=>V x+((s:ℂ)*Complex.I)*T x
  have cg (s : ℝ) : Continuous (G s) := cV.add (continuous_const.mul cT)
  have coefficient (s : ℝ) (n : ℤ) : coeff (G s) n=((omega n+s:ℝ):ℂ)*Complex.I*coeff T n := by
    rw [show G s=(fun x=>V x+((s:ℂ)*Complex.I)*T x) by rfl,coeff_add (g:=fun x=>((s:ℂ)*Complex.I)*T x) cV (continuous_const.mul cT)]
    change coeff V n+fourierCoeffOn _ (fun x=>((s:ℂ)*Complex.I)*T x) n=_
    rw [fourierCoeffOn.const_mul,coeff_der T' cV per]
    change _*_*coeff T n+_*coeff T n=_
    push_cast;ring
  have physical (s u : ℝ) : ‖G s u‖^2=(K u+s)^2 := by
    have eq : G s u=((K u+s:ℝ):ℂ)*Complex.I*T u := by dsimp only [G];rw [frenet];push_cast;ring
    simp only [eq,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,unit,mul_one,sq_abs]
  have freq (s : ℝ) (n : ℤ) : energy (G s) n=(omega n+s)^2*energy T n := by
    simp only [energy,coefficient,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,mul_pow,sq_abs]
  have h : HasSum (fun n : ℤ=> (1/4:ℝ)*(energy (G 1) n-energy (G (-1)) n))
      ((1/4:ℝ)*((∫u in 0..1,‖G 1 u‖^2)-(∫u in 0..1,‖G (-1) u‖^2))) :=
    ((parseval (G 1) (cg 1)).sub (parseval (G (-1)) (cg (-1)))).mul_left _
  convert! h using 1
  · funext n;rw [freq,freq];ring
  · calc
      (∫u in 0..1,K u) = ∫u in (0:ℝ)..1,(1/4:ℝ)*(‖G 1 u‖^2-‖G (-1) u‖^2) := by
        apply intervalIntegral.integral_congr
        intro u _;change K u=(1/4)*(‖G 1 u‖^2-‖G (-1) u‖^2);rw [physical,physical];ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub]
        · exact (show Continuous (fun u=>‖G 1 u‖^2) from (cg 1).norm.pow 2).intervalIntegrable (μ:=volume) 0 1
        · exact (show Continuous (fun u=>‖G (-1) u‖^2) from (cg (-1)).norm.pow 2).intervalIntegrable (μ:=volume) 0 1
end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.signed_moment
