import Lemniscate.PeriodicCjRescaling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Sobolev height decay and the quadratic phase tail give standard C^j
convergence of the actual normal graph in the physical curve parameter.

-/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff

private theorem rotation_difference_le_angle (θ φ : ℝ) :
    ‖Complex.exp (I*(θ:ℂ))-Complex.exp (I*(φ:ℂ))‖≤|θ-φ| := by
  have harg : I*(φ:ℂ)+I*((θ-φ:ℝ):ℂ)=I*(θ:ℂ) := by push_cast; ring
  have hfactor : Complex.exp (I*(θ:ℂ))-Complex.exp (I*(φ:ℂ))=
      Complex.exp (I*(φ:ℂ))*(Complex.exp (I*((θ-φ:ℝ):ℂ))-1) := by
    rw [mul_sub,← Complex.exp_add,mul_one,harg]
  rw [hfactor,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  simpa only [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ-φ))

private theorem convergence_scalar_bound
    (r d A B μ t X : ℝ) (hr : 0≤r) (hA : 0<A) (hB : 0≤B)
    (hμ : 0<μ) (ht : 0≤t) (hX : X∈Icc (0:ℝ) 1)
    (hrsq : r^2≤A*Real.exp (-2*μ*t)*X^2)
    (hd : d≤B*Real.exp (-2*μ*t)*X^2) :
    r+d≤(Real.sqrt A+B+1)*Real.exp (-μ*t)*X := by
  let e : ℝ := Real.exp (-μ*t)
  let y : ℝ := e*X
  have he0 : 0≤e := (Real.exp_pos _).le
  have he1 : e≤1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hμ.le) ht)
  have hy0 : 0≤y := mul_nonneg he0 hX.1
  have hyX : y≤X := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he1 hX.1
  have hy1 : y≤1 := hyX.trans hX.2
  have he2 : Real.exp (-2*μ*t)=e^2 := by
    dsimp only [e]
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hsqrt : (Real.sqrt A)^2=A := Real.sq_sqrt hA.le
  have hsq : r^2≤(Real.sqrt A*y)^2 := hrsq.trans_eq (by
    rw [he2,mul_pow,hsqrt]
    dsimp only [y]
    ring)
  have hrbound : r≤Real.sqrt A*y :=
    (sq_le_sq₀ hr (mul_nonneg (Real.sqrt_nonneg A) hy0)).mp hsq
  have hdquad : d≤B*y^2 := hd.trans_eq (by rw [he2]; dsimp only [y]; ring)
  have hysq : y^2≤y := by
    simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left hy1 hy0
  have hdbound : d≤B*y := hdquad.trans (mul_le_mul_of_nonneg_left hysq hB)
  calc
    r+d≤Real.sqrt A*y+B*y := add_le_add hrbound hdbound
    _=(Real.sqrt A+B)*y := by ring
    _≤(Real.sqrt A+B+1)*y := mul_le_mul_of_nonneg_right (by linarith) hy0
    _=(Real.sqrt A+B+1)*Real.exp (-μ*t)*X := by dsimp only [y,e]; ring

variable (T : ℝ) [Fact (0<T)]

/-- Squared Sobolev height decay and a quadratic phase tail imply the
physical-parameter C^j convergence estimate. The constant is independent
of the solution, phase, decay rate, time and initial size X. -/
theorem normal_graph_convergence_estimate
    (j : ℕ) (β ν : ℝ → ℂ)
    (hβ : ContDiff ℝ (j : ℕ∞ω) β) (hν : ContDiff ℝ (j : ℕ∞ω) ν)
    (hβper : Function.Periodic β T) (hνper : Function.Periodic ν T)
    (a : ℝ) (ha : a≠0) (A B : ℝ) (hA : 0<A) (hB : 0≤B) :
    ∃ C>0, ∀ (f : CircleSobolevSpace T (j+1)) (θ θlim t μ X : ℝ),
      0<μ → 0≤t → X∈Icc (0:ℝ) 1 →
      ‖f‖^2≤A*Real.exp (-2*μ*t)*X^2 →
      |θ-θlim|≤B*Real.exp (-2*μ*t)*X^2 →
      let D := circleSobolevClassicalJet T j f
      let h : ℝ → ℂ := fun x => D 0 (x:AddCircle T)
      periodicCjNorm j (fun s =>
        Complex.exp (I*(θ:ℂ))*(β (a*s)+h (a*s)*ν (a*s))-
          Complex.exp (I*(θlim:ℂ))*β (a*s))≤C*Real.exp (-μ*t)*X := by
  obtain ⟨Cj,hCj,hEstimate⟩ := normal_graph_cj_estimate T j β ν hβ hν hβper hνper
  let M : ℝ := (max 1 |a|)^j
  have hM : 0<M := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 |a|)) j
  let C : ℝ := M*Cj*(Real.sqrt A+B+1)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro f θ θlim t μ X hμ ht hX hf hθ
  let z : ℂ := Complex.exp (I*(θ:ℂ))
  let w : ℂ := Complex.exp (I*(θlim:ℂ))
  let D := circleSobolevClassicalJet T j f
  let h : ℝ → ℂ := fun x => D 0 (x:AddCircle T)
  let E : ℝ → ℂ := fun x => z*(β x+h x*ν x)-w*β x
  have hz : ‖z‖=1 := Complex.norm_exp_I_mul_ofReal θ
  have hcurve : periodicCjNorm j E≤Cj*(‖f‖+‖z-w‖) :=
    (hEstimate f z w hz).2.2
  have hrotation : ‖z-w‖≤B*Real.exp (-2*μ*t)*X^2 :=
    (rotation_difference_le_angle θ θlim).trans hθ
  have hdecay : ‖f‖+‖z-w‖≤(Real.sqrt A+B+1)*Real.exp (-μ*t)*X :=
    convergence_scalar_bound ‖f‖ ‖z-w‖ A B μ t X (norm_nonneg f)
      hA hB hμ ht hX hf hrotation
  change periodicCjNorm j (fun s => E (a*s))≤C*Real.exp (-μ*t)*X
  calc
    _≤M*periodicCjNorm j E := (periodic_cj_norm_rescaling j E a ha).2
    _≤M*(Cj*(‖f‖+‖z-w‖)) := mul_le_mul_of_nonneg_left hcurve hM.le
    _≤M*(Cj*((Real.sqrt A+B+1)*Real.exp (-μ*t)*X)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay hCj.le) hM.le
    _=C*Real.exp (-μ*t)*X := by dsimp only [C]; ring

end Lemniscate
