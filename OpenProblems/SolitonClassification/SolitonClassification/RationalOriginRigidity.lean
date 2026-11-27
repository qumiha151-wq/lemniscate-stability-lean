import SolitonClassification.RationalOriginVariation
import SolitonClassification.RationalPoleCoefficient
import Mathlib.Tactic.Positivity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Polynomial Filter Set
open scoped Topology Polynomial
namespace ClosedSimilarity.RationalCurvature

/-- A nontrivial positive-order zero of a solution is impossible at the
origin when dilation is nonzero. This also covers zero background curvature,
where the usual linearization degenerates. -/
theorem no_positive_zero {f : ℂ→ℂ} {μ a b v : ℂ} {n : ℤ} (hn : 0<n)
    (j : Jet f 0 n v) (μn : μ≠0) (an : a≠0)
    (germ : residual μ a b f=ᶠ[𝓝[≠] 0] fun _=>0) : v=0 := by
  by_contra vn
  have J := FourJet.at_zero (μ:=μ) j
  have h := ((((J.jquadratic.weaken (m:=n) (by omega)).add
    (J.jquartic.weaken (by omega))).add ((j.pow 6).weaken (by omega))).sub
    (((j.pow 2).smul (2*a)).weaken (by omega))).sub ((J.j₁.smul (2*b)).retag (sub_zero _) rfl)
  have first := h.eq_zero_of_germ_zero germ
  have char : (n:ℂ)≠0 := Int.cast_ne_zero.mpr (by omega)
  have bz : b=0 := by
    by_contra bn
    simp [bn,μn,char,vn] at first
  have q : Jet (quadratic μ f) 0 (2*n) 0 := by
    apply J.jquadratic.retag <;> push_cast <;> ring
  have j₂ : Jet (fun z=>2*a*f z^2) 0 (2*n) (2*a*v^2) := (j.pow 2).smul _
  have h' := ((q.add (J.jquartic.weaken (by omega))).add ((j.pow 6).weaken (by omega))).sub j₂
  have eq : (fun z=>quadratic μ f z+quartic μ f z+f z^6-2*a*f z^2)
      =ᶠ[𝓝[≠] 0] fun _=>0 := by
    filter_upwards [germ] with z hz
    simpa [residual,bz] using hz
  have second := h'.eq_zero_of_germ_zero eq
  simp [an,vn] at second

/-- No imaginary integer-frequency indicial root at a real nonzero circular
equilibrium. The rotation coefficient contributes only an imaginary term. -/
theorem circle_indicial_ne (c w b : ℝ) (n : ℤ) (cn : c≠0) :
    2*(c:ℂ)*(((w:ℂ)*I)*n)^4+5*(c:ℂ)^3*(((w:ℂ)*I)*n)^2-
    2*(b:ℂ)*(((w:ℂ)*I)*n)+4*(c:ℂ)^5≠0 := by
  intro h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.intCast_re,Complex.intCast_im,Complex.I_re,Complex.I_im,
    Complex.zero_re,pow_succ,pow_zero,
    Complex.re_ofNat,Complex.im_ofNat,mul_zero,zero_mul,add_zero,zero_add,sub_zero,one_mul,mul_one] at hr
  have mult : c*(2*((w*(n:ℝ))^4)-5*c^2*(w*(n:ℝ))^2+4*c^4)=0 := by
    linear_combination hr
  have no := (mul_eq_zero.mp mult).resolve_left cn
  have pc : 0<c^4 := by positivity
  nlinarith [sq_nonneg ((w*(n:ℝ))^2-5*c^2/4)]

theorem no_positive_variation {f : ℂ→ℂ} {c w a b : ℝ} {n : ℤ} {v : ℂ}
    (j : Variation f n c v) (hn : 0<n) (cn : c≠0)
    (constant : (c:ℂ)^6-2*(a:ℂ)*c^2=0)
    (germ : residual ((w:ℂ)*I) a b f=ᶠ[𝓝[≠] 0] fun _=>0) : v=0 := by
  have h := residual_variation j hn ((w:ℂ)*I) a b
  have eq : (fun z=>residual ((w:ℂ)*I) a b f z-((c:ℂ)^6-2*(a:ℂ)*c^2))
      =ᶠ[𝓝[≠] 0] fun _=>0 := by simpa [constant] using germ
  have zero := Jet.eq_zero_of_germ_zero h eq
  have nz : (c:ℂ)≠0 := by exact_mod_cast cn
  have fourth : (c:ℂ)^4=2*a := by
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp (show (c:ℂ)^2*(c^4-2*(a:ℂ))=0 by linear_combination constant)).resolve_left
    exact pow_ne_zero _ nz
  apply (mul_eq_zero.mp zero).resolve_left
  convert circle_indicial_ne c w b n cn using 2
  linear_combination 2*(c:ℂ)*fourth

/-- If the quotient differs from its value at zero, the genuine numerator
A-cB has a first nonzero Taylor coefficient. -/
theorem quotient_variation {A B : ℂ[X]} {c : ℂ} (bn : B.eval 0≠0)
    (ev : quotient A B 0=c) (nonconstant : A≠C c*B) :
    ∃ n : ℤ, 0<n ∧ ∃ v≠0,Variation (quotient A B) n c v := by
  let P := A-C c*B
  have pn : P≠0 := sub_ne_zero.mpr nonconstant
  have p0 : P.eval 0=0 := by
    dsimp [P]
    simp only [eval_sub,eval_mul,eval_C]
    exact sub_eq_zero.mpr ((div_eq_iff bn).mp ev)
  obtain ⟨G,fac,gd⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd pn 0
  have gn : G.eval 0≠0 := fun h => gd (dvd_iff_isRoot.mpr h)
  have pos : P.rootMultiplicity 0≠0 := by
    intro z
    rw [z,pow_zero,one_mul] at fac
    exact gn (fac ▸ p0)
  refine ⟨P.rootMultiplicity 0,by omega,G.eval 0/B.eval 0,div_ne_zero gn bn,?_⟩
  refine ⟨fun z=>G.eval z/B.eval z,
    ((AnalyticOnNhd.eval_polynomial G) 0 (mem_univ _)).div
      ((AnalyticOnNhd.eval_polynomial B) 0 (mem_univ _)) bn,rfl,?_⟩
  have con : ContinuousAt (fun z=>B.eval z) (0:ℂ) := ((AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) B) 0 (mem_univ _)).continuousAt
  have near := con.eventually_ne bn
  filter_upwards [near.filter_mono nhdsWithin_le_nhds] with z nz
  have eq := congrArg (Polynomial.eval z) fac
  change (A-C c*B).eval z=_ at eq
  simp only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,sub_zero] at eq
  simp only [quotient,sub_zero,zpow_natCast]
  field_simp [nz]
  linear_combination eq

/-- Regularity and reality at zero force the entire reduced rational
curvature to be constant, for arbitrary real rotational speed. -/
theorem constant_quotient_of_real_origin {A B : ℂ[X]} {w a b c : ℝ}
    (bn : B.eval 0≠0) (origin : quotient A B 0=c) (wa : w≠0) (aa : a≠0)
    (germ : residual ((w:ℂ)*I) a b (quotient A B)=ᶠ[𝓝[≠] 0] fun _=>0) : A=C (c:ℂ)*B := by
  by_contra neq
  obtain ⟨n,hn,v,vn,j⟩ := quotient_variation bn origin neq
  by_cases cz : c=0
  · subst c
    have h : Jet (quotient A B) 0 n v := by simpa [Variation] using j
    exact vn (no_positive_zero hn h (mul_ne_zero (by exact_mod_cast wa) Complex.I_ne_zero)
      (by exact_mod_cast aa) germ)
  · have analyticQ : AnalyticAt ℂ (quotient A B) 0 :=
      ((AnalyticOnNhd.eval_polynomial A) 0 (mem_univ _)).div
        ((AnalyticOnNhd.eval_polynomial B) 0 (mem_univ _)) bn
    have j0 := (Jet.of_analytic analyticQ).retag rfl origin
    exact vn (no_positive_variation j hn cz (residual_constant j0 germ) germ)

end ClosedSimilarity.RationalCurvature
