import SolitonClassification.RationalIndicialJet
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Derivative

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Polynomial Filter Set
open scoped Topology Polynomial
namespace ClosedSimilarity.RationalCurvature

/-- The actual principal coefficient at an ordinary pole of the complexified
arclength ODE. Both possible squares are retained. -/
theorem simple_pole_symbol {μ x A a b : ℂ} {f : ℂ→ℂ}
    (j : Jet f x (-1) A) (germ : residual μ a b f=ᶠ[𝓝[≠] x] fun _=>0) :
    A^2*(A^2+4*(μ*x)^2)*(A^2+9*(μ*x)^2)=0 := by
  have J := FourJet.at_point (μ:=μ) j
  have q₂ : Jet (quadratic μ f) x (-6) (36*(μ*x)^4*A^2) := by
    apply J.jquadratic.retag <;> norm_num
    ring
  have q₄ : Jet (quartic μ f) x (-6) (13*(μ*x)^2*A^4) := by
    apply J.jquartic.retag <;> norm_num
    ring
  have j6 : Jet (fun z=>f z^6) x (-6) (A^6) := (j.pow 6).retag (by norm_num) rfl
  have j2 := ((j.pow 2).smul (2*a)).weaken (m:=(-6:ℤ)) (by norm_num)
  have j1 := (J.j₁.smul (2*b)).weaken (m:=(-6:ℤ)) (by norm_num)
  have hz := ((((q₂.add q₄).add j6).sub j2).sub j1).eq_zero_of_germ_zero germ
  linear_combination hz

theorem real_residue {w : ℝ} {x A a b : ℂ} {f : ℂ→ℂ}
    (j : Jet f x (-1) A) (hn : A≠0)
    (germ : residual ((w:ℂ)*I) a b f=ᶠ[𝓝[≠] x] fun _=>0) :
    A=(2*w:ℝ)*x ∨ A=(-(2*w):ℝ)*x ∨ A=(3*w:ℝ)*x ∨ A=(-(3*w):ℝ)*x := by
  have h := simple_pole_symbol j germ
  have factor : (A-(2*w:ℝ)*x)*(A+(2*w:ℝ)*x)*(A-(3*w:ℝ)*x)*(A+(3*w:ℝ)*x)=0 := by
    have nz := pow_ne_zero 2 hn
    have hz : (A^2+4*((w:ℂ)*I*x)^2)*(A^2+9*((w:ℂ)*I*x)^2)=0 :=
      (mul_eq_zero.mp (by simpa only [mul_assoc] using h : A^2*
        ((A^2+4*((w:ℂ)*I*x)^2)*(A^2+9*((w:ℂ)*I*x)^2))=0)).resolve_left nz
    push_cast
    rw [mul_pow,mul_pow,Complex.I_sq] at hz
    linear_combination hz
  rcases mul_eq_zero.mp factor with h|h
  · rcases mul_eq_zero.mp h with h|h
    · rcases mul_eq_zero.mp h with h|h
      · exact Or.inl (sub_eq_zero.mp h)
      · right; left
        push_cast at *
        linear_combination h
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
  · right; right; right
    push_cast at *
    linear_combination h

/-- The total polynomial quotient is used only off its isolated poles. -/
def quotient (A B : ℂ[X]) (z : ℂ) : ℂ := A.eval z/B.eval z

theorem quotient_pole_jet {A B : ℂ[X]} (Bn : B≠0) (x : ℂ) :
    ∃ G : ℂ[X], B=(X-C x)^B.rootMultiplicity x*G ∧ G.eval x≠0 ∧
      Jet (quotient A B) x (-(B.rootMultiplicity x : ℤ)) (A.eval x/G.eval x) := by
  obtain ⟨G,eq,nd⟩ := B.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Bn x
  have gn : G.eval x≠0 := fun hz => nd (dvd_iff_isRoot.mpr hz)
  refine ⟨G,eq,gn,fun z=>A.eval z/G.eval z,?_,rfl,?_⟩
  · exact ((AnalyticOnNhd.eval_polynomial A) x (mem_univ x)).div
      ((AnalyticOnNhd.eval_polynomial G) x (mem_univ x)) gn
  · filter_upwards [eventually_mem_nhdsWithin] with z nz
    simp only [quotient,congrArg (Polynomial.eval z) eq,eval_mul,eval_pow,eval_sub,
      eval_X,eval_C,zpow_neg,zpow_natCast,div_eq_mul_inv,mul_inv_rev]
    ring

private theorem coprime_at_root {A B : ℂ[X]} (cop : IsCoprime A B) {x : ℂ} (root : B.eval x=0) :
    A.eval x≠0 := by
  intro zero
  obtain ⟨U,V,h⟩ := cop
  have hh := congrArg (Polynomial.eval x) h
  simp [zero,root] at hh

/-- The physical rational curvature has no pole at the Euler singularity. -/
theorem denominator_at_zero {A B : ℂ[X]} (Bn : B≠0) (cop : IsCoprime A B) {μ a b : ℂ}
    (germ : residual μ a b (quotient A B)=ᶠ[𝓝[≠] (0:ℂ)] fun _=>0) : B.eval 0≠0 := by
  intro hz
  obtain ⟨G,fac,gn,jet⟩ := quotient_pole_jet (A:=A) Bn 0
  have mn : B.rootMultiplicity 0≠0 := by
    intro m
    rw [m,pow_zero,one_mul] at fac
    exact gn (fac ▸ hz)
  exact div_ne_zero (coprime_at_root cop hz) gn
    (cannot_pole_at_zero jet germ (by omega))

/-- Every denominator root of an actual reduced polynomial quotient solving
the ODE is simple. Its residue divided by the root is a real integer
multiple of the physical frequency. -/
theorem denominator_root_data {A B : ℂ[X]} (Bn : B≠0) (cop : IsCoprime A B)
    {w : ℝ} {x a b : ℂ} (root : B.eval x=0)
    (germ : residual ((w:ℂ)*I) a b (quotient A B)=ᶠ[𝓝[≠] x] fun _=>0) :
    B.rootMultiplicity x=1 ∧ B.derivative.eval x≠0 ∧
    ∃ r : ℝ,A.eval x/B.derivative.eval x=(r:ℂ)*x := by
  obtain ⟨G,fac,gn,jet⟩ := quotient_pole_jet (A:=A) Bn x
  have an := coprime_at_root cop root
  have bn := div_ne_zero an gn
  have pos : B.rootMultiplicity x ≠0 := by
    intro zero
    rw [zero,pow_zero,one_mul] at fac
    exact gn (fac ▸ root)
  have mult : B.rootMultiplicity x=1 := by
    by_contra ne
    exact bn (cannot_higher_pole jet germ (by omega))
  rw [mult,pow_one] at fac
  have slope : B.derivative.eval x=G.eval x := by
    rw [fac,Polynomial.derivative_mul]
    simp
  rw [mult] at jet
  have j : Jet (quotient A B) x (-1) (A.eval x/G.eval x) := by simpa using jet
  refine ⟨mult,slope ▸ gn,?_⟩
  rw [slope]
  rcases real_residue j bn germ with h|h|h|h
  · exact ⟨_,h⟩
  · exact ⟨_,h⟩
  · exact ⟨_,h⟩
  · exact ⟨_,h⟩

end ClosedSimilarity.RationalCurvature
