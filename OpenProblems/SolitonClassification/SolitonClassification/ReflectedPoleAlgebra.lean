import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! Finite coefficient identities for the arclength-curvature equation at a
complex pole. The input/output coefficient equations are explicit here;
analytic continuation and Nevanlinna estimates are separate results. -/
noncomputable section
namespace ClosedSimilarity.ReflectedPoleAlgebra

def intrinsic {K : Type*} [Field K] (k v w j l a omega : K) : K :=
  k*l-v*j+3/2*k^2*v^2+5/2*k^3*w+k^6/2-a*k^2-omega*v

theorem scalar_elimination (k v w j l a omega : ℂ) :
    k*(l+3*k*v^2+3/2*k^2*w)-v*(j+3/2*k^2*v+omega)
      +k^3*(w+k^3/2)-a*k^2 = intrinsic k v w j l a omega := by
  unfold intrinsic
  ring

theorem derivative_order_coefficient (c m : ℂ) :
    c*(m*(m+1)*(m+2)*(m+3)*c)-(-m*c)*(-m*(m+1)*(m+2)*c)
      =3*c^2*m*(m+1)*(m+2) := by ring

theorem simple_pole_leading (c : ℂ) :
    intrinsic c (-c) (2*c) (-6*c) (24*c) 0 0
      = c^2*(c^2+4)*(c^2+9)/2 := by unfold intrinsic; ring

theorem residue_squares {c : ℂ} (hc : c ≠ 0)
    (he : intrinsic c (-c) (2*c) (-6*c) (24*c) 0 0=0) :
    c^2 = -4 ∨ c^2 = -9 := by
  rw [simple_pole_leading] at he
  rcases (mul_eq_zero.mp ((div_eq_zero_iff.mp he).resolve_right (by norm_num))) with h | h
  · left
    have h' := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hc)
    linear_combination h'
  · exact Or.inr (by linear_combination h)

def indicial {K : Type*} [Field K] (σ j : K) : K :=
  let u := j-1
  u*(u-1)*(u-2)*(u-3)+24+u*(u-1)*(u-2)+6*u+
    3*σ*(1-u)+5/2*σ*(u*(u-1)+6)+3*σ^2

/-- Linear response of the leading five terms to the monomial with exponent j-1. -/
theorem linearized_pole (c j : ℂ) :
    let u := j-1
    c*u*(u-1)*(u-2)*(u-3)+24*c
      -(-c*u*(u-1)*(u-2)-6*c*u)
      +3/2*(2*c*(-c)^2+2*c^2*(-c)*u)
      +5/2*(3*c^2*(2*c)+c^3*u*(u-1))+3*c^5 = c*indicial (c^2) j := by
  dsimp [indicial]
  ring

theorem indicial_four {K : Type*} [Field K] [CharZero K] (j : K) :
    indicial (-4) j = (j+1)*(j-1)*(j-4)*(j-5) := by unfold indicial; ring

theorem indicial_nine {K : Type*} [Field K] [CharZero K] (j : K) :
    indicial (-9) j = (j+1)*(j-6)*(j^2-4*j-15/2) := by unfold indicial; ring

theorem first_three : indicial (-9:ℂ) 1=105 ∧ indicial (-9:ℂ) 2=138 ∧
    indicial (-9:ℂ) 3=126 := by norm_num [indicial]

theorem first_three_vanish {c d e f : ℂ} (hc : c ≠ 0)
    (h₁ : c*indicial (-9) 1*d=0)
    (h₂ : d=0 → c*indicial (-9) 2*e=0)
    (h₃ : d=0 → e=0 → c*indicial (-9) 3*f=0) : d=0 ∧ e=0 ∧ f=0 := by
  have hd : d=0 := by simpa [first_three.1,hc] using h₁
  have he : e=0 := by simpa [first_three.2.1,hc] using h₂ hd
  exact ⟨hd,he,by simpa [first_three.2.2,hc] using h₃ hd he⟩

private theorem quadratic_ne_zero (j : ℚ) : j^2-4*j-15/2 ≠ 0 := by
  intro h
  have hs : IsSquare (23/2:ℚ) := ⟨j-2,by nlinarith⟩
  have hd := (Rat.isSquare_iff.mp hs).2
  have hden : (23/2:ℚ).den=2 := by norm_num
  rw [hden] at hd
  exact Nat.prime_two.not_isSquare hd

theorem rational_resonances (j : ℚ) :
    (indicial (-4) j=0 ↔ j= -1 ∨ j=1 ∨ j=4 ∨ j=5) ∧
    (indicial (-9) j=0 ↔ j= -1 ∨ j=6) := by
  rw [indicial_four,indicial_nine]
  simp only [mul_eq_zero,quadratic_ne_zero j,or_false]
  simp only [sub_eq_zero,add_eq_zero_iff_eq_neg]
  tauto

theorem fractional_coefficient_vanish {j : ℚ} {σ : ℚ} {c u : ℂ}
    (hj : ∀ n : ℤ, j ≠ (n:ℚ)) (hσ : σ= -4 ∨ σ= -9) (hc : c ≠ 0)
    (he : c*(indicial σ j : ℚ)*u=0) : u=0 := by
  have hn : indicial σ j ≠ 0 := by
    intro h
    rcases hσ with rfl | rfl
    · rcases (rational_resonances j).1.mp h with h | h | h | h
      · exact hj (-1) (by simpa using h)
      · exact hj 1 (by simpa using h)
      · exact hj 4 (by simpa using h)
      · exact hj 5 (by simpa using h)
    · rcases (rational_resonances j).2.mp h with h | h
      · exact hj (-1) (by simpa using h)
      · exact hj 6 (by simpa using h)
  exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hc (by exact_mod_cast hn))

/-- Both residues use this obstruction: A is a or -a according to which
of F+ih and F-ih has indicial exponent +2. -/
theorem weak_residue_impossible {A ω : ℝ} (hA : A ≠ 0) {c d e f g U V : ℂ}
    (hc : c^2= -4) (hu : U=2*U+(-ω+Complex.I*A))
    (hd : d*U=0) (hv : V= -2*V+(-ω-Complex.I*A))
    (he : 3/2*(c^2*e+c*d^2)=0)
    (hf : 2*f+3/2*c^2*f+3*c*d*e+d^3/2=0)
    (hg : d=0 → e=0 → f=0 → (U+V)/2=(6+3/2*c^2)*g) : False := by
  have hu' : U=(ω:ℂ)-Complex.I*A := by linear_combination -hu
  have hU : U ≠ 0 := by
    rw [hu']
    intro h
    have w := congrArg Complex.im h
    simp at w
    exact hA w
  have d0 := (mul_eq_zero.mp hd).resolve_right hU
  have e0 : e=0 := by rw [d0,hc] at he; linear_combination (-1/6)*he
  have f0 : f=0 := by rw [d0,hc] at hf; linear_combination (-1/4)*hf
  have hv' : 3*V= -(ω:ℂ)-Complex.I*A := by linear_combination hv
  have hg' := hg d0 e0 f0
  rw [hc,hu'] at hg'
  have h : (2:ℂ)*ω-4*Complex.I*A=0 := by linear_combination 6*hg' - hv'
  have w := congrArg Complex.im h
  simp at w
  exact hA (by linarith)

theorem defect_leading {c : ℂ} (hc : c^2= -9) : 2*c+2/9*c^3=0 := by
  linear_combination (2/9*c)*hc

#print axioms scalar_elimination
#print axioms derivative_order_coefficient
#print axioms residue_squares
#print axioms linearized_pole
#print axioms first_three_vanish
#print axioms rational_resonances
#print axioms fractional_coefficient_vanish
#print axioms weak_residue_impossible
#print axioms defect_leading
end ClosedSimilarity.ReflectedPoleAlgebra
