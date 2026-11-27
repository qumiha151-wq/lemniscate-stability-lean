import SolitonClassification.RationalLocalJet

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.RationalCurvature

def D₂ (μ : ℂ) (f : ℂ→ℂ) := euler μ (euler μ f)
def D₃ (μ : ℂ) (f : ℂ→ℂ) := euler μ (D₂ μ f)
def D₄ (μ : ℂ) (f : ℂ→ℂ) := euler μ (D₃ μ f)

def quadratic (μ : ℂ) (f : ℂ→ℂ) (z : ℂ) :=
  2*(f z*D₄ μ f z-euler μ f z*D₃ μ f z)
def quartic (μ : ℂ) (f : ℂ→ℂ) (z : ℂ) :=
  3*(f z^2*(euler μ f z)^2)+5*(f z^3*D₂ μ f z)
def residual (μ a b : ℂ) (f : ℂ→ℂ) (z : ℂ) :=
  quadratic μ f z+quartic μ f z+f z^6-2*a*f z^2-2*b*euler μ f z

/-- At an ordinary point use d=1, l=μx; at the Euler singular point use
d=0, l=μ. Then each differentiation lowers the exponent by d. -/
structure FourJet (μ x : ℂ) (f : ℂ→ℂ) (n d : ℤ) (A B C D E : ℂ) : Prop where
  j₀ : Jet f x n A
  j₁ : Jet (euler μ f) x (n-d) B
  j₂ : Jet (D₂ μ f) x (n-2*d) C
  j₃ : Jet (D₃ μ f) x (n-3*d) D
  j₄ : Jet (D₄ μ f) x (n-4*d) E

namespace FourJet
variable {μ x : ℂ} {f : ℂ→ℂ} {n d : ℤ} {A B C D E : ℂ}
theorem of_rule (j : Jet f x n A) (l : ℂ)
    (rule : ∀ {g : ℂ→ℂ} {m : ℤ} {v : ℂ},Jet g x m v →
      Jet (euler μ g) x (m-d) (l*(m*v))) :
    FourJet μ x f n d A (l*(n*A)) (l^2*n*(n-d)*A)
      (l^3*n*(n-d)*(n-2*d)*A) (l^4*n*(n-d)*(n-2*d)*(n-3*d)*A) := by
  have h₁ := rule j
  have h₂ : Jet (D₂ μ f) x (n-2*d) (l^2*n*(n-d)*A) := by
    apply (rule h₁).retag <;> push_cast <;> ring
  have h₃ : Jet (D₃ μ f) x (n-3*d) (l^3*n*(n-d)*(n-2*d)*A) := by
    apply (rule h₂).retag <;> push_cast <;> ring
  have h₄ : Jet (D₄ μ f) x (n-4*d) (l^4*n*(n-d)*(n-2*d)*(n-3*d)*A) := by
    apply (rule h₃).retag <;> push_cast <;> ring
  exact ⟨j,h₁,h₂,h₃,h₄⟩

theorem at_zero (j : Jet f 0 n A) :
    FourJet μ 0 f n 0 A (μ*(n*A)) (μ^2*n*(n-0)*A)
      (μ^3*n*(n-0)*(n-2*0)*A) (μ^4*n*(n-0)*(n-2*0)*(n-3*0)*A) := by
  have rule {g : ℂ→ℂ} {m : ℤ} {v : ℂ} (hg : Jet g 0 m v) :
      Jet (euler μ g) 0 (m-0) (μ*(m*v)) := by simpa using euler_at_zero (μ:=μ) hg
  simpa only [Int.cast_zero] using of_rule (μ:=μ) (d:=0) j μ rule

theorem at_point (j : Jet f x n A) :
    FourJet μ x f n 1 A ((μ*x)*(n*A)) ((μ*x)^2*n*(n-1)*A)
      ((μ*x)^3*n*(n-1)*(n-2*1)*A) ((μ*x)^4*n*(n-1)*(n-2*1)*(n-3*1)*A) := by
  simpa only [Int.cast_one] using of_rule (μ:=μ) (d:=1) j (μ*x)
    (fun hg => euler_at_nonzero hg)

variable (j : FourJet μ x f n d A B C D E)
include j

theorem jquadratic : Jet (quadratic μ f) x (2*n-4*d) (2*(A*E-B*D)) := by
  have h₀ : Jet (fun z=>f z*D₄ μ f z) x (2*n-4*d) (A*E) :=
    (j.j₀.mul j.j₄).retag (by ring) rfl
  have h₁ : Jet (fun z=>euler μ f z*D₃ μ f z) x (2*n-4*d) (B*D) :=
    (j.j₁.mul j.j₃).retag (by ring) rfl
  exact (h₀.sub h₁).smul 2

theorem jquartic : Jet (quartic μ f) x (4*n-2*d) (3*(A^2*B^2)+5*(A^3*C)) := by
  have h₀ : Jet (fun z=>f z^2*(euler μ f z)^2) x (4*n-2*d) (A^2*B^2) :=
    ((j.j₀.pow 2).mul (j.j₁.pow 2)).retag (by push_cast; ring) rfl
  have h₁ : Jet (fun z=>f z^3*D₂ μ f z) x (4*n-2*d) (A^3*C) :=
    ((j.j₀.pow 3).mul j.j₂).retag (by push_cast; ring) rfl
  exact (h₀.smul 3).add (h₁.smul 5)

theorem no_deep_pole {a b : ℂ} (germ : residual μ a b f=ᶠ[𝓝[≠] x] fun _=>0)
    (hn : 6*n<2*n-4*d) (hq : 6*n<4*n-2*d) (h₂ : 6*n<2*n) (h₁ : 6*n<n-d) :
    A=0 := by
  have h6 := j.j₀.pow 6
  have h := (((j.jquadratic.weaken hn).add (j.jquartic.weaken hq)).add h6).sub
    (((j.j₀.pow 2).smul (2*a)).weaken h₂)
  have total := h.sub ((j.j₁.smul (2*b)).weaken h₁)
  have z := total.eq_zero_of_germ_zero germ
  simpa using z

end FourJet

theorem cannot_pole_at_zero {a b μ A : ℂ} {n : ℤ} {f : ℂ→ℂ}
    (j : Jet f 0 n A) (germ : residual μ a b f=ᶠ[𝓝[≠] 0] fun _=>0) (hn : n<0) : A=0 :=
  (FourJet.at_zero j).no_deep_pole germ (by omega) (by omega) (by omega) (by omega)

theorem cannot_higher_pole {a b μ x A : ℂ} {n : ℤ} {f : ℂ→ℂ}
    (j : Jet f x n A) (germ : residual μ a b f=ᶠ[𝓝[≠] x] fun _=>0) (hn : n< -1) : A=0 :=
  (FourJet.at_point j).no_deep_pole germ (by omega) (by omega) (by omega) (by omega)

end ClosedSimilarity.RationalCurvature
