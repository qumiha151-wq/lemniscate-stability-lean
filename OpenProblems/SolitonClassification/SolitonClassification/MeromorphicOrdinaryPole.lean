import SolitonClassification.RationalLocalJet

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

def ordinaryQuadratic (k:ℂ→ℂ) (s:ℂ) := 2*(k s*deriv (deriv (deriv (deriv k))) s-deriv k s*deriv (deriv (deriv k)) s)
def ordinaryQuartic (k:ℂ→ℂ) (s:ℂ) := 3*(k s^2*(deriv k s)^2)+5*(k s^3*deriv (deriv k) s)
def ordinaryResidual (a b:ℂ) (k:ℂ→ℂ) (s:ℂ) :=
  ordinaryQuadratic k s+ordinaryQuartic k s+k s^6-2*a*k s^2-2*b*deriv k s

private theorem leading {k:ℂ→ℂ} {x c:ℂ} {n:ℤ} (j:Jet k x n c) :
    Jet (ordinaryQuadratic k) x (2*n-4)
      (2*(c*((n-3)*(n-2)*(n-1)*n*c)-(n*c)*((n-2)*(n-1)*n*c))) ∧
    Jet (ordinaryQuartic k) x (4*n-2) (3*(c^2*(n*c)^2)+5*(c^3*((n-1)*n*c))) := by
  have j₁ := j.deriv
  have j₂ := j₁.deriv
  have j₃ := j₂.deriv
  have j₄ := j₃.deriv
  have p : Jet (fun z=>k z*deriv (deriv (deriv (deriv k))) z) x (2*n-4) (c*((n-3)*(n-2)*(n-1)*n*c)) := by
    apply (j.mul j₄).retag <;> push_cast <;> ring
  have q : Jet (fun z=>deriv k z*deriv (deriv (deriv k)) z) x (2*n-4) ((n*c)*((n-2)*(n-1)*n*c)) := by
    apply (j₁.mul j₃).retag <;> push_cast <;> ring
  have r : Jet (fun z=>k z^2*(deriv k z)^2) x (4*n-2) (c^2*(n*c)^2) := by
    apply ((j.pow 2).mul (j₁.pow 2)).retag <;> push_cast <;> ring
  have t : Jet (fun z=>k z^3*deriv (deriv k) z) x (4*n-2) (c^3*((n-1)*n*c)) := by
    apply ((j.pow 3).mul j₂).retag <;> push_cast <;> ring
  exact ⟨(p.sub q).smul 2,(r.smul 3).add (t.smul 5)⟩

theorem pole_order_and_symbol {k:ℂ→ℂ} {x a b c:ℂ} {n:ℤ} (j:Jet k x n c) (nc:c≠0) (pole:n<0)
    (germ:ordinaryResidual a b k=ᶠ[𝓝[≠] x] fun _=>0) :
    n= -1 ∧ (c^2+4)*(c^2+9)=0 := by
  obtain ⟨p,q⟩ := leading j
  have single : n= -1 := by
    by_contra more
    have h₂ := ((j.pow 2).smul (2*a)).weaken (m:=6*n) (by omega)
    have h₁ := (j.deriv.smul (2*b)).weaken (m:=6*n) (by omega)
    have total := ((((p.weaken (m:=6*n) (by omega)).add (q.weaken (by omega))).add (j.pow 6)).sub h₂).sub h₁
    have zero := total.eq_zero_of_germ_zero germ
    exact (pow_ne_zero 6 nc) (by simpa using zero)
  refine ⟨single,?_⟩
  subst n
  have h₂ := ((j.pow 2).smul (2*a)).weaken (m:=-6) (by norm_num)
  have h₁ := (j.deriv.smul (2*b)).weaken (m:=-6) (by norm_num)
  have h₆ : Jet (fun t=>k t^6) x (-6) (c^6) := (j.pow 6).retag (by norm_num) rfl
  have eq := ((((p.add q).add h₆).sub h₂).sub h₁).eq_zero_of_germ_zero germ
  have w : c^2*((c^2+4)*(c^2+9))=0 := by norm_num at eq;linear_combination eq
  exact (mul_eq_zero.mp w).resolve_left (pow_ne_zero _ nc)

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.pole_order_and_symbol
