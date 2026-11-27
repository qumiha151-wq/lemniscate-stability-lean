import SolitonClassification.OddLocalRigidity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation

abbrev V := Fin 5 → ℝ
def act (M : Fin 5 → Fin 5 → ℝ) (x : V) (i : Fin 5) :=
  M i 0*x 0 + M i 1*x 1 + M i 2*x 2 + M i 3*x 3 + M i 4*x 4

def centre (x : V) : V := ![-x 0,x 1,-x 2,-x 3,x 4]

private theorem null_pair {a b c d x y : ℝ}
    (h : a*d-b*c ≠ 0) (u : a*x+b*y=0) (v : c*x+d*y=0) : x=0 ∧ y=0 := by
  have p : (a*d-b*c)*x=0 := by linear_combination d*u - b*v
  have q : (a*d-b*c)*y=0 := by linear_combination a*v - c*u
  exact ⟨(mul_eq_zero.mp p).resolve_left h,(mul_eq_zero.mp q).resolve_left h⟩

/-- Injectivity of the odd fixed-period shooting derivative on the v=0
    section, expressed entirely with two minors of the quarter transfer.
    x is the transported-back Jacobi vector. The two projections onto (k,p)
    vanish for both x and its centre reflection whenever the odd variation is
    periodic. Time-translation covariance is used only in three rows. -/
theorem two_quarter_minors_rigidity (M : Fin 5 → Fin 5 → ℝ) (x : V) (b A : ℝ)
    (ax : A≠0) (time_k : b*M 0 0 + M 0 3=0)
    (time_v : b*M 1 0 + M 1 3=A) (time_p : b*M 2 0 + M 2 3=0)
    (even : M 0 0*M 2 2-M 0 2*M 2 0 ≠0)
    (split : M 0 1*M 2 4-M 0 4*M 2 1 ≠0)
    (yk : act M x 0=0) (yv : act M x 1=0) (yp : act M x 2=0)
    (jk : act M (centre x) 0=0) (jp : act M (centre x) 2=0) : x=0 := by
  unfold act at yk yv yp
  simp [act,centre] at jk jp
  have h1 : M 0 1*x 1 + M 0 4*x 4=0 := by linarith
  have h2 : M 2 1*x 1 + M 2 4*x 4=0 := by linarith
  obtain ⟨z1,z4⟩ := null_pair split h1 h2
  simp only [z1,z4,mul_zero,add_zero] at yk yp yv
  have e1 : M 0 0*(x 0-b*x 3)+M 0 2*x 2=0 := by linear_combination yk - x 3*time_k
  have e2 : M 2 0*(x 0-b*x 3)+M 2 2*x 2=0 := by linear_combination yp - x 3*time_p
  obtain ⟨ze,z2⟩ := null_pair even e1 e2
  have qa : A*x 3=0 := by linear_combination yv - (x 3)*time_v - (M 1 0)*ze - (M 1 2)*z2
  have z3 := (mul_eq_zero.mp qa).resolve_left ax
  have z0 : x 0=0 := by simpa [z3] using ze
  ext i
  fin_cases i <;> assumption


def axis (x : V) : V := ![x 0,-x 1,x 2,-x 3,-x 4]

def carried (T : V ≃ₗ[ℝ] V) (y : V) : V := T (centre (T.symm y))

private theorem centre_twice (x : V) : centre (centre x)=x := by
  ext i
  fin_cases i <;> simp [centre]

private theorem carried_twice (T : V ≃ₗ[ℝ] V) (y : V) : carried T (carried T y)=y := by
  simp only [carried,LinearEquiv.symm_apply_apply,centre_twice,LinearEquiv.apply_symm_apply]

private theorem carried_neg (T : V ≃ₗ[ℝ] V) (y : V) : carried T (-y)= -(carried T y) := by
  have negc (x : V) : centre (-x) = -(centre x) := by
    ext i
    fin_cases i <;> simp [centre]
  simp [carried,negc]

/-- Every odd Jacobi vector fixed by the actual four-quarter return vanishes
    on the transverse section. The four-quarter formula is (J R)^2, with
    J the conjugated centre reversor and R the seam reversor. -/
theorem odd_front_return_injective (M : Fin 5 → Fin 5 → ℝ) (T : V ≃ₗ[ℝ] V)
    (Tval : ∀ x i, T x i=act M x i) (b A q w : ℝ)
    (ax : A≠0) (time_k : b*M 0 0 + M 0 3=0)
    (time_v : b*M 1 0 + M 1 3=A) (time_p : b*M 2 0 + M 2 3=0)
    (even : M 0 0*M 2 2-M 0 2*M 2 0 ≠0)
    (split : M 0 1*M 2 4-M 0 4*M 2 1 ≠0)
    (period : let y : V := ![0,0,0,q,w]
      carried T (axis (carried T (axis y)))=y) : q=0 ∧ w=0 := by
  let y : V := ![0,0,0,q,w]
  let x := T.symm y
  have odd : axis y= -y := by
    ext i
    fin_cases i <;> simp [y,axis]
  change carried T (axis (carried T (axis y)))=y at period
  have eq := congrArg (carried T) period
  rw [carried_twice,odd,carried_neg] at eq
  have jk := congrFun eq 0
  have jp := congrFun eq 2
  change -(T (centre x) 0)=T (centre x) 0 at jk
  change -(T (centre x) 2)=T (centre x) 2 at jp
  rw [Tval] at jk jp
  have same : T x=y := T.apply_symm_apply y
  have point (i : Fin 5) : act M x i=y i := (Tval x i).symm.trans (congrFun same i)
  have zero := two_quarter_minors_rigidity M x b A ax time_k time_v time_p even split
    (point 0) (point 1) (point 2) (by linarith) (by linarith)
  rw [zero,map_zero] at same
  exact ⟨(congrFun same 3).symm,(congrFun same 4).symm⟩

end ClosedSimilarity.RotatingBifurcation
#print axioms ClosedSimilarity.RotatingBifurcation.two_quarter_minors_rigidity

#print axioms ClosedSimilarity.RotatingBifurcation.odd_front_return_injective
