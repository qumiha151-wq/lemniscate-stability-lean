import SolitonClassification.RamifiedDerivative

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RationalCurvature

theorem pole_order {q : ℕ} (hq : 0<q) {f : ℂ→ℂ} {a b c : ℂ} {n : ℤ}
    (j : Jet f 0 n c) (cn : c≠0) (hn : n<0)
    (eq : jetResidual q a b f =ᶠ[𝓝[≠] 0] fun _=>0) :
    n= -(q:ℤ) ∧ (c^2+4)*(c^2+9)=0 := by
  let t := (n:ℂ)/q
  let D := ds q
  have qn : (q:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have j1 : Jet (D f) 0 (n-q) (t*c) := ds_jet hq j
  have j2 : Jet (D (D f)) 0 (n-2*q) ((t-1)*t*c) := by
    apply (ds_jet hq j1).retag (by omega)
    dsimp [t];push_cast;field_simp
  have j3 : Jet (D (D (D f))) 0 (n-3*q) ((t-2)*(t-1)*t*c) := by
    apply (ds_jet hq j2).retag (by omega)
    dsimp [t];push_cast;field_simp
  have j4 : Jet (D (D (D (D f)))) 0 (n-4*q) ((t-3)*(t-2)*(t-1)*t*c) := by
    apply (ds_jet hq j3).retag (by omega)
    dsimp [t];push_cast;field_simp
  have quadratic := (((j.mul j4).retag (m:=2*n-4*q) (by omega) rfl).sub
    ((j1.mul j3).retag (m:=2*n-4*q) (by omega) rfl)).smul 2
  have quartic := ((((j.pow 2).mul (j1.pow 2)).retag (m:=4*n-2*q) (by omega) rfl).smul 3).add
    ((((j.pow 3).mul j2).retag (m:=4*n-2*q) (by omega) rfl).smul 5)
  have a2 := (j.pow 2).smul (2*a)
  have b1 := j1.smul (2*b)
  have n5 : n= -(q:ℤ) := by
    rcases lt_trichotomy n (-(q:ℤ)) with high|same|low
    · have s := ((((quadratic.weaken (m:=6*n) (by omega)).add (quartic.weaken (by omega))).add
        (j.pow 6)).sub (a2.weaken (by omega))).sub (b1.weaken (by omega))
      exact False.elim ((pow_ne_zero 6 cn) (by simpa using s.eq_zero_of_germ_zero eq))
    · exact same
    · have s := (((quadratic.add (quartic.weaken (by omega))).add ((j.pow 6).weaken (by omega))).sub
        (a2.weaken (by omega))).sub (b1.weaken (by omega))
      have raw := s.eq_zero_of_germ_zero eq
      have zz : (-6:ℂ)*c^2*t*(t-1)*(t-2)=0 := by linear_combination raw
      have ne (i : ℕ) : t-(i:ℂ)≠0 := by
        intro h
        have h' : (n:ℂ)=(i:ℂ)*q := (div_eq_iff qn).mp (sub_eq_zero.mp h)
        have h'' : n=(i:ℤ)*q := by exact_mod_cast h'
        have nz : 0≤(i:ℤ)*(q:ℤ) := by positivity
        omega
      have nt : t≠0 := by simpa using ne 0
      exact False.elim ((mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (-6:ℂ)≠0)
        (pow_ne_zero 2 cn)) nt) (ne 1)) (ne 2)) (by simpa using zz))
  refine ⟨n5,?_⟩
  have s := (((quadratic.add (quartic.retag (m:=2*n-4*q) (by omega) rfl)).add
    ((j.pow 6).retag (by omega) rfl)).sub (a2.weaken (by omega))).sub (b1.weaken (by omega))
  have raw := s.eq_zero_of_germ_zero eq
  have tr : t= -1 := by dsimp [t];rw [n5];push_cast;field_simp
  rw [tr] at raw
  have zz : c^2*((c^2+4)*(c^2+9))=0 := by linear_combination raw
  exact (mul_eq_zero.mp zz).resolve_left (pow_ne_zero 2 cn)

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.pole_order
