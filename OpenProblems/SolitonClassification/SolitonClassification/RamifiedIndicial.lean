import SolitonClassification.RamifiedDerivative
import Mathlib.Data.Rat.Lemmas

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 650000
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RationalCurvature

private theorem irrational_factor (v : ℚ) : 2*v^2-4*v-21≠0 := by
  intro h
  have bad : IsSquare ((46:ℕ):ℚ) := ⟨2*v-2,by norm_num;nlinarith⟩
  obtain ⟨n,eq⟩:= Rat.isSquare_natCast_iff.mp bad
  have nr : n<7 := by
    by_contra! high
    have := Nat.mul_self_le_mul_self high
    omega
  have low := Nat.mul_self_le_mul_self (show n≤6 by omega)
  omega

/-- A first difference between solutions with the same polar coefficient has
integral exponent in the original arclength coordinate. Both polar symbols
are allowed before descent. -/
theorem indicial_divisibility {q : ℕ} (hq : 0<q) {f g : ℂ→ℂ} {a b c d : ℂ} {m : ℤ}
    (hf : Jet f 0 (-(q:ℤ)) c) (hg : Jet g 0 (-(q:ℤ)) c)
    (hc : (c^2+4)*(c^2+9)=0) (hd : Jet (fun z=>f z-g z) 0 m d) (dn : d≠0)
    (rf : jetResidual q a b f =ᶠ[𝓝[≠] 0] fun _=>0)
    (rg : jetResidual q a b g =ᶠ[𝓝[≠] 0] fun _=>0) : (q:ℤ)∣m := by
  let u : ℚ := (m:ℚ)/q
  let t := (m:ℂ)/q
  let D := ds q
  have qn : (q:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have j : DifferenceJet 0 (m+q) (-(q:ℤ)) c d f g := ⟨hf,hg,hd.retag (by omega) rfl⟩
  have j1 : DifferenceJet 0 (m+q) (-2*q) (-c) (t*d) (D f) (D g) := by
    apply (ds_difference hq j).retag (by omega) <;> simp only [t,Int.cast_neg,Int.cast_natCast,Int.cast_add] <;> field_simp
    all_goals ring
  have j2 : DifferenceJet 0 (m+q) (-3*q) (2*c) ((t-1)*t*d) (D (D f)) (D (D g)) := by
    apply (ds_difference hq j1).retag (by omega) <;> simp only [t,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_add] <;> field_simp
    all_goals ring
  have j3 : DifferenceJet 0 (m+q) (-4*q) (-6*c) ((t-2)*(t-1)*t*d)
      (D (D (D f))) (D (D (D g))) := by
    apply (ds_difference hq j2).retag (by omega) <;> simp only [t,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_add] <;> field_simp
    all_goals ring
  have j4 : DifferenceJet 0 (m+q) (-5*q) (24*c) ((t-3)*(t-2)*(t-1)*t*d)
      (D (D (D (D f)))) (D (D (D (D g)))) := by
    apply (ds_difference hq j3).retag (by omega) <;> simp only [t,Int.cast_neg,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,Int.cast_add] <;> field_simp
    all_goals ring
  have quadratic := (((j.mul j4).retag (N:=-6*q) (by omega) rfl rfl).sub
    ((j1.mul j3).retag (N:=-6*q) (by omega) rfl rfl)).smul 2
  have quartic := ((((j.pow 2).mul (j1.pow 2)).retag (N:=-6*q) (by omega) rfl rfl).smul 3).add
    ((((j.pow 3).mul j2).retag (N:=-6*q) (by omega) rfl rfl).smul 5)
  have higher := ((j.pow 6).retag (N:=-6*q) (by omega) rfl rfl)
  have lowerA := (((j.pow 2).smul (2*a)).weaken (m:=-6*q) (by omega))
  have lowerB := ((j1.smul (2*b)).weaken (m:=-6*q) (by omega))
  have body := ((((quadratic.add quartic).add higher).sub lowerA).sub lowerB).change
  have zero := body.eq_zero_of_germ_zero (show (fun z=>jetResidual q a b f z -
      jetResidual q a b g z)=ᶠ[𝓝[≠] 0] fun _=>0 from by
    filter_upwards [rf,rg] with z v w
    simp [v,w])
  norm_num at zero
  have of_int (i : ℤ) (h : t=(i:ℂ)) : (q:ℤ)∣m := by
    obtain h' := (div_eq_iff qn).mp h
    use i
    rw [mul_comm]
    exact_mod_cast h'
  have cn : c≠0 := by intro v;norm_num [v] at hc
  rcases mul_eq_zero.mp hc with four|nine
  · have h : (2*c*d)*((t+2)*t*(t-3)*(t-4))=0 := by
      linear_combination zero-(c*d*(5*t^2-11*t+12+6*c^2))*four
    have eq := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) cn) dn)
    simp only [mul_eq_zero] at eq
    rcases eq with ((eq|eq)|eq)|eq
    · exact of_int (-2) (by norm_num;linear_combination eq)
    · exact of_int 0 (by simpa using eq)
    · exact of_int 3 (by norm_num;linear_combination eq)
    · exact of_int 4 (by norm_num;linear_combination eq)
  · have h : c*d*((t+2)*(t-5)*(2*t^2-4*t-21))=0 := by
      linear_combination zero-(c*d*(5*t^2-11*t-18+6*c^2))*nine
    have eq := (mul_eq_zero.mp h).resolve_left (mul_ne_zero cn dn)
    simp only [mul_eq_zero] at eq
    rcases eq with (eq|eq)|eq
    · exact of_int (-2) (by norm_num;linear_combination eq)
    · exact of_int 5 (by norm_num;linear_combination eq)
    · have rat : 2*u^2-4*u-21=0 := by
        dsimp [t] at eq
        dsimp [u]
        exact_mod_cast eq
      exact (irrational_factor u rat).elim

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.indicial_divisibility
