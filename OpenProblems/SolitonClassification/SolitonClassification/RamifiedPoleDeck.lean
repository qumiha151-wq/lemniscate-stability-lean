import SolitonClassification.RamifiedPoleBalance
import SolitonClassification.RamifiedIndicial

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RationalCurvature

/-- A nonzero leading coefficient of a cyclic difference cannot occur at a
power divisible by the order of the deck group. -/
theorem deck_difference_not_divisible {q : ℕ} (hq : 0<q) {r d : ℂ}
    {f : ℂ→ℂ} {m : ℤ} (hr : r^q=1) (dn : d≠0)
    (j : Jet (fun w=>f w-deck r f w) 0 m d) : ¬(q:ℤ)∣m := by
  rintro ⟨i,hi⟩
  have rn : r≠0 := by intro z;rw [z,zero_pow (Nat.ne_of_gt hq)] at hr;norm_num at hr
  have phase (k : ℕ) : (r^k)^m=1 := by
    have z : (r^k)^q=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,hr,one_pow]
    rw [hi,zpow_mul,zpow_natCast,z,one_zpow]
  have sum (k : ℕ) : Jet (fun w=>f w-deck (r^k) f w) 0 m ((k:ℂ)*d) := by
    induction k with
    | zero => simpa [deck] using Jet.zero 0 m
    | succ k ih =>
      have p := deck_jet (pow_ne_zero k rn) j
      rw [phase,one_mul] at p
      apply ((ih.add p).retag rfl (by push_cast;ring)).congr
      filter_upwards with w
      simp only [deck,pow_succ]
      rw [show r*(r^k*w)=(r^k*r)*w by ring]
      ring
  have z := (sum q).eq_zero_of_germ_zero (by simp [hr,deck])
  have qn : (q:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  exact (mul_ne_zero qn dn) z

/-- Every deck rotation fixes a finite Laurent pole germ of the pulled-back
curvature equation. Only its meromorphic order on the cover is prescribed. -/
theorem pole_deck_invariant {q : ℕ} (hq : 0<q) {f : ℂ→ℂ} {a b : ℂ} {n : ℤ}
    (mf : MeromorphicAt f 0) (order : meromorphicOrderAt f 0=(n:WithTop ℤ)) (pole : n<0)
    (residual : jetResidual q a b f =ᶠ[𝓝[≠] 0] fun _=>0) (r:ℂ) (hr:r^q=1) :
    (fun w=>f (r*w)) =ᶠ[𝓝[≠] (0:ℂ)] f := by
  obtain ⟨c,cn,hf⟩ := Jet.of_order mf order
  obtain ⟨ord,symbol⟩ := pole_order hq hf cn pole residual
  subst n
  have rn : r≠0 := by intro z;rw [z,zero_pow (Nat.ne_of_gt hq)] at hr;norm_num at hr
  have hg := deck_jet rn hf
  rw [zpow_neg,zpow_natCast,hr,inv_one,one_mul] at hg
  have rg : jetResidual q a b (deck r f)=ᶠ[𝓝[≠] 0] fun _=>0 := by
    rw [residual_deck hq hr]
    exact (deck_punctured rn).eventually residual
  have mr : MeromorphicAt f (r*0) := by simpa using mf
  have mg : MeromorphicAt (deck r f) 0 :=
    mr.comp_analyticAt (g:=fun z:ℂ=>r*z) (analyticAt_const.mul analyticAt_id)
  let v := fun z=>f z-deck r f z
  have mv : MeromorphicAt v 0 := mf.sub mg
  by_cases top : meromorphicOrderAt v 0=⊤
  · have vanish := meromorphicOrderAt_eq_top_iff.mp top
    filter_upwards [vanish] with w h
    exact (sub_eq_zero.mp h).symm
  · lift meromorphicOrderAt v 0 to ℤ using top with m hm
    obtain ⟨d,dn,jet⟩ := Jet.of_order mv hm.symm
    have div := indicial_divisibility hq hf hg symbol jet dn residual rg
    exact False.elim (deck_difference_not_divisible hq hr dn jet div)

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.pole_deck_invariant
