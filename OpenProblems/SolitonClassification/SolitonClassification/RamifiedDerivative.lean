import SolitonClassification.MeromorphicDifferenceJet
import Mathlib.Analysis.Calculus.Deriv.CompMul

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RationalCurvature

def ds (q : ℕ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  ((q:ℂ)*w^(q-1))⁻¹ * deriv f w

def jetResidual (q : ℕ) (a b : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let D := ds q
  2*(f z*D (D (D (D f))) z - D f z*D (D (D f)) z) +
    (3*(f z^2*(D f z)^2)+5*(f z^3*D (D f) z)) + f z^6-2*a*f z^2-2*b*D f z

theorem ds_branch {q : ℕ} (hq : 0<q) {f : ℂ → ℂ} {s₀ w : ℂ} (nw : w≠0)
    (hf : DifferentiableAt ℂ f (s₀+w^q)) :
    ds q (fun z=>f (s₀+z^q)) w=deriv f (s₀+w^q) := by
  have pw : HasDerivAt (fun z:ℂ=>s₀+z^q) ((q:ℂ)*w^(q-1)) w := by
    simpa using (((hasDerivAt_id w).pow q).const_add s₀)
  have de := hf.hasDerivAt.comp w pw
  change ((q:ℂ)*w^(q-1))⁻¹*deriv (f ∘ (fun z=>s₀+z^q)) w=_
  have qn : (q:ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [de.deriv];field_simp

private theorem jacobian (q : ℕ) (hq : 0<q) :
    Jet (fun w:ℂ=>((q:ℂ)*w^(q-1))⁻¹) 0 (1-(q:ℤ)) (q:ℂ)⁻¹ := by
  refine ⟨fun _=>(q:ℂ)⁻¹,analyticAt_const,rfl,?_⟩
  filter_upwards with w
  rw [sub_zero,show (1-(q:ℤ))= -((q-1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,mul_inv_rev]

theorem ds_jet {q : ℕ} (hq : 0<q) {f : ℂ → ℂ} {n : ℤ} {c : ℂ}
    (j : Jet f 0 n c) : Jet (ds q f) 0 (n-q) ((n:ℂ)/q*c) := by
  apply ((jacobian q hq).mul j.deriv).retag <;> first | omega | ring

theorem ds_difference {q : ℕ} (hq : 0<q) {f g : ℂ → ℂ} {n gap : ℤ} {c d : ℂ}
    (j : DifferenceJet 0 gap n c d f g) :
    DifferenceJet 0 gap (n-q) ((n:ℂ)/q*c) (((n:ℂ)+gap)/q*d) (ds q f) (ds q g) := by
  let v := fun w:ℂ=>((q:ℂ)*w^(q-1))⁻¹
  have h : DifferenceJet 0 gap (1-(q:ℤ)) (q:ℂ)⁻¹ 0 v v := by
    refine ⟨jacobian q hq,jacobian q hq,?_⟩
    simpa using Jet.zero 0 (1-(q:ℤ)+gap)
  apply (h.mul j.deriv).retag <;> first | omega | ring

def deck (r : ℂ) (f : ℂ → ℂ) (w : ℂ) := f (r*w)

theorem deck_punctured {r : ℂ} (hr : r≠0) :
    Tendsto (fun w:ℂ=>r*w) (𝓝[≠] 0) (𝓝[≠] 0) := by
  have h : Tendsto (fun w:ℂ=>r*w) (𝓝[≠] 0) (𝓝[≠] (r*0)) := by
    apply (show Continuous (fun w:ℂ=>r*w) from continuous_const.mul continuous_id).continuousWithinAt.tendsto_nhdsWithin
    intro w hw
    simpa using mul_ne_zero hr hw
  simpa using h

theorem deck_jet {r c : ℂ} {n : ℤ} {f : ℂ → ℂ} (hr : r≠0) (j : Jet f 0 n c) :
    Jet (deck r f) 0 n (r^n*c) := by
  obtain ⟨g,ag,gz,eq⟩ := j
  have ar : AnalyticAt ℂ g (r*0) := by simpa using ag
  refine ⟨fun w=>r^n*g (r*w),analyticAt_const.mul (ar.comp (f:=fun w:ℂ=>r*w) (analyticAt_const.mul analyticAt_id)),
    by simp [gz],?_⟩
  filter_upwards [(deck_punctured hr).eventually eq] with z e
  change f (r*z)=(r*z-0)^n*g (r*z) at e
  simp only [deck,e,sub_zero,mul_zpow];ring

theorem ds_deck {q : ℕ} (hq : 0<q) {r : ℂ} (hr : r^q=1) (f : ℂ → ℂ) :
    ds q (deck r f)=deck r (ds q f) := by
  have rn : r≠0 := by intro z; rw [z,zero_pow (by omega : q≠0)] at hr; norm_num at hr
  have rq : r*r^(q-1)=1 := by simpa only [←pow_succ',Nat.sub_add_cancel hq] using hr
  funext w
  change ((q:ℂ)*w^(q-1))⁻¹*deriv (fun z=>f (r*z)) w=((q:ℂ)*(r*w)^(q-1))⁻¹*deriv f (r*w)
  rw [deriv_comp_mul_left,mul_pow,smul_eq_mul]
  have ident : (r^(q-1))⁻¹=r := inv_eq_of_mul_eq_one_left rq
  simp only [mul_inv_rev,ident]
  ring

theorem residual_deck {q : ℕ} (hq : 0<q) {r : ℂ} (hr : r^q=1) (a b : ℂ) (f : ℂ→ℂ) :
    jetResidual q a b (deck r f) = deck r (jetResidual q a b f) := by
  funext w
  simp only [jetResidual,ds_deck hq hr,deck]

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.ds_branch
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.residual_deck
