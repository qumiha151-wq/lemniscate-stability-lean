import SolitonClassification.RamifiedBranchResidual
import SolitonClassification.RamifiedBoundedCurvature

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RamifiedBounded

def ordinaryForce (k : ℂ→ℂ) (s : ℂ) := deriv (deriv k) s+k s^3/2
def ordinaryHeight (b : ℂ) (k : ℂ→ℂ) (s : ℂ) := (deriv (ordinaryForce k) s+b)/k s
def branchForce (q : ℕ) (f : ℂ→ℂ) (w : ℂ) := ds q (ds q f) w+f w^3/2
def branchHeight (q : ℕ) (b : ℂ) (f : ℂ→ℂ) (w : ℂ) := (ds q (branchForce q f) w+b)/f w

private theorem force_analytic {k:ℂ→ℂ} {s:ℂ} (ak:AnalyticAt ℂ k s) :
    AnalyticAt ℂ (ordinaryForce k) s :=
  ak.deriv.deriv.add (ak.pow 3).div_const

private theorem force_deriv {k:ℂ→ℂ} {s:ℂ} (ak:AnalyticAt ℂ k s) :
    deriv (ordinaryForce k) s =
      deriv (deriv (deriv k)) s + 3/2*k s^2*deriv k s := by
  have z := ak.deriv.deriv.differentiableAt.hasDerivAt.fun_add
    ((ak.differentiableAt.hasDerivAt.pow 3).div_const 2)
  rw [show deriv (ordinaryForce k) s=_ from z.deriv]
  ring

private theorem force_second {k:ℂ→ℂ} {s:ℂ} (ak:AnalyticAt ℂ k s) :
    deriv (deriv (ordinaryForce k)) s=deriv (deriv (deriv (deriv k))) s+
      3*k s*(deriv k s)^2 + 3/2*k s^2*deriv (deriv k) s := by
  have eq : deriv (ordinaryForce k) =ᶠ[𝓝 s] fun z=>
      deriv (deriv (deriv k)) z + 3/2*k z^2*deriv k z :=
    ak.eventually_analyticAt.mono (fun _ h=>force_deriv h)
  have z := ak.deriv.deriv.deriv.differentiableAt.hasDerivAt.fun_add
    (((ak.differentiableAt.hasDerivAt.pow 2).const_mul (3/2:ℂ)).fun_mul
      ak.deriv.differentiableAt.hasDerivAt)
  simp only [Pi.pow_apply] at z
  rw [eq.deriv_eq,z.deriv]
  ring

private theorem height_deriv {k:ℂ→ℂ} {s a b:ℂ} (ak:AnalyticAt ℂ k s) (nk:k s≠0)
    (eq:ordinaryResidual a b k s=0) :
    HasDerivAt (ordinaryHeight b k) (a-k s*ordinaryForce k s) s := by
  have z := (((force_analytic ak).deriv.differentiableAt.hasDerivAt).add_const b).fun_div
    ak.differentiableAt.hasDerivAt nk
  apply z.congr_deriv
  rw [force_deriv ak,force_second ak]
  dsimp only [ordinaryForce,ordinaryResidual,ordinaryQuadratic,ordinaryQuartic] at eq ⊢
  field_simp
  linear_combination eq

/-- Recover all three stress coordinates and all four differential laws from
ordinary scalar curvature germs wherever the covering curvature does not vanish. -/
theorem laws_of_scalar_charts {q:ℕ} (hq:0<q) (a b s₀:ℂ) {f:ℂ→ℂ}
    (charts : ∀ᶠ w in 𝓝[≠] (0:ℂ), ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
      (f =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0)
    (nonzero : ∀ᶠ w in 𝓝[≠] (0:ℂ),f w≠0) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ),Laws q a b f (ds q f) (branchForce q f) (branchHeight q b f) w := by
  filter_upwards [charts,nonzero,eventually_mem_nhdsWithin] with w chart nfw nw
  obtain ⟨k,ak,rep,eq⟩ := chart
  have d1 := ds_of_branch_germ hq nw ak rep
  have d2 := ds_of_branch_germ hq nw ak.deriv d1
  have fRep : branchForce q f =ᶠ[𝓝 w] fun z=>ordinaryForce k (s₀+z^q) := by
    filter_upwards [d2,rep] with z h₂ h
    simp only [branchForce,ordinaryForce,h₂,h]
  have dF := ds_of_branch_germ hq nw (force_analytic ak) fRep
  have hRep : branchHeight q b f =ᶠ[𝓝 w] fun z=>ordinaryHeight b k (s₀+z^q) := by
    filter_upwards [dF,rep] with z h₁ h
    simp only [branchHeight,ordinaryHeight,h₁,h]
  have nk : k (s₀+w^q)≠0 := by rwa [←rep.eq_of_nhds]
  have pw : HasDerivAt (fun z:ℂ=>s₀+z^q) (speed q w) w := by
    simpa [speed] using (((hasDerivAt_id w).pow q).const_add s₀)
  have first := ((ak.differentiableAt.hasDerivAt.comp w pw).congr_of_eventuallyEq rep)
  have second := ((ak.deriv.differentiableAt.hasDerivAt.comp w pw).congr_of_eventuallyEq d1)
  have third := (((force_analytic ak).differentiableAt.hasDerivAt.comp w pw).congr_of_eventuallyEq fRep)
  have fourth := (((height_deriv ak nk eq).comp w pw).congr_of_eventuallyEq hRep)
  refine ⟨first.congr_deriv ?_,second.congr_deriv ?_,third.congr_deriv ?_,fourth.congr_deriv ?_⟩
  · rw [d1.eq_of_nhds,mul_comm]
  · rw [fRep.eq_of_nhds,rep.eq_of_nhds];dsimp [ordinaryForce];ring
  · rw [rep.eq_of_nhds,hRep.eq_of_nhds];dsimp [ordinaryHeight];field_simp;ring
  · rw [rep.eq_of_nhds,fRep.eq_of_nhds,mul_comm]

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.laws_of_scalar_charts
