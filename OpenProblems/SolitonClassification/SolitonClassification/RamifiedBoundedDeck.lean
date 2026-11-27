import SolitonClassification.RamifiedBoundedStress
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.RamifiedBounded

structure Filled (m : ℕ) (a b : ℂ) where
  k : ℂ→ℂ
  v : ℂ→ℂ
  F : ℂ→ℂ
  h : ℂ→ℂ
  ak : AnalyticAt ℂ k 0
  av : AnalyticAt ℂ v 0
  aF : AnalyticAt ℂ F 0
  ah : AnalyticAt ℂ h 0
  law : ∀ᶠ z in 𝓝 (0:ℂ), Laws m a b k v F h z

theorem fill_derivative {f t r u : ℂ→ℂ}
    (hr : AnalyticAt ℂ r 0) (hu : AnalyticAt ℂ u 0)
    (ef : f=ᶠ[𝓝[≠] 0] r) (et : t=ᶠ[𝓝[≠] 0] u)
    (law : ∀ᶠ z in 𝓝[≠] (0:ℂ),HasDerivAt f (t z) z) :
    ∀ᶠ z in 𝓝 (0:ℂ),HasDerivAt r (u z) z := by
  have left : deriv f=ᶠ[𝓝[≠] (0:ℂ)] t := law.mono (fun _ d=>d.deriv)
  have er := ef.nhdsNE_deriv.symm.trans (left.trans et)
  have all := (hr.deriv.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hu.continuousAt).mp er
  filter_upwards [all,hr.eventually_analyticAt] with z e ar
  rw [←e]
  exact ar.differentiableAt.hasDerivAt

theorem filled_state {m:ℕ} {a b:ℂ} {k v F h:ℂ→ℂ}
    (k₁ : Fills k) (v₁ : Fills v) (F₁ : Fills F) (h₁ : Fills h)
    (law : ∀ᶠ z in 𝓝[≠] (0:ℂ),Laws m a b k v F h z) :
    ∃ Y : Filled m a b, k=ᶠ[𝓝[≠] 0] Y.k ∧ v=ᶠ[𝓝[≠] 0] Y.v ∧
      F=ᶠ[𝓝[≠] 0] Y.F ∧ h=ᶠ[𝓝[≠] 0] Y.h := by
  obtain ⟨K,ak,ek⟩ := k₁
  obtain ⟨V,av,ev⟩ := v₁
  obtain ⟨P,aP,eP⟩ := F₁
  obtain ⟨Q,aQ,eQ⟩ := h₁
  have J := speed_analytic m
  have dK := fill_derivative ak (J.mul av) ek
    (EventuallyEq.rfl.mul ev) (law.mono (fun _ l=>l.1))
  have dV := fill_derivative av (J.mul (aP.sub ((ak.pow 3).div (analyticAt_const (v:=(2:ℂ))) (by norm_num)))) ev
    (by filter_upwards [eP,ek] with z x y; change _=speed m z*(P z-K z^3/2);rw [←x,←y])
    (law.mono (fun _ l=>l.2.1))
  have dP := fill_derivative aP (J.mul ((ak.mul aQ).sub (analyticAt_const (v:=b)))) eP
    (by filter_upwards [ek,eQ] with z x y;change _=speed m z*(K z*Q z-b);rw [←x,←y])
    (law.mono (fun _ l=>l.2.2.1))
  have dQ := fill_derivative aQ (J.mul ((analyticAt_const (v:=a)).sub (ak.mul aP))) eQ
    (by filter_upwards [ek,eP] with z x y;change _=speed m z*(a-K z*P z);rw [←x,←y])
    (law.mono (fun _ l=>l.2.2.2))
  exact ⟨⟨K,V,P,Q,ak,av,aP,aQ,dK.and (dV.and (dP.and dQ))⟩,ek,ev,eP,eQ⟩

theorem speed_deck {m : ℕ} (hm : m≠0) {η : ℂ} (he : η^m=1) (z : ℂ) :
    speed m (η*z)*η=speed m z := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  simp only [speed,Nat.succ_sub_one,mul_pow]
  rw [show ((n+1:ℕ):ℂ)*(η^n*z^n)*η=((n+1:ℕ):ℂ)*(η^(n+1)*z^n) by rw [pow_succ];ring,he,one_mul]

abbrev State := ℂ × ℂ × ℂ × ℂ × ℂ

def field (m:ℕ) (a b:ℂ) (p:State) : State :=
  let J := speed m p.1
  let k := p.2.1
  let v := p.2.2.1
  let F := p.2.2.2.1
  let h := p.2.2.2.2
  (1,J*v,J*(F-k^3/2),J*(k*h-b),J*(a-k*F))

def Filled.track {m a b} (Y:Filled m a b) (η:ℂ) (t:ℝ) : State :=
  (t,Y.k (η*t),Y.v (η*t),Y.F (η*t),Y.h (η*t))

theorem Filled.track_derivative {m a b} (Y:Filled m a b) (hm:m≠0) {η:ℂ} (he:η^m=1) :
    ∀ᶠ t in 𝓝 (0:ℝ),HasDerivAt (Y.track η) (field m a b (Y.track η t)) t := by
  have lim : Tendsto (fun t:ℝ=>η*(t:ℂ)) (𝓝 0) (𝓝 0) := by
    simpa only [Complex.ofReal_zero,mul_zero,Pi.mul_apply] using! ((continuous_const.mul Complex.continuous_ofReal).continuousAt
      (x:=(0:ℝ)) : ContinuousAt (fun t:ℝ=>η*(t:ℂ)) 0).tendsto
  filter_upwards [lim.eventually Y.law] with t l
  have trans {f:ℂ→ℂ} {p:ℂ} (d:HasDerivAt f (speed m (η*t)*p) (η*t)) :
      HasDerivAt (fun s:ℝ=>f (η*s)) (speed m (t:ℂ)*p) t := by
    have clk : HasDerivAt (fun z:ℂ=>η*z) η (t:ℂ) := by simpa using (hasDerivAt_id (t:ℂ)).const_mul η
    convert! (d.comp (t:ℂ) clk).comp_ofReal using 1
    linear_combination -p*(speed_deck hm he (t:ℂ))
  have dt : HasDerivAt (fun s:ℝ=>(s:ℂ)) (1:ℂ) t := by simpa using! (Complex.ofRealCLM.hasDerivAt (x:=t))
  exact dt.prodMk ((trans l.1).prodMk ((trans l.2.1).prodMk
    ((trans l.2.2.1).prodMk (trans l.2.2.2))))

theorem Filled.track_unique {m a b} (Y:Filled m a b) (hm:m≠0) {η:ℂ} (he:η^m=1) :
    Y.track η=ᶠ[𝓝 (0:ℝ)] Y.track 1 := by
  have d₁ := Y.track_derivative hm he
  have d₂ := Y.track_derivative (η:=1) hm (one_pow m)
  have initial : Y.track η 0=Y.track 1 0 := by simp [track]
  have sm : ContDiff ℝ 1 (field m a b) := by unfold field speed;fun_prop
  obtain ⟨K,V,hv,lc⟩ := (sm.contDiffAt (x:=Y.track η 0)).exists_lipschitzOnWith
  have av : ∀ᶠ t in 𝓝 (0:ℝ),Y.track η t∈V := d₁.self_of_nhds.continuousAt hv
  have bv : ∀ᶠ t in 𝓝 (0:ℝ),Y.track 1 t∈V := d₂.self_of_nhds.continuousAt (initial ▸ hv)
  exact ODE_solution_unique_of_eventually (v:=fun _=>field m a b) (s:=fun _=>V)
    (Eventually.of_forall (fun _=>lc)) (d₁.and av) (d₂.and bv) initial

theorem Filled.curvature_deck {m a b} (Y:Filled m a b) (hm:m≠0) {η:ℂ} (he:η^m=1) :
    (fun z=>Y.k (η*z))=ᶠ[𝓝 (0:ℂ)] Y.k := by
  have ak : AnalyticAt ℂ (fun z=>Y.k (η*z)) 0 := by
    exact AnalyticAt.comp (by simpa using Y.ak) (by fun_prop : AnalyticAt ℂ (fun z:ℂ=>η*z) 0)
  apply (ak.frequently_eq_iff_eventually_eq Y.ak).mp
  have tr := Y.track_unique hm he
  have eq : ∀ᶠ (t:ℝ) in 𝓝 (0:ℝ),Y.k (η*(t:ℂ))=Y.k (t:ℂ) := by
    filter_upwards [tr] with t e
    simpa [track] using congrArg (fun p:State=>p.2.1) e
  have lim : Tendsto (fun t:ℝ=>(t:ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx
    simpa using hx
  by_contra! ne
  obtain ⟨t,p,q⟩ := ((lim.eventually ne).and (eq.filter_mono nhdsWithin_le_nhds)).exists
  exact p q

#print axioms Filled.curvature_deck
end ClosedSimilarity.RamifiedBounded
