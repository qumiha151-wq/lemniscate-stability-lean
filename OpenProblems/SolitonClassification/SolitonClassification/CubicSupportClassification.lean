import SolitonClassification.CubicSupportRigidity
import SolitonClassification.ReflectedMarker
import SolitonClassification.NoClosedTranslators
import SolitonClassification.SingleValuedForce
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! A cubic physical force law selects the Bernoulli support trajectory at
dilation coefficient one. The positive simple inflection and its initial
state are derived from the closed Frenet curve. -/
noncomputable section
namespace ClosedSimilarity
open Set Filter ReflectedArc ReflectedMarker
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace PeriodicSupportProfile
variable {L : ℝ} (z : PeriodicSupportProfile 1 0 L)

def dilationState (s : ℝ) : Support := ![z.k s,z.v s,z.p s,z.q s]

theorem dilationState_solves : Solves z.dilationState := by
  intro s
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact z.dk s
  · simpa [dilationState,supportField] using z.dv s
  · exact z.dp s
  · exact z.dq s

private theorem curvature_signs (hL : 0<L) (hn : ¬∃ c, ∀ s, z.k s=c) :
    ∃ x y, z.k x<0 ∧ 0<z.k y := by
  obtain ⟨⟨x,hx⟩,y,hy⟩ := z.both_curvature_excursions_of_period hL hn
  have h := z.curvatureRMS_pos (z.dilation_pos hL) hL
  exact ⟨x,y,by linarith,by linarith⟩

private theorem cubic_zero_simple {a d j c : ℝ}
    (he : ∀ s, z.p s=a*z.k s^3+d*z.k s^2+j*z.k s+c)
    {x y s₀ : ℝ} (hx : z.k x<0) (hy : 0<z.k y) (hk : z.k s₀=0) :
    z.v s₀≠0 := by
  intro hv
  let W (u : ℝ) := (1/4+a/2)*u^4+(2*d/3)*u^3+j*u^2+2*c*u
  have dW (s : ℝ) : HasDerivAt W
      (4*(1/4+a/2)*s^3+3*(2*d/3)*s^2+2*j*s+2*c) s := by
    convert! (((((hasDerivAt_id s).pow 4).const_mul (1/4+a/2)).add
      (((hasDerivAt_id s).pow 3).const_mul (2*d/3))).add
      (((hasDerivAt_id s).pow 2).const_mul j)).add ((hasDerivAt_id s).const_mul (2*c))
      using 1
    simp only [id_eq]
    ring
  let E (s : ℝ) := z.v s^2+W (z.k s)
  have dE (s : ℝ) : HasDerivAt E 0 s := by
    convert! ((z.dv s).pow 2).add ((dW (z.k s)).comp s (z.dk s)) using 1
    rw [he]
    ring
  have ee (s : ℝ) : E s=0 := by
    have h := is_const_of_deriv_eq_zero (fun t => (dE t).differentiableAt)
      (fun t => (dE t).deriv) s s₀
    simpa [E,W,hk,hv] using h
  have wm : IsLocalMax W 0 := by
    filter_upwards [Ioo_mem_nhds hx hy] with u hu
    obtain ⟨s,hs⟩ := intermediate_value_univ x y z.continuous_k
      (show u∈Icc (z.k x) (z.k y) from ⟨hu.1.le,hu.2.le⟩)
    have h := ee s
    change z.v s^2+W (z.k s)=0 at h
    rw [hs] at h
    have W₀ : W 0=0 := by simp [W]
    rw [W₀]
    linarith [sq_nonneg (z.v s)]
  have hc : c=0 := by
    have h := wm.hasDerivAt_eq_zero (dW 0)
    norm_num at h
    linarith
  let line (t : ℝ) : Support := ![0,0,0,z.q s₀+(t-s₀)]
  have hline : Solves line := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [line,supportField] using hasDerivAt_const t (0:ℝ)
    · simpa [line,supportField] using hasDerivAt_const t (0:ℝ)
    · simpa [line,supportField] using hasDerivAt_const t (0:ℝ)
    · simpa [line,supportField] using ((hasDerivAt_id t).sub_const s₀).const_add (z.q s₀)
  have initial : z.dilationState s₀=line s₀ := by simp [dilationState,line,hk,hv,he,hc]
  have eq := support_unique z.dilationState_solves hline initial
  have zero : z.k y=0 := congrFun (congrFun eq y) 0
  linarith

private theorem upward_zero (hL : 0<L) {x y : ℝ}
    (hx : z.k x<0) (hy : 0<z.k y) :
    ∃ s, z.k s=0 ∧ 0≤z.v s := by
  obtain ⟨b,hb,eb⟩ := z.periodic_k.exists_mem_Ico hL y x
  have bypos : 0<z.k b := eb ▸ hy
  let Z := Icc x b ∩ z.k ⁻¹' ({0}:Set ℝ)
  obtain ⟨s',hs',hz'⟩ := intermediate_value_Icc hb.1 z.continuous_k.continuousOn
    (show (0:ℝ)∈Icc (z.k x) (z.k b) from ⟨hx.le,bypos.le⟩)
  have compact : IsCompact Z :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage z.continuous_k)
  obtain ⟨s,hs,hm⟩ := compact.exists_isMinOn ⟨s',hs',hz'⟩ continuous_id.continuousOn
  have ks : z.k s=0 := hs.2
  have xs : x<s := lt_of_le_of_ne hs.1.1 (by rintro rfl; linarith)
  refine ⟨s,ks,ge_of_tendsto (hasDerivAt_iff_tendsto_slope_left_right.mp (z.dk s)).1 ?_⟩
  filter_upwards [Ioo_mem_nhdsLT xs] with t ht
  have tk : z.k t<0 := by
    by_contra! htpos
    obtain ⟨u,hu,ku⟩ := intermediate_value_Icc ht.1.le z.continuous_k.continuousOn
      (show (0:ℝ)∈Icc (z.k x) (z.k t) from ⟨hx.le,htpos⟩)
    have huZ : u∈Z := ⟨⟨hu.1,hu.2.trans (ht.2.le.trans hs.1.2)⟩,ku⟩
    have su : s≤u := hm huZ
    linarith [hu.2,ht.2]
  rw [slope_def_field,ks,sub_zero]
  exact div_nonneg_of_nonpos tk.le (sub_nonpos.mpr ht.2.le)

/-- All nonconstant normalized periodic solutions with a polynomial support
law of degree at most three pass through the same positive marker state. -/
theorem cubic_support_canonical_state (hL : 0<L) (hn : ¬∃ c, ∀ s, z.k s=c)
    {a d j c : ℝ} (he : ∀ s, z.p s=a*z.k s^3+d*z.k s^2+j*z.k s+c) :
    a= -5/18 ∧ d=0 ∧ j=0 ∧ c=0 ∧
    ∃ s, z.dilationState s=![0,Real.sqrt (6/5),0,0] := by
  obtain ⟨x,y,hx,hy⟩ := z.curvature_signs hL hn
  obtain ⟨s,hs,hv⟩ := z.upward_zero hL hx hy
  have hnz := z.cubic_zero_simple he hx hy hs
  obtain ⟨ha,hd,hj,hc,hm⟩ := z.cubic_support_at_simple_inflection he hs hnz
  subst a d j c
  have pe (t : ℝ) : z.p t= -5/18*z.k t^3 := by simpa using he t
  have kv (t : ℝ) : z.k t*z.q t=5/6*z.k t^2*z.v t := by
    have h := z.dp t
    rw [show z.p=(fun w => -5/18*z.k w^3) from funext pe] at h
    have e := h.unique (((z.dk t).pow 3).const_mul (-5/18))
    linear_combination -e
  have lhs := (z.dk s).mul (z.dq s)
  have rhs := ((((z.dk s).pow 2).const_mul (5/6)).mul (z.dv s))
  have fe : z.k*z.q=(fun w => 5/6*(z.k^2) w)*z.v := funext kv
  rw [fe] at lhs
  have e := lhs.unique rhs
  simp [hs] at e
  have hq := e.resolve_left hnz
  have hvs : z.v s=Real.sqrt (6/5) := by
    rw [←hm,Real.sqrt_sq hv]
  exact ⟨rfl,rfl,rfl,rfl,s,by simp [dilationState,hs,hvs,pe,hq]⟩

end PeriodicSupportProfile

namespace ClosedUnitFrenetCurve
private def normalizedSupport (C : ClosedUnitFrenetCurve) (ω : ℝ)
    (hp : ∀s,C.force s= -C.normalSupport s-ω*C.tangentSupport s) :
    PeriodicSupportProfile 1 ω C.period where
  k := C.k
  v := C.v
  p := C.normalSupport
  q := C.tangentSupport
  dk := C.dk
  dv := fun s => by
    convert C.dv s using 1
    have h := hp s
    dsimp only [force] at h
    linarith
  dp := C.normalSupport_hasDerivAt
  dq := C.tangentSupport_hasDerivAt
  periodic_k := C.periodic_k
  periodic_v := C.periodic_v
  periodic_p := C.periodic_normalSupport
  periodic_q := C.periodic_tangentSupport

def supportPath (C : ClosedUnitFrenetCurve) (t : ℝ) : Support :=
  ![C.k t,C.v t,C.normalSupport t,C.tangentSupport t]

/-- The hypotheses use force and curvature calculated from position coordinates.
The last clause is uniqueness of the entire support orbit, at the positive
Bernoulli initial state. -/
theorem cubic_force_selects_bernoulli (C : ClosedUnitFrenetCurve)
    (hp : ∀ s, C.positionForce s= -C.normalSupport s)
    (hn : ¬∃ k₀, ∀ s, C.positionCurvature s=k₀) {a d j c : ℝ}
    (he : ∀ s,C.positionForce s=a*C.positionCurvature s^3+
      d*C.positionCurvature s^2+j*C.positionCurvature s+c) :
    a=5/18 ∧ d=0 ∧ j=0 ∧ c=0 ∧
    ∃ s, C.x s=0 ∧ C.y s=0 ∧ C.positionCurvature s=0 ∧ C.v s=Real.sqrt (6/5) ∧
    ∀ B : ℝ → Support, Solves B → B 0=![0,Real.sqrt (6/5),0,0] →
      ∀ t,C.supportPath (t+s)=B t := by
  rw [C.positionForce_eq] at hp he
  rw [C.positionCurvature_eq] at hn he ⊢
  let z := C.normalizedSupport 0 (by simpa using hp)
  have poly (s : ℝ) : z.p s=(-a)*z.k s^3+(-d)*z.k s^2+(-j)*z.k s+(-c) := by
    change C.normalSupport s=_
    change C.normalSupport s=(-a)*C.k s^3+(-d)*C.k s^2+(-j)*C.k s+(-c)
    linarith [he s,hp s]
  obtain ⟨ha,hd,hj,hc,s,hs⟩ := z.cubic_support_canonical_state C.period_pos hn poly
  have ks : C.k s=0 := congrFun hs 0
  have vs : C.v s=Real.sqrt (6/5) := congrFun hs 1
  have ps : C.normalSupport s=0 := congrFun hs 2
  have qs : C.tangentSupport s=0 := congrFun hs 3
  have hx : C.x s=0 := by
    dsimp only [normalSupport] at ps
    dsimp only [tangentSupport] at qs
    linear_combination -(C.ty s)*ps+(C.tx s)*qs-(C.x s)*(C.unit s)
  have hy : C.y s=0 := by
    dsimp only [normalSupport] at ps
    dsimp only [tangentSupport] at qs
    linear_combination (C.tx s)*ps+(C.ty s)*qs-(C.y s)*(C.unit s)
  refine ⟨by linarith,by linarith,by linarith,by linarith,s,hx,hy,ks,vs,?_⟩
  intro B dB start
  have dS : Solves (fun t => z.dilationState (t+s)) :=
    fun t => (z.dilationState_solves (t+s)).comp_add_const t s
  have match0 : z.dilationState (0+s)=B 0 := by simpa using hs.trans start.symm
  have eq := support_unique dS dB (a:=0) match0
  exact fun t => congrFun eq t

theorem cubic_force_excludes_rotation_and_selects_bernoulli (C : ClosedUnitFrenetCurve) {ω : ℝ}
    (hp : ∀ s, C.positionForce s= -C.normalSupport s-ω*C.tangentSupport s)
    (hn : ¬∃ k₀, ∀ s, C.positionCurvature s=k₀) {a d j c : ℝ}
    (he : ∀ s,C.positionForce s=a*C.positionCurvature s^3+
      d*C.positionCurvature s^2+j*C.positionCurvature s+c) :
    ω=0 ∧ a=5/18 ∧ d=0 ∧ j=0 ∧ c=0 ∧
    ∃ s, C.x s=0 ∧ C.y s=0 ∧ C.positionCurvature s=0 ∧ C.v s=Real.sqrt (6/5) ∧
    ∀ B : ℝ → Support, Solves B → B 0=![0,Real.sqrt (6/5),0,0] →
      ∀ t,C.supportPath (t+s)=B t := by
  let z := C.normalizedSupport ω (by simpa only [C.positionForce_eq] using hp)
  have hω : ω=0 := by
    apply z.angular_rate_zero_of_continuous_force_law C.period_pos
      (by change ¬∃ k₀,∀ s,C.k s=k₀; simpa only [C.positionCurvature_eq] using hn)
      (G:=fun u => a*u^3+d*u^2+j*u+c) (by fun_prop)
    intro t
    change -1*C.normalSupport t-ω*C.tangentSupport t=_
    change -1*C.normalSupport t-ω*C.tangentSupport t=a*C.k t^3+d*C.k t^2+j*C.k t+c
    rw [←C.positionCurvature_eq]
    linarith [he t,hp t]
  subst ω
  exact ⟨rfl,C.cubic_force_selects_bernoulli (by simpa using hp) hn he⟩

end ClosedUnitFrenetCurve
end ClosedSimilarity
#print axioms ClosedSimilarity.PeriodicSupportProfile.cubic_support_canonical_state
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.cubic_force_selects_bernoulli
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.cubic_force_excludes_rotation_and_selects_bernoulli
