import SolitonClassification.RamifiedBaseResidual
import SolitonClassification.MeromorphicPoleExtension

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified

private theorem residual_germ {a b x : ℂ} {f g : ℂ→ℂ} (e:f=ᶠ[𝓝[≠] x] g) :
    ordinaryResidual a b f=ᶠ[𝓝[≠] x] ordinaryResidual a b g := by
  have e₁ := e.nhdsNE_deriv
  have e₂ := e₁.nhdsNE_deriv
  have e₃ := e₂.nhdsNE_deriv
  have e₄ := e₃.nhdsNE_deriv
  filter_upwards [e,e₁,e₂,e₃,e₄] with z h h₁ h₂ h₃ h₄
  simp only [ordinaryResidual,ordinaryQuadratic,ordinaryQuartic,h,h₁,h₂,h₃,h₄]

private theorem residual_analytic {a b x:ℂ} {H:ℂ→ℂ} (ak:AnalyticAt ℂ H x) :
    AnalyticAt ℂ (ordinaryResidual a b H) x := by
  have d₁ := ak.deriv
  have d₂ := d₁.deriv
  have d₃ := d₂.deriv
  have d₄ := d₃.deriv
  unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
  fun_prop

/-- A true analytic filling, or a simple pole with no regular terms of
degrees zero, one, or two. The cubic defect is holomorphic and zero at
the pole. Values assigned to a meromorphic representative at its pole
do not enter any of the punctured equalities. -/
def OrdinaryEnd (a b x:ℂ) (G:ℂ→ℂ) : Prop :=
  (∃H:ℂ→ℂ,AnalyticAt ℂ H x ∧ G=ᶠ[𝓝[≠] x] H ∧ ordinaryResidual a b H x=0) ∨
  (meromorphicOrderAt G x=((-1:ℤ):WithTop ℤ) ∧ ∃c:ℂ,
    (c=3*I ∨ c= -(3*I)) ∧
    (∃R:ℂ→ℂ,AnalyticAt ℂ R x ∧
      G=ᶠ[𝓝[≠] x] fun s=>c/(s-x)+(s-x)^3*R s) ∧
    ∃E:ℂ→ℂ,AnalyticAt ℂ E x ∧ E x=0 ∧
      (fun s=>deriv (deriv G) s+2*(G s)^3/9)=ᶠ[𝓝[≠] x] E)

theorem ordinary_end_of_solution {a b:ℝ} (ha:0<a) {x:ℂ} {G:ℂ→ℂ}
    (mg:MeromorphicAt G x)
    (eq:ordinaryResidual (a:ℂ) (b:ℂ) G=ᶠ[𝓝[≠] x] fun _=>0) :
    OrdinaryEnd a b x G := by
  by_cases regular : 0≤meromorphicOrderAt G x
  · left
    obtain ⟨H,ah,rep⟩:= mg.meromorphicOrderAt_nonneg_iff.mp regular
    have van := (residual_germ (a:=(a:ℂ)) (b:=(b:ℂ)) rep).symm.trans eq
    have con : ContinuousWithinAt (ordinaryResidual (a:ℂ) (b:ℂ) H) {x}ᶜ x := (residual_analytic (a:=(a:ℂ)) (b:=(b:ℂ)) ah).continuousAt.continuousWithinAt
    exact ⟨H,ah,rep,tendsto_nhds_unique_of_eventuallyEq (l:=𝓝[≠] x) con tendsto_const_nhds van⟩
  · right
    have top : meromorphicOrderAt G x≠⊤ := by intro t;rw [t] at regular;exact regular le_top
    lift meromorphicOrderAt G x to ℤ using top with n order
    have neg : n<0 := by
      by_contra! nn
      apply regular
      exact WithTop.coe_nonneg.mpr nn
    obtain ⟨on,c,root,_,expan,defect⟩:=pole_expansion (b:=b) ha mg order.symm neg eq
    have sq : c^2=(3*I)^2 := by rw [root,mul_pow,I_sq];norm_num
    exact ⟨by rw [on],c,sq_eq_sq_iff_eq_or_eq_neg.mp sq,expan,defect⟩

/-- Finite power-cover solution germs on a punctured disk descend, solve the
ordinary scalar equation, and have exactly the ordinary removable or simple
pole alternatives for positive real dilation and real angular velocity. -/
theorem finite_cover_ordinary_end {q:ℕ} (hq:0<q) {r:ℝ} (hr:0<r)
    {a b:ℝ} (ha:0<a) (s₀:ℂ) (f:ℂ→ℂ) (charts:PuncturedCharts q r a b s₀ f) :
    ∃G:ℂ→ℂ,MeromorphicAt G s₀ ∧ (f=ᶠ[𝓝[≠] (0:ℂ)] fun w=>G (s₀+w^q)) ∧
      (∀ᶠ s in 𝓝[≠] s₀,AnalyticAt ℂ G s ∧ ordinaryResidual a b G s=0) ∧
      OrdinaryEnd a b s₀ G := by
  obtain ⟨G,mg,rep,good⟩:=finite_cover_base_solution hq hr a b s₀ f charts
  exact ⟨G,mg,rep,good,ordinary_end_of_solution ha mg (good.mono (fun _ h=>h.2))⟩

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.finite_cover_ordinary_end
