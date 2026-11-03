import Lemniscate.NormalGraphPolynomial
import Lemniscate.NormalGraphComplexVariation
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The real normal-graph equation and its first variation.

The reference parameter is arclength, with t_s = k n and n_s = -k t.
The polynomial jets and complex rational variation are shared with the
Sobolev equation. The real variation follows by restriction to the real axis
and the exact cancellation of the metric square root on regular graphs.
-/
noncomputable section
namespace Lemniscate
open Complex Filter
open scoped Topology

private def graphMetric (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  Real.sqrt (graphMetricSquared K h)

private def graphInverseMetric (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  (graphMetric K h)⁻¹

/-- The geometric elastic force, expressed through the actual spatial jets.
The support is eta = <beta,n> and b = <beta,t>. -/
def normalGraphJetForce (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) : ℝ :=
  graphCurvatureNumeratorSS K h*(graphInverseMetric K h)^5-
    (7/2:ℝ)*graphCurvatureNumeratorS K h*graphMetricSquaredS K h*
      (graphInverseMetric K h)^7-
    (3/2:ℝ)*graphCurvatureNumerator K h*graphMetricSquaredSS K h*
      (graphInverseMetric K h)^7+
    (9/2:ℝ)*graphCurvatureNumerator K h*(graphMetricSquaredS K h)^2*
      (graphInverseMetric K h)^9+
    (1/2:ℝ)*(graphCurvatureNumerator K h)^3*(graphInverseMetric K h)^9+
    c*graphSupportNumerator K h*graphInverseMetric K h

private def graphPrefactor (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  graphMetric K h/graphA K h

def normalGraphJetFlow (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) : ℝ :=
  -(graphPrefactor K h*normalGraphJetForce K c h)

/-- The metric square root cancels from the normal-graph equation. -/
theorem normal_graph_jet_rational (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) (hA : 0 < 1-K.k*h.h) :
    let A := graphA K h
    let H := graphMetricSquared K h
    let H₁ := graphMetricSquaredS K h
    let H₂ := graphMetricSquaredSS K h
    let N := graphCurvatureNumerator K h
    let N₁ := graphCurvatureNumeratorS K h
    let N₂ := graphCurvatureNumeratorSS K h
    let P := graphSupportNumerator K h
    normalGraphJetFlow K c h =
      -A⁻¹*(N₂/H^2-(7/2:ℝ)*N₁*H₁/H^3-(3/2:ℝ)*N*H₂/H^3+
        (9/2:ℝ)*N*H₁^2/H^4+(1/2:ℝ)*N^3/H^4+c*P) := by
  let A := graphA K h
  let H := graphMetricSquared K h
  let g := graphMetric K h
  let H₁ := graphMetricSquaredS K h
  let H₂ := graphMetricSquaredSS K h
  let N := graphCurvatureNumerator K h
  let N₁ := graphCurvatureNumeratorS K h
  let N₂ := graphCurvatureNumeratorSS K h
  let P := graphSupportNumerator K h
  have hA0 : A ≠ 0 := hA.ne'
  have hH : 0 < H := by
    dsimp only [H,graphMetricSquared,graphA]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hA) (sq_nonneg _)
  have hg0 : g ≠ 0 := (Real.sqrt_pos.2 hH).ne'
  have hg2 : g^2 = H := Real.sq_sqrt hH.le
  change -(g/A*(N₂*(g⁻¹)^5-(7/2:ℝ)*N₁*H₁*(g⁻¹)^7-
      (3/2:ℝ)*N*H₂*(g⁻¹)^7+(9/2:ℝ)*N*H₁^2*(g⁻¹)^9+
      (1/2:ℝ)*N^3*(g⁻¹)^9+c*P*g⁻¹)) =
    -A⁻¹*(N₂/H^2-(7/2:ℝ)*N₁*H₁/H^3-(3/2:ℝ)*N*H₂/H^3+
      (9/2:ℝ)*N*H₁^2/H^4+(1/2:ℝ)*N^3/H^4+c*P)
  rw [← hg2]
  field_simp [hA0,hg0] <;> ring

/-- On regular real graphs the rational flow is the geometric jet flow. -/
theorem normal_graph_rational_flow_real (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) (hA : 0 < 1-K.k*h.h) :
    normalGraphRationalFlow K c h = normalGraphJetFlow K c h := by
  rw [normal_graph_jet_rational K c h hA]
  simp only [normalGraphRationalFlow,Ring.inverse_eq_inv,smul_eq_mul,
    div_eq_mul_inv,inv_pow]
  <;> ring

private def complexBackgroundJet (K : NormalGraphBackgroundJet) : BackgroundJetOver ℂ :=
  ⟨K.k,K.ks,K.kss,K.ksss,K.eta,K.b⟩

private def complexHeightJet (F : NormalGraphHeightJet) : HeightJetOver ℂ :=
  ⟨F.h,F.hs,F.hss,F.hsss,F.hssss⟩

theorem normal_graph_rational_flow_ofReal (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) :
    normalGraphRationalFlow (complexBackgroundJet K) c (complexHeightJet h) =
      ((normalGraphRationalFlow K c h : ℝ) : ℂ) := by
  simp only [normalGraphRationalFlow,complexBackgroundJet,complexHeightJet,
    graphCurvatureNumeratorSS,graphCurvatureNumeratorS,graphCurvatureNumerator,
    graphMetricSquaredSS,graphMetricSquaredS,graphMetricSquared,
    graphSupportNumerator,graphAss,graphAs,graphA,Ring.inverse_eq_inv,
    real_smul,smul_eq_mul]
  push_cast <;> rfl

/-- Restricting the complex rational variation gives the real geometric
variation, because A stays positive in a neighborhood of zero height. -/
theorem normal_graph_jet_flow_hasDerivAt (K : NormalGraphBackgroundJet) (c : ℝ)
    (F : NormalGraphHeightJet) :
    HasDerivAt (fun ε : ℝ => normalGraphJetFlow K c (normalGraphScaleHeight ε F))
      (-F.hssss-(5/2:ℝ)*K.k^2*F.hss-(5*K.k*K.ks-c*K.b)*F.hs-
        (3*K.ks^2+4*K.k*K.kss+(3/2:ℝ)*K.k^4+c)*F.h) 0 := by
  let Kc := complexBackgroundJet K
  let Fc := complexHeightJet F
  let D : ℝ := -F.hssss-(5/2:ℝ)*K.k^2*F.hss-(5*K.k*K.ks-c*K.b)*F.hs-
    (3*K.ks^2+4*K.k*K.kss+(3/2:ℝ)*K.k^4+c)*F.h
  have hD :
      -Fc.hssss-(5/2:ℂ)*Kc.k^2*Fc.hss-(5*Kc.k*Kc.ks-(c:ℂ)*Kc.b)*Fc.hs-
        (3*Kc.ks^2+4*Kc.k*Kc.kss+(3/2:ℂ)*Kc.k^4+(c:ℂ))*Fc.h = (D:ℂ) := by
    dsimp only [D,Kc,Fc,complexBackgroundJet,complexHeightJet]
    push_cast <;> rfl
  have hc := normal_graph_complex_rational_flow_hasDerivAt Kc c Fc
  rw [hD] at hc
  change HasDerivAt
    (fun ε : ℂ => normalGraphRationalFlow Kc c (normalGraphScaleHeight ε Fc))
    (D:ℂ) 0 at hc
  have hcast (ε : ℝ) :
      normalGraphRationalFlow Kc c (normalGraphScaleHeight (ε:ℂ) Fc) =
        ((normalGraphRationalFlow K c (normalGraphScaleHeight ε F) : ℝ) : ℂ) := by
    have hs : normalGraphScaleHeight (ε:ℂ) Fc =
        complexHeightJet (normalGraphScaleHeight ε F) := by
      simp [normalGraphScaleHeight,complexHeightJet,Fc]
    rw [hs]
    exact normal_graph_rational_flow_ofReal K c _
  have hr : HasDerivAt
      (fun ε : ℝ => normalGraphRationalFlow K c (normalGraphScaleHeight ε F)) D 0 := by
    simpa only [hcast,Complex.ofReal_re] using hc.real_of_complex
  have hA : ∀ᶠ ε : ℝ in 𝓝 0, 0 < 1-K.k*(ε*F.h) :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0).eventually_lt
      (by fun_prop) (by norm_num)
  have heq :
      (fun ε : ℝ => normalGraphJetFlow K c (normalGraphScaleHeight ε F)) =ᶠ[𝓝 0]
      (fun ε : ℝ => normalGraphRationalFlow K c (normalGraphScaleHeight ε F)) := by
    filter_upwards [hA] with ε hε
    exact (normal_graph_rational_flow_real K c (normalGraphScaleHeight ε F) hε).symm
  exact hr.congr_of_eventuallyEq heq

/-- The real principal coefficient follows from the shared algebraic identity. -/
theorem normal_graph_jet_quasilinear (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) (hA : 0 < 1-K.k*h.h) :
    normalGraphJetFlow K c h =
      -(((1-K.k*h.h)^2+h.hs^2)^2)⁻¹*h.hssss+
        normalGraphJetFlow K c {h with hssss := 0} := by
  have hu : IsUnit (graphA K h) := isUnit_iff_ne_zero.mpr hA.ne'
  rw [← normal_graph_rational_flow_real K c h hA,
    ← normal_graph_rational_flow_real K c {h with hssss := 0} hA]
  simpa only [Ring.inverse_eq_inv,graphMetricSquared,graphA,inv_pow] using
    normal_graph_rational_flow_quasilinear K c h hu

/- Physical D_s = sqrt(2) D_x, k = 3q, k_s = 3sqrt(2)p,
k_ss = -6q^3 and b = sqrt(2)qp. -/
theorem bernoulli_normal_graph_linearization_scaling (q p f f₁ f₂ f₄ : ℝ)
    (he : 2*p^2+q^4=1) :
    -(4*f₄)-(5/2:ℝ)*(3*q)^2*(2*f₂)-
      (5*(3*q)*(3*Real.sqrt 2*p)-(15/2:ℝ)*(Real.sqrt 2*q*p))*(Real.sqrt 2*f₁)-
      (3*(3*Real.sqrt 2*p)^2+4*(3*q)*(-6*q^3)+(3/2:ℝ)*(3*q)^4+15/2)*f =
    -4*f₄-45*q^2*f₂-75*q*p*f₁-(69/2:ℝ)*f-(45/2:ℝ)*q^4*f := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  linear_combination -((75/2:ℝ)*q*p*f₁+27*p^2*f)*hs - (27*f)*he

end Lemniscate
