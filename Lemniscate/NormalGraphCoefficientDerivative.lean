import Lemniscate.NormalGraphRationalSmoothness
import Lemniscate.NormalGraphRationalIdentities
import Lemniscate.NormalGraphComplexVariation
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The Frechet derivative of the lower-order normal-graph coefficient.

The existing Banach-algebra smoothness theorem supplies a genuine Frechet
derivative first. Its values are identified using complex directional
derivatives and continuous point evaluation; a directional derivative alone
is not substituted for Frechet differentiability.
-/
noncomputable section
namespace Lemniscate
open Complex Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

def normalGraphLowerOrderDerivative (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) : (Fin 4 → C(AddCircle T, ℂ)) →L[ℂ] C(AddCircle T, ℂ) :=
  (-(5/2:ℝ)) •
      ((ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ) (K.k^2)).comp
        (ContinuousLinearMap.proj 2))-
    (ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ) ((5:ℂ) • (K.k*K.ks)-c • K.b)).comp
      (ContinuousLinearMap.proj 1)-
    (ContinuousLinearMap.mul ℂ C(AddCircle T, ℂ)
      ((3:ℂ) • K.ks^2+(4:ℂ) • (K.k*K.kss)+(3/2:ℝ) • K.k^4+c • 1)).comp
      (ContinuousLinearMap.proj 0)

theorem normal_graph_lower_order_hasFDerivAt
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) :
    HasFDerivAt (normalGraphLowerOrderCoefficient T K c)
      (normalGraphLowerOrderDerivative T K c) 0 := by
  obtain ⟨hopen,hzero,hsmooth⟩ := normal_graph_coefficients_smooth T K c
  have hdiff : DifferentiableAt ℂ (normalGraphLowerOrderCoefficient T K c) 0 :=
    ((hsmooth 0 hzero).snd).differentiableAt (by simp)
  let D := fderiv ℂ (normalGraphLowerOrderCoefficient T K c) 0
  have hD : HasFDerivAt (normalGraphLowerOrderCoefficient T K c) D 0 :=
    hdiff.hasFDerivAt
  have hidentify : D = normalGraphLowerOrderDerivative T K c := by
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousMap.ext
    intro x
    have hray : HasDerivAt (fun ε : ℂ => ε • v) v 0 := by
      simpa only [id_eq,one_smul] using! (hasDerivAt_id (0:ℂ)).smul_const v
    have hDray : HasFDerivAt (normalGraphLowerOrderCoefficient T K c) D
        ((0:ℂ) • v) := by
      simpa only [zero_smul] using hD
    have hbray : HasDerivAt
        (fun ε : ℂ => normalGraphLowerOrderCoefficient T K c (ε • v)) (D v) 0 := by
      simpa only [Function.comp_def] using hDray.comp_hasDerivAt 0 hray
    have heval : HasDerivAt
        (fun ε : ℂ => normalGraphLowerOrderCoefficient T K c (ε • v) x) (D v x) 0 := by
      simpa only [Function.comp_def,ContinuousMap.evalCLM_apply] using
        (ContinuousMap.evalCLM ℂ x).hasFDerivAt.comp_hasDerivAt 0 hbray
    have htend : Tendsto (fun ε : ℂ => ε • v) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul] using hray.continuousAt.tendsto
    have hunit : ∀ᶠ ε : ℂ in 𝓝 0,
        (ε • v) ∈ normalGraphCoefficientDomain T K :=
      htend.eventually (hopen.mem_nhds hzero)
    let Kx : BackgroundJetOver ℂ :=
      ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩
    let V : HeightJetOver ℂ := ⟨v 0 x,v 1 x,v 2 x,v 3 x,0⟩
    have heq :
        (fun ε : ℂ => normalGraphLowerOrderCoefficient T K c (ε • v) x) =ᶠ[𝓝 0]
        (fun ε : ℂ => normalGraphRationalFlow Kx c
          ⟨ε*V.h,ε*V.hs,ε*V.hss,ε*V.hsss,ε*V.hssss⟩) := by
      filter_upwards [hunit] with ε hε
      have h := normal_graph_rational_flow_apply T K c
        ⟨(ε • v) 0,(ε • v) 1,(ε • v) 2,(ε • v) 3,0⟩ hε.1 hε.2 x
      simpa only [normalGraphLowerOrderCoefficient,Kx,V,Pi.smul_apply,
        ContinuousMap.smul_apply,smul_eq_mul,ContinuousMap.zero_apply,mul_zero] using h
    have hscalar := (normal_graph_complex_rational_flow_hasDerivAt Kx c V).congr_of_eventuallyEq heq
    have hvalue : D v x =
        -(5/2:ℂ)*(K.k x)^2*(v 2 x)-
          (5*K.k x*K.ks x-(c:ℂ)*K.b x)*(v 1 x)-
          (3*(K.ks x)^2+4*K.k x*K.kss x+(3/2:ℂ)*(K.k x)^4+(c:ℂ))*(v 0 x) := by
      simpa only [Kx,V,neg_zero,zero_sub,neg_mul] using heval.unique hscalar
    rw [hvalue]
    simp only [normalGraphLowerOrderDerivative,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply,ContinuousLinearMap.mul_apply',
      ContinuousMap.smul_apply,ContinuousMap.sub_apply,ContinuousMap.add_apply,
      ContinuousMap.mul_apply,ContinuousMap.pow_apply,ContinuousMap.natCast_apply,
      ContinuousMap.one_apply,real_smul]
    push_cast
    ring
  rw [← hidentify]
  exact hD

end Lemniscate
