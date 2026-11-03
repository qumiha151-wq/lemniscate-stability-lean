import Lemniscate.Algebra
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add

/-! First variation of the exact finite-jet normal-graph equation.

The reference parameter is arclength, with t_s=k n and n_s=-k t.
The normal support is eta=<beta,n>; b=<beta,t> is the tangential support.
This file calculates the epsilon derivative of the graph equation; the
separate geometric bridge identifies these finite jets with actual derivatives
of beta+h n. No normal-variation formula is assumed here.
-/
noncomputable section
namespace Lemniscate

structure NormalGraphBackgroundJet where
  k : ℝ
  ks : ℝ
  kss : ℝ
  ksss : ℝ
  eta : ℝ
  b : ℝ

structure NormalGraphHeightJet where
  h : ℝ
  hs : ℝ
  hss : ℝ
  hsss : ℝ
  hssss : ℝ

def normalGraphScaleHeight (ε : ℝ) (f : NormalGraphHeightJet) : NormalGraphHeightJet :=
  ⟨ε*f.h,ε*f.hs,ε*f.hss,ε*f.hsss,ε*f.hssss⟩

private def graphA (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  1-K.k*h.h

private def graphAs (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  -K.ks*h.h-K.k*h.hs

private def graphAss (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  -K.kss*h.h-2*K.ks*h.hs-K.k*h.hss

private def graphMetricSquared (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  (graphA K h)^2+h.hs^2

private def graphMetricSquaredS (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  2*graphA K h*graphAs K h+2*h.hs*h.hss

private def graphMetricSquaredSS (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  2*(graphAs K h)^2+2*graphA K h*graphAss K h+2*h.hss^2+2*h.hs*h.hsss

private def graphMetric (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  Real.sqrt (graphMetricSquared K h)

private def graphInverseMetric (K : NormalGraphBackgroundJet) (h : NormalGraphHeightJet) : ℝ :=
  (graphMetric K h)⁻¹

/- The numerator is det(Z_s,Z_ss). Its next two definitions are the exact
spatial derivatives obtained from the Frenet rules and the supplied jets. -/
private def graphCurvatureNumerator (K : NormalGraphBackgroundJet)
    (h : NormalGraphHeightJet) : ℝ :=
  K.k*(graphA K h)^2+graphA K h*h.hss+K.ks*h.h*h.hs+2*K.k*h.hs^2

private def graphCurvatureNumeratorS (K : NormalGraphBackgroundJet)
    (h : NormalGraphHeightJet) : ℝ :=
  K.ks*(graphA K h)^2+2*K.k*graphA K h*graphAs K h+
    graphAs K h*h.hss+graphA K h*h.hsss+K.kss*h.h*h.hs+
    3*K.ks*h.hs^2+K.ks*h.h*h.hss+4*K.k*h.hs*h.hss

private def graphCurvatureNumeratorSS (K : NormalGraphBackgroundJet)
    (h : NormalGraphHeightJet) : ℝ :=
  K.kss*(graphA K h)^2+4*K.ks*graphA K h*graphAs K h+
    2*K.k*(graphAs K h)^2+2*K.k*graphA K h*graphAss K h+
    graphAss K h*h.hss+2*graphAs K h*h.hsss+graphA K h*h.hssss+
    K.ksss*h.h*h.hs+4*K.kss*h.hs^2+2*K.kss*h.h*h.hss+
    11*K.ks*h.hs*h.hss+K.ks*h.h*h.hsss+4*K.k*h.hss^2+4*K.k*h.hs*h.hsss

private def graphSupportNumerator (K : NormalGraphBackgroundJet)
    (h : NormalGraphHeightJet) : ℝ :=
  graphA K h*(K.eta+h.h)-K.b*h.hs

/- With H=g^2 and r=1/g, the first four terms below are exactly
g^(-1) D_s(g^(-1) D_s(N*r^3)). The last two are kappa^3/2+c*eta_h. -/
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

private theorem quadratic_hasDerivAt (a d R : ℝ) :
    HasDerivAt (fun ε : ℝ => a+ε*d+ε^2*R) d 0 := by
  have hd := HasDerivAt.add
    (HasDerivAt.add (hasDerivAt_const (0:ℝ) a) ((hasDerivAt_id (0:ℝ)).mul_const d))
    (((hasDerivAt_id (0:ℝ)).pow 2).mul_const R)
  convert! hd using 1 <;> norm_num

@[simp] private theorem graphA_zero (K : NormalGraphBackgroundJet) (f : NormalGraphHeightJet) :
    graphA K (normalGraphScaleHeight 0 f) = 1 := by
  simp [graphA,normalGraphScaleHeight]

@[simp] private theorem graphMetricSquared_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphMetricSquared K (normalGraphScaleHeight 0 f) = 1 := by
  simp [graphMetricSquared,graphA,normalGraphScaleHeight]

@[simp] private theorem graphMetricSquaredS_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphMetricSquaredS K (normalGraphScaleHeight 0 f) = 0 := by
  simp [graphMetricSquaredS,graphA,graphAs,normalGraphScaleHeight]

@[simp] private theorem graphMetricSquaredSS_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphMetricSquaredSS K (normalGraphScaleHeight 0 f) = 0 := by
  simp [graphMetricSquaredSS,graphA,graphAs,graphAss,normalGraphScaleHeight]

@[simp] private theorem graphMetric_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphMetric K (normalGraphScaleHeight 0 f) = 1 := by
  simp [graphMetric]

@[simp] private theorem graphInverseMetric_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphInverseMetric K (normalGraphScaleHeight 0 f) = 1 := by
  simp [graphInverseMetric]

@[simp] private theorem graphCurvatureNumerator_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphCurvatureNumerator K (normalGraphScaleHeight 0 f) = K.k := by
  simp [graphCurvatureNumerator,graphA,normalGraphScaleHeight]

@[simp] private theorem graphCurvatureNumeratorS_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphCurvatureNumeratorS K (normalGraphScaleHeight 0 f) = K.ks := by
  simp [graphCurvatureNumeratorS,graphA,graphAs,normalGraphScaleHeight]

@[simp] private theorem graphCurvatureNumeratorSS_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphCurvatureNumeratorSS K (normalGraphScaleHeight 0 f) = K.kss := by
  simp [graphCurvatureNumeratorSS,graphA,graphAs,graphAss,normalGraphScaleHeight]

@[simp] private theorem graphSupportNumerator_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphSupportNumerator K (normalGraphScaleHeight 0 f) = K.eta := by
  simp [graphSupportNumerator,graphA,normalGraphScaleHeight]

@[simp] private theorem graphPrefactor_zero (K : NormalGraphBackgroundJet)
    (f : NormalGraphHeightJet) : graphPrefactor K (normalGraphScaleHeight 0 f) = 1 := by
  simp [graphPrefactor]

/- Each derivative below follows from an exact quadratic polynomial in epsilon,
including all nonlinear remainder terms. -/
theorem normal_graph_jet_flow_hasDerivAt (K : NormalGraphBackgroundJet) (c : ℝ)
    (f : NormalGraphHeightJet) :
    HasDerivAt (fun ε : ℝ => normalGraphJetFlow K c (normalGraphScaleHeight ε f))
      (-f.hssss-(5/2:ℝ)*K.k^2*f.hss-(5*K.k*K.ks-c*K.b)*f.hs-
        (3*K.ks^2+4*K.k*K.kss+(3/2:ℝ)*K.k^4+c)*f.h) 0 := by
  have hA : HasDerivAt (fun ε : ℝ => graphA K (normalGraphScaleHeight ε f))
      (-K.k*f.h) 0 := by
    convert! quadratic_hasDerivAt 1 (-K.k*f.h) 0 using 1
    funext ε
    dsimp only [graphA,normalGraphScaleHeight]
    ring
  have hH : HasDerivAt (fun ε : ℝ => graphMetricSquared K (normalGraphScaleHeight ε f))
      (-2*K.k*f.h) 0 := by
    convert! quadratic_hasDerivAt 1 (-2*K.k*f.h) (K.k^2*f.h^2+f.hs^2) using 1
    funext ε
    dsimp only [graphMetricSquared,graphA,normalGraphScaleHeight]
    ring
  have hH1 : HasDerivAt (fun ε : ℝ => graphMetricSquaredS K (normalGraphScaleHeight ε f))
      (-2*(K.ks*f.h+K.k*f.hs)) 0 := by
    convert! quadratic_hasDerivAt 0 (-2*(K.ks*f.h+K.k*f.hs))
      (2*K.k*f.h*(K.ks*f.h+K.k*f.hs)+2*f.hs*f.hss) using 1
    funext ε
    dsimp only [graphMetricSquaredS,graphA,graphAs,normalGraphScaleHeight]
    ring
  have hH2 : HasDerivAt (fun ε : ℝ => graphMetricSquaredSS K (normalGraphScaleHeight ε f))
      (-2*(K.kss*f.h+2*K.ks*f.hs+K.k*f.hss)) 0 := by
    convert! quadratic_hasDerivAt 0 (-2*(K.kss*f.h+2*K.ks*f.hs+K.k*f.hss))
      (2*(K.ks*f.h+K.k*f.hs)^2+
        2*K.k*f.h*(K.kss*f.h+2*K.ks*f.hs+K.k*f.hss)+2*f.hss^2+2*f.hs*f.hsss) using 1
    funext ε
    dsimp only [graphMetricSquaredSS,graphA,graphAs,graphAss,normalGraphScaleHeight]
    ring
  have hN : HasDerivAt (fun ε : ℝ => graphCurvatureNumerator K (normalGraphScaleHeight ε f))
      (f.hss-2*K.k^2*f.h) 0 := by
    convert! quadratic_hasDerivAt K.k (f.hss-2*K.k^2*f.h)
      (K.k^3*f.h^2-K.k*f.h*f.hss+K.ks*f.h*f.hs+2*K.k*f.hs^2) using 1
    funext ε
    dsimp only [graphCurvatureNumerator,graphA,normalGraphScaleHeight]
    ring
  have hN1 : HasDerivAt (fun ε : ℝ => graphCurvatureNumeratorS K (normalGraphScaleHeight ε f))
      (f.hsss-4*K.k*K.ks*f.h-2*K.k^2*f.hs) 0 := by
    convert! quadratic_hasDerivAt K.ks (f.hsss-4*K.k*K.ks*f.h-2*K.k^2*f.hs)
      (3*K.k^2*K.ks*f.h^2+2*K.k^3*f.h*f.hs-K.k*f.h*f.hsss+
        K.kss*f.h*f.hs+3*K.ks*f.hs^2+3*K.k*f.hs*f.hss) using 1
    funext ε
    dsimp only [graphCurvatureNumeratorS,graphA,graphAs,normalGraphScaleHeight]
    ring
  have hN2 : HasDerivAt (fun ε : ℝ => graphCurvatureNumeratorSS K (normalGraphScaleHeight ε f))
      (f.hssss-4*(K.ks^2+K.k*K.kss)*f.h-8*K.k*K.ks*f.hs-2*K.k^2*f.hss) 0 := by
    convert! quadratic_hasDerivAt K.kss
      (f.hssss-4*(K.ks^2+K.k*K.kss)*f.h-8*K.k*K.ks*f.hs-2*K.k^2*f.hss)
      ((6*K.k*K.ks^2+3*K.k^2*K.kss)*f.h^2+12*K.k^2*K.ks*f.h*f.hs+
        2*K.k^3*f.hs^2+2*K.k^3*f.h*f.hss-K.ks*f.h*f.hsss+
        2*K.k*f.hs*f.hsss-K.k*f.h*f.hssss+K.ksss*f.h*f.hs+
        4*K.kss*f.hs^2+K.kss*f.h*f.hss+9*K.ks*f.hs*f.hss+3*K.k*f.hss^2) using 1
    funext ε
    dsimp only [graphCurvatureNumeratorSS,graphA,graphAs,graphAss,normalGraphScaleHeight]
    ring
  have hP : HasDerivAt (fun ε : ℝ => graphSupportNumerator K (normalGraphScaleHeight ε f))
      (-K.k*f.h*K.eta+f.h-K.b*f.hs) 0 := by
    convert! quadratic_hasDerivAt K.eta (-K.k*f.h*K.eta+f.h-K.b*f.hs)
      (-K.k*f.h^2) using 1
    funext ε
    dsimp only [graphSupportNumerator,graphA,normalGraphScaleHeight]
    ring
  have hG : HasDerivAt (fun ε : ℝ => graphMetric K (normalGraphScaleHeight ε f))
      (-K.k*f.h) 0 := by
    convert! hH.sqrt (by simp) using 1 <;>
      simp only [graphMetric,graphMetricSquared_zero,Real.sqrt_one] <;> ring
  have hR : HasDerivAt (fun ε : ℝ => graphInverseMetric K (normalGraphScaleHeight ε f))
      (K.k*f.h) 0 := by
    convert! hG.inv (by simp) using 1 <;>
      simp only [graphInverseMetric,graphMetric_zero,one_pow,div_one,neg_neg] <;> ring
  have hPref : HasDerivAt (fun ε : ℝ => graphPrefactor K (normalGraphScaleHeight ε f)) 0 0 := by
    convert! hG.div hA (by simp) using 1 <;>
      simp only [graphPrefactor,graphMetric_zero,graphA_zero,mul_one,one_mul,
        sub_self,one_pow,zero_div]
  have hForce : HasDerivAt
      (fun ε : ℝ => normalGraphJetForce K c (normalGraphScaleHeight ε f))
      (f.hssss+(5/2:ℝ)*K.k^2*f.hss+(5*K.k*K.ks-c*K.b)*f.hs+
        (3*K.ks^2+4*K.k*K.kss+(3/2:ℝ)*K.k^4+c)*f.h) 0 := by
    have hd0 := HasDerivAt.mul hN2 (hR.pow 5)
    have hd1 := HasDerivAt.mul (HasDerivAt.mul (hN1.const_mul (7/2:ℝ)) hH1) (hR.pow 7)
    have hd2 := HasDerivAt.mul (HasDerivAt.mul (hN.const_mul (3/2:ℝ)) hH2) (hR.pow 7)
    have hd3 := HasDerivAt.mul (HasDerivAt.mul (hN.const_mul (9/2:ℝ)) (hH1.pow 2)) (hR.pow 9)
    have hd4 := HasDerivAt.mul ((hN.pow 3).const_mul (1/2:ℝ)) (hR.pow 9)
    have hd5 := HasDerivAt.mul (hP.const_mul c) hR
    have hd := HasDerivAt.add (HasDerivAt.add
      (HasDerivAt.add (HasDerivAt.sub (HasDerivAt.sub hd0 hd1) hd2) hd3) hd4) hd5
    convert! hd using 1 <;>
      simp only [normalGraphJetForce,Pi.mul_apply,Pi.pow_apply,graphCurvatureNumerator_zero,
        graphCurvatureNumeratorS_zero,graphCurvatureNumeratorSS_zero,
        graphMetricSquaredS_zero,graphMetricSquaredSS_zero,
        graphInverseMetric_zero,graphSupportNumerator_zero,
        one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_mul,add_zero,
        zero_add,mul_one,one_mul,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  convert! HasDerivAt.neg (HasDerivAt.mul hPref hForce) using 1 <;>
    simp only [normalGraphJetFlow,Pi.mul_apply,graphPrefactor_zero,zero_mul,one_mul,zero_add] <;> ring

/- Physical D_s=sqrt(2) D_x, k=3q, k_s=3sqrt(2)p, k_ss=-6q^3,
and b=sqrt(2)qp. These are precisely the coefficients of paperLinearExpression. -/
theorem bernoulli_normal_graph_linearization_scaling (q p f f₁ f₂ f₄ : ℝ)
    (he : 2*p^2+q^4=1) :
    -(4*f₄)-(5/2:ℝ)*(3*q)^2*(2*f₂)-
      (5*(3*q)*(3*Real.sqrt 2*p)-(15/2:ℝ)*(Real.sqrt 2*q*p))*(Real.sqrt 2*f₁)-
      (3*(3*Real.sqrt 2*p)^2+4*(3*q)*(-6*q^3)+(3/2:ℝ)*(3*q)^4+15/2)*f =
    -4*f₄-45*q^2*f₂-75*q*p*f₁-(69/2:ℝ)*f-(45/2:ℝ)*q^4*f := by
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  linear_combination -((75/2:ℝ)*q*p*f₁+27*p^2*f)*hs - (27*f)*he


/- The fourth derivative occurs affinely, with precisely the uniformly
parabolic coefficient -g^(-4). No term in the remainder contains h_ssss. -/
theorem normal_graph_jet_quasilinear (K : NormalGraphBackgroundJet) (c : ℝ)
    (h : NormalGraphHeightJet) (hA : 0 < 1-K.k*h.h) :
    normalGraphJetFlow K c h =
      -(((1-K.k*h.h)^2+h.hs^2)^2)⁻¹*h.hssss+
        normalGraphJetFlow K c {h with hssss := 0} := by
  let A := 1-K.k*h.h
  let H := A^2+h.hs^2
  let g := Real.sqrt H
  have hA0 : A ≠ 0 := hA.ne'
  have hH : 0 < H := by
    dsimp only [H]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hA) (sq_nonneg _)
  have hg0 : g ≠ 0 := (Real.sqrt_pos.2 hH).ne'
  have hg2 : g^2 = H := Real.sq_sqrt hH.le
  have hforce : normalGraphJetForce K c h = A*h.hssss*(g⁻¹)^5+
      normalGraphJetForce K c {h with hssss := 0} := by
    dsimp only [normalGraphJetForce,graphCurvatureNumeratorSS,
      graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredSS,
      graphMetricSquaredS,graphInverseMetric,graphMetric,graphMetricSquared,
      graphSupportNumerator,graphAss,graphAs,graphA,A,H,g]
    ring
  have hcoeff : g/A*(A*(g⁻¹)^5) = (H^2)⁻¹ := by
    rw [← hg2]
    field_simp [hA0,hg0]
    <;> ring
  change -(g/A*normalGraphJetForce K c h) =
    -(H^2)⁻¹*h.hssss-(g/A*normalGraphJetForce K c {h with hssss := 0})
  rw [hforce]
  linear_combination -h.hssss*hcoeff

/- Smoothness in all background and height coordinates on the regular graph
set. This is a finite-dimensional statement; Sobolev smoothness is separate. -/
theorem normal_graph_jet_contDiffAt (c : ℝ) (z : Fin 11 → ℝ)
    (hA : 0 < 1-z 0*z 6) :
    ContDiffAt ℝ (⊤ : WithTop ℕ∞)
      (fun w : Fin 11 → ℝ => normalGraphJetFlow
        ⟨w 0,w 1,w 2,w 3,w 4,w 5⟩ c ⟨w 6,w 7,w 8,w 9,w 10⟩) z := by
  have hA0 : 1-z 0*z 6 ≠ 0 := hA.ne'
  have hH : 0 < (1-z 0*z 6)^2+(z 7)^2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hA) (sq_nonneg _)
  have hH0 : (1-z 0*z 6)^2+(z 7)^2 ≠ 0 := hH.ne'
  have hg0 : Real.sqrt ((1-z 0*z 6)^2+(z 7)^2) ≠ 0 :=
    (Real.sqrt_pos.2 hH).ne'
  dsimp only [normalGraphJetFlow,normalGraphJetForce,graphPrefactor,
    graphCurvatureNumeratorSS,graphCurvatureNumeratorS,graphCurvatureNumerator,
    graphMetricSquaredSS,graphMetricSquaredS,graphInverseMetric,graphMetric,
    graphMetricSquared,graphSupportNumerator,graphAss,graphAs,graphA]
  fun_prop (disch := assumption)


/- Multiplying the geometric force by its normal-graph prefactor cancels
every square root. This rational expression is the form needed for the
Banach-algebra inverse estimates in the nonlinear equation. -/
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

end Lemniscate
