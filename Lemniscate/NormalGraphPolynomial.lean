import Lemniscate.Algebra
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! Polynomial jet data and the algebraic rational normal-graph flow.

The background and height records, their polynomial expressions and the
principal fourth-derivative identity are shared by real and complex proofs.
This foundation uses no square roots, derivatives, or periodic function spaces.
-/
noncomputable section
namespace Lemniscate

structure BackgroundJetOver (R : Type*) where
  k : R
  ks : R
  kss : R
  ksss : R
  eta : R
  b : R

structure HeightJetOver (R : Type*) where
  h : R
  hs : R
  hss : R
  hsss : R
  hssss : R

abbrev NormalGraphBackgroundJet := BackgroundJetOver ℝ

abbrev NormalGraphHeightJet := HeightJetOver ℝ

def normalGraphScaleHeight {R : Type*} [Mul R]
    (ε : R) (F : HeightJetOver R) : HeightJetOver R :=
  ⟨ε*F.h,ε*F.hs,ε*F.hss,ε*F.hsss,ε*F.hssss⟩

def graphA {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  1-K.k*h.h

def graphAs {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  -K.ks*h.h-K.k*h.hs

def graphAss {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  -K.kss*h.h-2*K.ks*h.hs-K.k*h.hss

def graphMetricSquared {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  (graphA K h)^2+h.hs^2

def graphMetricSquaredS {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  2*graphA K h*graphAs K h+2*h.hs*h.hss

def graphMetricSquaredSS {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  2*(graphAs K h)^2+2*graphA K h*graphAss K h+2*h.hss^2+2*h.hs*h.hsss

/- The numerator is det(Z_s,Z_ss). Its next two definitions are the exact
spatial derivatives obtained from the Frenet rules and the supplied jets. -/
def graphCurvatureNumerator {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  K.k*(graphA K h)^2+graphA K h*h.hss+K.ks*h.h*h.hs+2*K.k*h.hs^2

def graphCurvatureNumeratorS {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  K.ks*(graphA K h)^2+2*K.k*graphA K h*graphAs K h+
    graphAs K h*h.hss+graphA K h*h.hsss+K.kss*h.h*h.hs+
    3*K.ks*h.hs^2+K.ks*h.h*h.hss+4*K.k*h.hs*h.hss

def graphCurvatureNumeratorSS {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  K.kss*(graphA K h)^2+4*K.ks*graphA K h*graphAs K h+
    2*K.k*(graphAs K h)^2+2*K.k*graphA K h*graphAss K h+
    graphAss K h*h.hss+2*graphAs K h*h.hsss+graphA K h*h.hssss+
    K.ksss*h.h*h.hs+4*K.kss*h.hs^2+2*K.kss*h.h*h.hss+
    11*K.ks*h.hs*h.hss+K.ks*h.h*h.hsss+4*K.k*h.hss^2+4*K.k*h.hs*h.hsss

def graphSupportNumerator {R : Type*} [CommRing R] (K : BackgroundJetOver R)
    (h : HeightJetOver R) : R :=
  graphA K h*(K.eta+h.h)-K.b*h.hs

def normalGraphRationalFlow {R : Type*} [CommRing R] [Algebra ℝ R]
    (K : BackgroundJetOver R) (c : ℝ) (h : HeightJetOver R) : R :=
  let A := graphA K h
  let H := graphMetricSquared K h
  let H₁ := graphMetricSquaredS K h
  let H₂ := graphMetricSquaredSS K h
  let N := graphCurvatureNumerator K h
  let N₁ := graphCurvatureNumeratorS K h
  let N₂ := graphCurvatureNumeratorSS K h
  let P := graphSupportNumerator K h
  let iH := Ring.inverse H;
  -(Ring.inverse A)*
    (N₂*iH^2-(7/2:ℝ) • (N₁*H₁*iH^3)-(3/2:ℝ) • (N*H₂*iH^3)+
      (9/2:ℝ) • (N*H₁^2*iH^4)+(1/2:ℝ) • (N^3*iH^4)+c • P)

/-- Only A must be a unit for the algebraic principal-part identity.
No invertibility hypothesis on the squared metric is needed for this identity. -/
theorem normal_graph_rational_flow_quasilinear
    {R : Type*} [CommRing R] [Algebra ℝ R]
    (K : BackgroundJetOver R) (c : ℝ) (h : HeightJetOver R)
    (hA : IsUnit (graphA K h)) :
    normalGraphRationalFlow K c h =
      -(Ring.inverse (graphMetricSquared K h))^2*h.hssss+
        normalGraphRationalFlow K c {h with hssss := 0} := by
  let h₀ : HeightJetOver R := {h with hssss := 0}
  have hA₀ : graphA K h₀ = graphA K h := rfl
  have hH₀ : graphMetricSquared K h₀ = graphMetricSquared K h := rfl
  have hH₁₀ : graphMetricSquaredS K h₀ = graphMetricSquaredS K h := rfl
  have hH₂₀ : graphMetricSquaredSS K h₀ = graphMetricSquaredSS K h := rfl
  have hN₀ : graphCurvatureNumerator K h₀ = graphCurvatureNumerator K h := rfl
  have hN₁₀ : graphCurvatureNumeratorS K h₀ = graphCurvatureNumeratorS K h := rfl
  have hP₀ : graphSupportNumerator K h₀ = graphSupportNumerator K h := rfl
  have hN₂ : graphCurvatureNumeratorSS K h =
      graphA K h*h.hssss+graphCurvatureNumeratorSS K h₀ := by
    dsimp only [graphCurvatureNumeratorSS,graphAss,graphAs,graphA,h₀]
    ring
  have hflow : normalGraphRationalFlow K c h =
      -(Ring.inverse (graphA K h))*
        (graphA K h*h.hssss*(Ring.inverse (graphMetricSquared K h))^2)+
          normalGraphRationalFlow K c h₀ := by
    dsimp only [normalGraphRationalFlow]
    rw [hN₂]
    simp only [hA₀,hH₀,hH₁₀,hH₂₀,hN₀,hN₁₀,hP₀,Algebra.smul_def]
    ring
  rw [hflow]
  have hcancel := Ring.inverse_mul_cancel (graphA K h) hA
  rw [show -(Ring.inverse (graphA K h))*
      (graphA K h*h.hssss*(Ring.inverse (graphMetricSquared K h))^2) =
    -(Ring.inverse (graphA K h)*graphA K h)*
      ((Ring.inverse (graphMetricSquared K h))^2*h.hssss) by ring,hcancel]
  ring

end Lemniscate
