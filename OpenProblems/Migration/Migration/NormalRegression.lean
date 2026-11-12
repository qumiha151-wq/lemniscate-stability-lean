import Migration.NormalGram

/-! The normal-distance regression center of an actual closed unit-speed
curve. Its defining matrix is proved invertible in NormalGram; balance
and unique minimization are derived from the actual coordinate integrals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped ContDiff
namespace MigrationGeometry

def normalSupport (x y : ℝ → ℝ) (d : Fin 2 → ℝ) (s : ℝ) : ℝ :=
  -(x s-d 0)*deriv y s+(y s-d 1)*deriv x s

def normalBalance (x y : ℝ → ℝ) (L : ℝ) (d : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![∫ s in 0..L, normalSupport x y d s*(-deriv y s),
    ∫ s in 0..L, normalSupport x y d s*deriv x s]

def regressionCenter (x y : ℝ → ℝ) (L : ℝ) : Fin 2 → ℝ :=
  (normalGram x y L)⁻¹ *ᵥ normalBalance x y L 0

def normalDistanceSquared (x y : ℝ → ℝ) (L : ℝ) (d : Fin 2 → ℝ) : ℝ :=
  ∫ s in 0..L, (normalSupport x y d s)^2

theorem normalSupport_continuous {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (d : Fin 2 → ℝ) :
    Continuous (normalSupport x y d) :=
  ((hx.continuous.sub continuous_const).neg.mul
    (contDiff_infty_iff_deriv.mp hy).2.continuous).add
    ((hy.continuous.sub continuous_const).mul
      (contDiff_infty_iff_deriv.mp hx).2.continuous)

private theorem integral_sub_two_const_mul {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (a b L : ℝ) :
    (∫ s in 0..L, f s-a*g s-b*h s) =
      (∫ s in 0..L, f s)-a*(∫ s in 0..L, g s)-b*(∫ s in 0..L, h s) := by
  rw [intervalIntegral.integral_sub
    (f := fun s => f s-a*g s) (g := fun s => b*h s)
    ((hf.sub (hg.const_mul a)).intervalIntegrable 0 L)
    ((hh.const_mul b).intervalIntegrable 0 L),
    intervalIntegral.integral_sub
    (f := f) (g := fun s => a*g s)
    (hf.intervalIntegrable 0 L) ((hg.const_mul a).intervalIntegrable 0 L),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

theorem normalBalance_eq {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (L : ℝ) (d : Fin 2 → ℝ) :
    normalBalance x y L d = normalBalance x y L 0-normalGram x y L *ᵥ d := by
  have cx := (contDiff_infty_iff_deriv.mp hx).2.continuous
  have cy := (contDiff_infty_iff_deriv.mp hy).2.continuous
  have cp := normalSupport_continuous hx hy (0 : Fin 2 → ℝ)
  funext i
  fin_cases i
  · simp only [normalBalance, normalGram, Pi.sub_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply]
    change (∫ s in 0..L, normalSupport x y d s*(-deriv y s)) =
      (∫ s in 0..L, normalSupport x y 0 s*(-deriv y s))-
        ((∫ s in 0..L, (deriv y s)^2)*d 0+
          (∫ s in 0..L, -(deriv x s*deriv y s))*d 1)
    calc
      _ = ∫ s in 0..L, normalSupport x y 0 s*(-deriv y s)-
          d 0*(deriv y s)^2-d 1*(-(deriv x s*deriv y s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [normalSupport]
        ring
      _ = _ := by
        rw [integral_sub_two_const_mul
          (f := fun s => normalSupport x y 0 s*(-deriv y s))
          (g := fun s => (deriv y s)^2)
          (h := fun s => -(deriv x s*deriv y s))
          (cp.mul cy.neg) (cy.pow 2) (cx.mul cy).neg (d 0) (d 1) L]
        ring
  · simp only [normalBalance, normalGram, Pi.sub_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply]
    change (∫ s in 0..L, normalSupport x y d s*deriv x s) =
      (∫ s in 0..L, normalSupport x y 0 s*deriv x s)-
        ((∫ s in 0..L, -(deriv x s*deriv y s))*d 0+
          (∫ s in 0..L, (deriv x s)^2)*d 1)
    calc
      _ = ∫ s in 0..L, normalSupport x y 0 s*deriv x s-
          d 0*(-(deriv x s*deriv y s))-d 1*(deriv x s)^2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [normalSupport]
        ring
      _ = _ := by
        rw [integral_sub_two_const_mul
          (f := fun s => normalSupport x y 0 s*deriv x s)
          (g := fun s => -(deriv x s*deriv y s))
          (h := fun s => (deriv x s)^2)
          (cp.mul cx) (cx.mul cy).neg (cx.pow 2) (d 0) (d 1) L]
        ring

/-- Balance is proved for the center defined by the actual Gram inverse;
the integral equations are conclusions, not input data. -/
theorem regressionCenter_balance {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1) :
    normalBalance x y L (regressionCenter x y L)=0 := by
  have hA := normalGram_isUnit hx hy hL hclosedx hclosedy hunit
  rw [normalBalance_eq hx hy,regressionCenter,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
    Matrix.one_mulVec,sub_self]

theorem normalSupport_projection_integral {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (L : ℝ) (d v : Fin 2 → ℝ) :
    (∫ s in 0..L, normalSupport x y d s*normalProjection x y (v 0) (v 1) s) =
      v 0*normalBalance x y L d 0+v 1*normalBalance x y L d 1 := by
  have cx := (contDiff_infty_iff_deriv.mp hx).2.continuous
  have cy := (contDiff_infty_iff_deriv.mp hy).2.continuous
  have cp := normalSupport_continuous hx hy d
  calc
    _ = ∫ s in 0..L, v 0*(normalSupport x y d s*(-deriv y s))+
        v 1*(normalSupport x y d s*deriv x s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [normalProjection]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (f := fun s => v 0*(normalSupport x y d s*(-deriv y s)))
        (g := fun s => v 1*(normalSupport x y d s*deriv x s))
        (((cp.mul cy.neg).const_mul (v 0)).intervalIntegrable 0 L)
        (((cp.mul cx).const_mul (v 1)).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
      rfl

/-- The exact least-squares gap is the positive-definite actual Gram form. -/
theorem regressionCenter_distance_identity {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (z : Fin 2 → ℝ) :
    normalDistanceSquared x y L z =
      normalDistanceSquared x y L (regressionCenter x y L)+
      star (z-regressionCenter x y L) ⬝ᵥ
        (normalGram x y L *ᵥ (z-regressionCenter x y L)) := by
  let d := regressionCenter x y L
  let v := z-d
  have hb : normalBalance x y L d=0 :=
    regressionCenter_balance hx hy hL hclosedx hclosedy hunit
  have hp := normalSupport_continuous hx hy d
  have hv := normalProjection_continuous hx hy (v 0) (v 1)
  have hcross : (∫ s in 0..L, normalSupport x y d s*
      normalProjection x y (v 0) (v 1) s)=0 := by
    rw [normalSupport_projection_integral hx hy, hb]
    simp
  rw [normalGram_quadratic hx hy]
  change (∫ s in 0..L, (normalSupport x y z s)^2) =
    (∫ s in 0..L, (normalSupport x y d s)^2)+
      ∫ s in 0..L, (normalProjection x y (v 0) (v 1) s)^2
  calc
    _ = ∫ s in 0..L, ((normalSupport x y d s)^2-
        2*(normalSupport x y d s*normalProjection x y (v 0) (v 1) s))+
        (normalProjection x y (v 0) (v 1) s)^2 := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [normalSupport,normalProjection,v]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add
        (f := fun s => (normalSupport x y d s)^2-
          2*(normalSupport x y d s*normalProjection x y (v 0) (v 1) s))
        (g := fun s => (normalProjection x y (v 0) (v 1) s)^2)
        (((hp.pow 2).sub ((hp.mul hv).const_mul 2)).intervalIntegrable 0 L)
        ((hv.pow 2).intervalIntegrable 0 L),
        intervalIntegral.integral_sub
        (f := fun s => (normalSupport x y d s)^2)
        (g := fun s => 2*(normalSupport x y d s*normalProjection x y (v 0) (v 1) s))
        ((hp.pow 2).intervalIntegrable 0 L)
        (((hp.mul hv).const_mul 2).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul,hcross,mul_zero,sub_zero]

/-- The inverse-defined center is the unique minimizer of the actual
integrated squared normal distance among all points of the plane. -/
theorem regressionCenter_unique_minimizer {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (z : Fin 2 → ℝ) :
    normalDistanceSquared x y L (regressionCenter x y L) ≤ normalDistanceSquared x y L z ∧
    (normalDistanceSquared x y L z=normalDistanceSquared x y L (regressionCenter x y L)
      ↔ z=regressionCenter x y L) := by
  by_cases hz : z=regressionCenter x y L
  · simp [hz]
  have hpos := (normalGram_posDef hx hy hL hclosedx hclosedy hunit).dotProduct_mulVec_pos
    (sub_ne_zero.mpr hz)
  have hid := regressionCenter_distance_identity hx hy hL hclosedx hclosedy hunit z
  constructor
  · linarith
  constructor
  · intro he
    linarith
  · intro he
    exact (hz he).elim

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Normal regression audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Normal regression audit passed for {count} declarations; standard axioms only."
