import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Lean.Util.CollectAxioms

/-! The normal Gram form of an actual closed unit-speed planar immersion
is positive definite. The normal is computed from the actual coordinate
derivatives; no integral balance or positive-definiteness assumption occurs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped ContDiff
namespace MigrationGeometry

def normalProjection (x y : ℝ → ℝ) (ex ey s : ℝ) : ℝ :=
  -ex * deriv y s + ey * deriv x s

theorem normalProjection_continuous {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y) (ex ey : ℝ) :
    Continuous (normalProjection x y ex ey) :=
  (((contDiff_infty_iff_deriv.mp hy).2.continuous).const_mul (-ex)).add
    (((contDiff_infty_iff_deriv.mp hx).2.continuous).const_mul ey)

/-- Rolle's theorem forces the actual normal to have a nonzero component
in every nonzero fixed direction at some point of each closed period. -/
theorem exists_normalProjection_ne_zero {x y : ℝ → ℝ} {L ex ey : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (he : ex ≠ 0 ∨ ey ≠ 0) :
    ∃ s ∈ Ioo 0 L, normalProjection x y ex ey s ≠ 0 := by
  have hcont := (hx.continuous.const_mul ex).add (hy.continuous.const_mul ey)
  have hends : ex*x 0+ey*y 0=ex*x L+ey*y L := by rw [hclosedx,hclosedy]
  obtain ⟨s,hs,hzero⟩ := exists_hasDerivAt_eq_zero hL hcont.continuousOn hends
    (f' := fun s => ex*deriv x s+ey*deriv y s)
    (fun s _ => ((hx.differentiable (by simp) s).hasDerivAt.const_mul ex).add
      ((hy.differentiable (by simp) s).hasDerivAt.const_mul ey))
  refine ⟨s,hs,?_⟩
  intro hn
  have hu := hunit s ⟨hs.1.le,hs.2.le⟩
  have hid : (normalProjection x y ex ey s)^2+
      (ex*deriv x s+ey*deriv y s)^2 = ex^2+ey^2 := by
    dsimp [normalProjection]
    linear_combination (ex^2+ey^2)*hu
  rw [hn,hzero] at hid
  rcases he with he | he
  · nlinarith [sq_pos_of_ne_zero he,sq_nonneg ey]
  · nlinarith [sq_pos_of_ne_zero he,sq_nonneg ex]

/-- Strict positivity of the integral of the squared actual normal
projection, derived from closure and unit speed. -/
theorem normalProjection_square_integral_pos {x y : ℝ → ℝ} {L ex ey : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1)
    (he : ex ≠ 0 ∨ ey ≠ 0) :
    0 < ∫ s in 0..L, (normalProjection x y ex ey s)^2 := by
  obtain ⟨s,hs,hn⟩ := exists_normalProjection_ne_zero hx hy hL hclosedx hclosedy hunit he
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0:ℝ)) (g := fun s => (normalProjection x y ex ey s)^2)
    hL continuous_const.continuousOn
    ((normalProjection_continuous hx hy ex ey).pow 2).continuousOn
    (fun s _ => sq_nonneg _) ⟨s,⟨hs.1.le,hs.2.le⟩,sq_pos_of_ne_zero hn⟩
  simpa only [intervalIntegral.integral_zero] using h

def normalGram (x y : ℝ → ℝ) (L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![∫ s in 0..L, (deriv y s)^2,
      ∫ s in 0..L, -(deriv x s*deriv y s);
      ∫ s in 0..L, -(deriv x s*deriv y s),
      ∫ s in 0..L, (deriv x s)^2]

theorem normalGram_isHermitian (x y : ℝ → ℝ) (L : ℝ) :
    (normalGram x y L).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  fin_cases i <;> fin_cases j <;> simp [normalGram]

theorem normalGram_quadratic {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (L : ℝ) (v : Fin 2 → ℝ) :
    star v ⬝ᵥ (normalGram x y L *ᵥ v) =
      ∫ s in 0..L, (normalProjection x y (v 0) (v 1) s)^2 := by
  have cx := (contDiff_infty_iff_deriv.mp hx).2.continuous
  have cy := (contDiff_infty_iff_deriv.mp hy).2.continuous
  have hi : (∫ s in 0..L, (normalProjection x y (v 0) (v 1) s)^2) =
      (v 0)^2*(∫ s in 0..L, (deriv y s)^2) +
      (2*v 0*v 1)*(∫ s in 0..L, -(deriv x s*deriv y s)) +
      (v 1)^2*(∫ s in 0..L, (deriv x s)^2) := by
    calc
      _ = ∫ s in 0..L, ((v 0)^2*(deriv y s)^2+
          (2*v 0*v 1)*(-(deriv x s*deriv y s)))+(v 1)^2*(deriv x s)^2 := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [normalProjection]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          (f := fun s => (v 0)^2*(deriv y s)^2+
            (2*v 0*v 1)*(-(deriv x s*deriv y s)))
          (g := fun s => (v 1)^2*(deriv x s)^2)
          ((((cy.pow 2).const_mul ((v 0)^2)).add
            ((cx.mul cy).neg.const_mul (2*v 0*v 1))).intervalIntegrable 0 L)
          (((cx.pow 2).const_mul ((v 1)^2)).intervalIntegrable 0 L),
          intervalIntegral.integral_add
          (f := fun s => (v 0)^2*(deriv y s)^2)
          (g := fun s => (2*v 0*v 1)*(-(deriv x s*deriv y s)))
          (((cy.pow 2).const_mul ((v 0)^2)).intervalIntegrable 0 L)
          (((cx.mul cy).neg.const_mul (2*v 0*v 1)).intervalIntegrable 0 L),
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hi]
  simp only [normalGram, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Pi.star_apply, star_trivial, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The actual normal Gram matrix is positive definite, derived solely
from smooth coordinates, closed endpoints, positive length and unit speed. -/
theorem normalGram_posDef {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1) :
    (normalGram x y L).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (normalGram_isHermitian x y L)
  intro v hv
  rw [normalGram_quadratic hx hy]
  apply normalProjection_square_integral_pos hx hy hL hclosedx hclosedy hunit
  by_contra h
  push Not at h
  apply hv
  funext i
  fin_cases i <;> simp [h.1,h.2]

/-- Thus the regression center defined using the inverse of this actual
Gram matrix has no singular-matrix ambiguity for a closed immersion. -/
theorem normalGram_isUnit {x y : ℝ → ℝ} {L : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hL : 0 < L) (hclosedx : x L = x 0) (hclosedy : y L = y 0)
    (hunit : ∀ s ∈ Icc 0 L, (deriv x s)^2+(deriv y s)^2=1) :
    IsUnit (normalGram x y L) :=
  (normalGram_posDef hx hy hL hclosedx hclosedy hunit).isUnit

end MigrationGeometry

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`MigrationGeometry).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Normal Gram audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Normal Gram audit passed for {count} declarations; standard axioms only."
