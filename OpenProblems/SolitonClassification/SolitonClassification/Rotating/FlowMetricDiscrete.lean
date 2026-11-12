import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Finite accumulation of actual segment-growth and matrix-reset bounds.
The exponent contains only the small moving-coordinate coefficient and
the sum of reset defects, never the raw field bound times total time. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset

def metricGridBudget (rate I : ℝ) (duration jump : ℕ → ℝ) (n : ℕ) : ℝ :=
  rate*(∑j∈range n,duration j)+I*(∑j∈range n,jump j)

theorem metric_grid_growth {e duration jump : ℕ → ℝ} {N : ℕ} {B rate I : ℝ}
    (hB : 0≤B) (hI : 0≤I) (hj : ∀j<N,0≤jump j)
    (hzero : e 0≤B)
    (hstep : ∀j<N,e (j+1)≤(1+I*jump j)*e j*Real.exp (rate*duration j)) :
    ∀n≤N,e n≤B*Real.exp (metricGridBudget rate I duration jump n) := by
  intro n hn
  induction n with
  | zero => simpa [metricGridBudget] using hzero
  | succ n ih =>
    have hn' : n<N := by omega
    have hprev := ih (by omega)
    have hjn := hj n hn'
    have hm : 0≤1+I*jump n := by positivity
    have hex : 1+I*jump n≤Real.exp (I*jump n) := by
      simpa only [add_comm] using Real.add_one_le_exp (I*jump n)
    have heq : Real.exp (I*jump n)*Real.exp (metricGridBudget rate I duration jump n)*
        Real.exp (rate*duration n)=Real.exp (metricGridBudget rate I duration jump (n+1)) := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1
      simp only [metricGridBudget,sum_range_succ]
      ring
    calc
      e (n+1) ≤ (1+I*jump n)*e n*Real.exp (rate*duration n) := hstep n hn'
      _ ≤ (1+I*jump n)*(B*Real.exp (metricGridBudget rate I duration jump n))*
          Real.exp (rate*duration n) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hprev hm) (Real.exp_pos _).le
      _ ≤ Real.exp (I*jump n)*(B*Real.exp (metricGridBudget rate I duration jump n))*
          Real.exp (rate*duration n) := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hex (by positivity)) (Real.exp_pos _).le
      _ = B*(Real.exp (I*jump n)*Real.exp (metricGridBudget rate I duration jump n)*
          Real.exp (rate*duration n)) := by ring
      _ = _ := by rw [heq]

theorem metric_grid_inside_growth {e duration jump : ℕ → ℝ} {N n : ℕ}
    {B rate I z τ T J : ℝ}
    (hB : 0≤B) (hrate : 0≤rate) (hI : 0≤I) (hj : ∀j<N,0≤jump j)
    (hzero : e 0≤B)
    (hstep : ∀j<N,e (j+1)≤(1+I*jump j)*e j*Real.exp (rate*duration j))
    (hn : n≤N) (hz : z≤e n*Real.exp (rate*τ))
    (htime : (∑j∈range n,duration j)+τ≤T) (hjump : (∑j∈range n,jump j)≤J) :
    z≤B*Real.exp (rate*T+I*J) := by
  have hnode := metric_grid_growth hB hI hj hzero hstep n hn
  have hb : metricGridBudget rate I duration jump n+rate*τ≤rate*T+I*J := by
    have h1:=mul_le_mul_of_nonneg_left htime hrate
    have h2:=mul_le_mul_of_nonneg_left hjump hI
    dsimp [metricGridBudget]
    nlinarith
  calc
    z ≤ (B*Real.exp (metricGridBudget rate I duration jump n))*Real.exp (rate*τ) :=
      hz.trans (mul_le_mul_of_nonneg_right hnode (Real.exp_pos _).le)
    _ = B*Real.exp (metricGridBudget rate I duration jump n+rate*τ) := by
      rw [Real.exp_add,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hb) hB

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating discrete moving-matrix audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating discrete moving-matrix audit passed for {count} declarations."
