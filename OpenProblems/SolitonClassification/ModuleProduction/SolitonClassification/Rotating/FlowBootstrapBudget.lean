module

public import SolitonClassification.Rotating.FlowMetricDiscrete

@[expose] public section

/-! Affine state-error budgets with differential forcing and two reset
budgets. This recurrence is independent of the actual trajectory; its
strict upper bound will justify each first-threshold step. -/
namespace SolitonClassification.Rotating
noncomputable section
open Finset

def bootstrapNodeBudget (B C I : ℝ) (duration stateJump matrixJump : ℕ → ℝ) : ℕ → ℝ
  | 0 => B
  | n+1 => (1+I*matrixJump n)*(bootstrapNodeBudget B C I duration stateJump matrixJump n+
      C*duration n)+I*stateJump n

theorem bootstrap_affine_step {e A x y u v : ℝ}
    (hA : 0≤A) (hx : 0≤x) (hy : 0≤y) (hu : 0≤u) (hv : 0≤v)
    (he : e≤A*Real.exp u) :
    (1+v)*(e+x)+y≤(A+x+y)*Real.exp (u+v) := by
  have heu : 1≤Real.exp u := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hu
  have heuv : 1≤Real.exp (u+v) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (add_nonneg hu hv)
  have hex : 1+v≤Real.exp v := by simpa only [add_comm] using Real.add_one_le_exp v
  have hextra : e+x≤(A+x)*Real.exp u := by
    have h := mul_le_mul_of_nonneg_left heu hx
    nlinarith
  calc
    _ ≤ (1+v)*((A+x)*Real.exp u)+y := by
      have hh := mul_le_mul_of_nonneg_left hextra (show 0≤1+v by positivity)
      linarith
    _ ≤ Real.exp v*((A+x)*Real.exp u)+y := by
      have hh := mul_le_mul_of_nonneg_right hex (show 0 ≤ (A+x)*Real.exp u by positivity)
      linarith
    _ = (A+x)*Real.exp (u+v)+y := by rw [Real.exp_add]; ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left heuv hy
      nlinarith

theorem bootstrapNodeBudget_bound {duration stateJump matrixJump : ℕ → ℝ}
    {N : ℕ} {B C I : ℝ} (hB : 0≤B) (hC : 0≤C) (hI : 0≤I)
    (hd : ∀j<N,0≤duration j) (hx : ∀j<N,0≤stateJump j) (hm : ∀j<N,0≤matrixJump j) :
    ∀n≤N,bootstrapNodeBudget B C I duration stateJump matrixJump n≤
      (B+C*(∑j∈range n,duration j)+I*(∑j∈range n,stateJump j))*
        Real.exp (I*(∑j∈range n,matrixJump j)) := by
  intro n hn
  induction n with
  | zero => simp [bootstrapNodeBudget]
  | succ n ih =>
    have hn' : n<N := by omega
    have hdn := hd n hn'
    have hxn := hx n hn'
    have hmn := hm n hn'
    have hds : 0≤∑j∈range n,duration j := sum_nonneg fun j hj => hd j (by have := mem_range.mp hj; omega)
    have hxs : 0≤∑j∈range n,stateJump j := sum_nonneg fun j hj => hx j (by have := mem_range.mp hj; omega)
    have hms : 0≤∑j∈range n,matrixJump j := sum_nonneg fun j hj => hm j (by have := mem_range.mp hj; omega)
    have hh := bootstrap_affine_step (x:=C*duration n) (y:=I*stateJump n) (v:=I*matrixJump n)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (ih (by omega))
    change bootstrapNodeBudget B C I duration stateJump matrixJump (n+1)≤_ at hh
    convert! hh using 1
    simp only [sum_range_succ]
    congr 1 <;> ring

theorem bootstrapNodeBudget_inside_bound {duration stateJump matrixJump : ℕ → ℝ}
    {N n : ℕ} {B C I τ T SX SM : ℝ}
    (hB : 0≤B) (hC : 0≤C) (hI : 0≤I)
    (hd : ∀j<N,0≤duration j) (hx : ∀j<N,0≤stateJump j) (hm : ∀j<N,0≤matrixJump j)
    (hn : n≤N) (hτ : 0≤τ)
    (htime : (∑j∈range n,duration j)+τ≤T)
    (hSX : (∑j∈range n,stateJump j)≤SX) (hSM : (∑j∈range n,matrixJump j)≤SM) :
    bootstrapNodeBudget B C I duration stateJump matrixJump n+C*τ≤
      (B+C*T+I*SX)*Real.exp (I*SM) := by
  have hnode := bootstrapNodeBudget_bound hB hC hI hd hx hm n hn
  have hds : 0≤∑j∈range n,duration j := sum_nonneg fun j hj => hd j (by have := mem_range.mp hj; omega)
  have hxs : 0≤∑j∈range n,stateJump j := sum_nonneg fun j hj => hx j (by have := mem_range.mp hj; omega)
  have hms : 0≤∑j∈range n,matrixJump j := sum_nonneg fun j hj => hm j (by have := mem_range.mp hj; omega)
  have hex : 1≤Real.exp (I*(∑j∈range n,matrixJump j)) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hI hms)
  have hbase : B+C*((∑j∈range n,duration j)+τ)+I*(∑j∈range n,stateJump j)≤B+C*T+I*SX := by
    have h1 := mul_le_mul_of_nonneg_left htime hC
    have h2 := mul_le_mul_of_nonneg_left hSX hI
    linarith
  have hbasen : 0≤B+C*((∑j∈range n,duration j)+τ)+I*(∑j∈range n,stateJump j) := by positivity
  calc
    _ ≤ (B+C*((∑j∈range n,duration j)+τ)+I*(∑j∈range n,stateJump j))*
        Real.exp (I*(∑j∈range n,matrixJump j)) := by
      have he := mul_le_mul_of_nonneg_left hex (mul_nonneg hC hτ)
      nlinarith
    _ ≤ _ := mul_le_mul hbase
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hSM hI)) (Real.exp_pos _).le (hbasen.trans hbase)

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating affine state-budget audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating affine state-budget audit passed for {count} declarations."

end
