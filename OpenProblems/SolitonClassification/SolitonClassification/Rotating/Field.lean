import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Convert
import Lean.Util.CollectAxioms

/-! The actual rotating support ODE in coordinates (k,v/8,p,q,b,theta).
This module proves algebra and actual Fréchet derivatives. It asserts no
periodic orbit, shooting zero, or validity of an imported numeric report. -/
namespace SolitonClassification.Rotating
noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

abbrev State := Fin 6 → ℝ

def field (x : State) : State :=
  ![8*x 1,-(x 0)^3/16-x 2/8-x 4*x 3/8,-x 0*x 3,
    1+x 0*x 2,0,x 0]

def physicalField (x : State) : State :=
  ![x 1,-(x 0)^3/2-x 2-x 4*x 3,-x 0*x 3,1+x 0*x 2,0,x 0]

def unscale (x : State) : State := ![x 0,8*x 1,x 2,x 3,x 4,x 5]

theorem field_conjugacy (x : State) : unscale (field x)=physicalField (unscale x) := by
  ext i
  fin_cases i <;> simp [unscale,field,physicalField] <;> ring

def linear (a u : State) : State :=
  ![8*u 1,-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8-u 4*a 3/8,
    -a 0*u 3-u 0*a 3,a 0*u 2+u 0*a 2,0,u 0]

def bilinear (a u v : State) : State :=
  ![0,-3*a 0*u 0*v 0/16-u 4*v 3/8,-u 0*v 3,u 0*v 2,0,0]

def trilinear (u v w : State) : State := ![0,-u 0*v 0*w 0/16,0,0,0,0]

theorem field_expansion (a u : State) :
    field (a+u)=field a+linear a u+bilinear a u u+trilinear u u u := by
  ext i
  fin_cases i <;> simp [field,linear,bilinear,trilinear] <;> ring

theorem field_line_expansion (a u : State) (t : ℝ) :
    field (a+t • u)=field a+t • linear a u+t^2 • bilinear a u u+
      t^3 • trilinear u u u := by
  ext i
  fin_cases i <;> simp [field,linear,bilinear,trilinear,smul_eq_mul] <;> ring

theorem field_smooth : ContDiff ℝ ∞ field := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

theorem field_line_hasDerivAt (a u : State) :
    HasDerivAt (fun t : ℝ => field (a+t • u)) (linear a u) 0 := by
  have h := (((hasDerivAt_const (0:ℝ) (field a)).add
    ((hasDerivAt_id (0:ℝ)).smul_const (linear a u))).add
    (((hasDerivAt_id (0:ℝ)).pow 2).smul_const (bilinear a u u))).add
    (((hasDerivAt_id (0:ℝ)).pow 3).smul_const (trilinear u u u))
  convert! h using 1
  · funext t
    exact field_line_expansion a u t
  · simp

theorem field_fderiv_apply (a u : State) : fderiv ℝ field a u=linear a u := by
  have hg : HasDerivAt (fun t : ℝ => a+t • u) u 0 := by
    convert! (hasDerivAt_const (0:ℝ) a).add
      ((hasDerivAt_id (0:ℝ)).smul_const u) using 1 <;> simp
  have hf := (field_smooth.differentiable (by simp) a).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq 0 hg (by simp)
  exact hc.unique (field_line_hasDerivAt a u)

def outerTube : Set State := {x | |x 0|≤17/2 ∧ |x 1|≤9/2 ∧
  |x 2|≤17/2 ∧ |x 3|≤17/2 ∧ |x 4|≤1/50}

lemma coordinate_bound (u : State) (i : Fin 6) : |u i|≤‖u‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm u i

theorem field_bound {a : State} (ha : a∈outerTube) : ‖field a‖≤75 := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  fin_cases i
  · change |8*a 1|≤75
    rw [abs_mul]; norm_num; linarith
  · change |-(a 0)^3/16-a 2/8-a 4*a 3/8|≤75
    calc
      _ ≤ |-(a 0)^3/16-a 2/8|+|a 4*a 3/8| := abs_sub _ _
      _ ≤ (|-(a 0)^3/16|+|a 2/8|)+|a 4*a 3/8| := by gcongr; apply abs_sub
      _ = |a 0|^3/16+|a 2|/8+|a 4| * |a 3|/8 := by simp [abs_div,abs_mul,abs_pow]
      _ ≤ (17/2)^3/16+(17/2)/8+(1/50)*(17/2)/8 := by gcongr
      _ ≤ 75 := by norm_num
  · change |-a 0*a 3|≤75
    rw [abs_mul,abs_neg]
    calc
      |a 0| * |a 3| ≤ (17/2:ℝ)*(17/2) := by gcongr
      _ ≤ 75 := by norm_num
  · change |1+a 0*a 2|≤75
    calc
      _ ≤ |(1:ℝ)|+|a 0*a 2| := abs_add_le _ _
      _ = 1+|a 0| * |a 2| := by simp [abs_mul]
      _ ≤ 1+(17/2)*(17/2) := by gcongr
      _ ≤ 75 := by norm_num
  · simp [field]
  · change |a 0|≤75
    linarith

theorem bilinear_bound {a : State} (ha : a∈outerTube) (u v : State) :
    ‖bilinear a u v‖≤2*‖u‖*‖v‖ := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖≤_; simp; positivity }
  · change |-3*a 0*u 0*v 0/16-u 4*v 3/8|≤_
    calc
      _ ≤ |-3*a 0*u 0*v 0/16|+|u 4*v 3/8| := abs_sub _ _
      _ = 3*|a 0| * |u 0| * |v 0|/16+|u 4| * |v 3|/8 := by
        simp only [abs_div,abs_mul]; norm_num
      _ ≤ 3*(17/2)*‖u‖*‖v‖/16+‖u‖*‖v‖/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |-u 0*v 3|≤_
    rw [abs_mul,abs_neg]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]
  · change |u 0*v 2|≤_
    rw [abs_mul]
    calc
      _ ≤ ‖u‖*‖v‖ := by gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith [mul_nonneg (norm_nonneg u) (norm_nonneg v)]

theorem trilinear_bound (u v w : State) :
    ‖trilinear u v w‖≤(1/16)*‖u‖*‖v‖*‖w‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i <;> try { change ‖(0:ℝ)‖≤_; simp; positivity }
  change |-u 0*v 0*w 0/16|≤_
  rw [abs_div,abs_mul,abs_mul,abs_neg]
  norm_num
  calc
    _ ≤ ‖u‖*‖v‖*‖w‖/16 := by gcongr <;> apply coordinate_bound
    _ = _ := by ring

theorem linear_bound {a : State} (ha : a∈outerTube) (u : State) :
    ‖linear a u‖≤17*‖u‖ := by
  rcases ha with ⟨h0,h1,h2,h3,h4⟩
  have hn := norm_nonneg u
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · change |8*u 1|≤_
    rw [abs_mul]; norm_num
    linarith [coordinate_bound u 1]
  · change |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8-u 4*a 3/8|≤_
    calc
      _ ≤ |-3*(a 0)^2*u 0/16-u 2/8-a 4*u 3/8|+|u 4*a 3/8| := abs_sub _ _
      _ ≤ (|-3*(a 0)^2*u 0/16-u 2/8|+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ ≤ ((|-3*(a 0)^2*u 0/16|+|u 2/8|)+|a 4*u 3/8|)+|u 4*a 3/8| := by
        gcongr; apply abs_sub
      _ = 3*|a 0|^2*|u 0|/16+|u 2|/8+|a 4| * |u 3|/8+|u 4| * |a 3|/8 := by
        simp only [abs_div,abs_mul,abs_pow]; norm_num
      _ ≤ 3*(17/2)^2*‖u‖/16+‖u‖/8+(1/50)*‖u‖/8+‖u‖*(17/2)/8 := by
        gcongr <;> apply coordinate_bound
      _ ≤ _ := by nlinarith
  · change |-a 0*u 3-u 0*a 3|≤_
    calc
      _ ≤ |-a 0*u 3|+|u 0*a 3| := abs_sub _ _
      _ = |a 0| * |u 3|+|u 0| * |a 3| := by simp [abs_mul]
      _ ≤ (17/2)*‖u‖+‖u‖*(17/2) := by gcongr <;> apply coordinate_bound
      _ = _ := by ring
  · change |a 0*u 2+u 0*a 2|≤_
    calc
      _ ≤ |a 0*u 2|+|u 0*a 2| := abs_add_le _ _
      _ = |a 0| * |u 2|+|u 0| * |a 2| := by simp [abs_mul]
      _ ≤ (17/2)*‖u‖+‖u‖*(17/2) := by gcongr <;> apply coordinate_bound
      _ = _ := by ring
  · simp [linear]
  · change |u 0|≤_
    linarith [coordinate_bound u 0]

theorem field_fderiv_bound {a : State} (ha : a∈outerTube) :
    ‖fderiv ℝ field a‖≤17 := by
  apply (fderiv ℝ field a).opNorm_le_bound (by norm_num)
  intro u
  rw [field_fderiv_apply]
  exact linear_bound ha u

theorem field_majorant {a : State} (ha : a∈outerTube) (u : State) :
    ‖field (a+u)‖≤75*(1+‖u‖/10)^3 := by
  rw [field_expansion]
  have h1 := norm_add_le (field a) (linear a u)
  have h2 := norm_add_le (field a+linear a u) (bilinear a u u)
  have h3 := norm_add_le (field a+linear a u+bilinear a u u) (trilinear u u u)
  have hp : ‖field a+linear a u+bilinear a u u+trilinear u u u‖≤
      75+17*‖u‖+2*‖u‖^2+(1/16)*‖u‖^3 := by
    nlinarith [field_bound ha,linear_bound ha u,bilinear_bound ha u u,trilinear_bound u u u]
  have hn := norm_nonneg u
  have hs := sq_nonneg ‖u‖
  have hc := pow_nonneg hn 3
  nlinarith

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.field_fderiv_apply

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Rotating actual-field audit passed; standard axioms only."
