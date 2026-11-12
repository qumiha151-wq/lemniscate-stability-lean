import SolitonClassification.Rotating.BoundedODE
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-! Actual global scalar flows for smooth periodic fields. The field bounds,
Lipschitz estimate, existence, uniqueness and group laws are conclusions.
No other open-problem project is imported. -/
namespace SolitonClassification.Rotating.NormalEvolution
noncomputable section
open Set Real
open scoped ContDiff NNReal
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

structure PeriodicScalarField where
  period : ℝ
  period_pos : 0 < period
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  periodic : Function.Periodic toFun period

instance : CoeFun PeriodicScalarField (fun _ => ℝ → ℝ) := ⟨PeriodicScalarField.toFun⟩

theorem periodic_deriv {f : ℝ → ℝ} {L : ℝ} (hp : Function.Periodic f L) :
    Function.Periodic (deriv f) L := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hp

theorem scalarField_bounds (g : PeriodicScalarField) :
    ∃ K M : ℝ≥0, LipschitzWith K g ∧ ∀ x, ‖g x‖ ≤ M := by
  obtain ⟨C,hC⟩ := (g.periodic.isBounded_of_continuous g.period_pos.ne' g.smooth.continuous).exists_norm_le
  have hC0 : 0 ≤ C := (norm_nonneg (g 0)).trans (hC _ (mem_range_self 0))
  have hd : ContDiff ℝ ∞ (deriv g) := g.smooth.deriv'
  obtain ⟨D,hD⟩ := ((periodic_deriv g.periodic).isBounded_of_continuous
    g.period_pos.ne' hd.continuous).exists_norm_le
  have hD0 : 0 ≤ D := (norm_nonneg (deriv g 0)).trans (hD _ (mem_range_self 0))
  refine ⟨⟨D,hD0⟩,⟨C,hC0⟩,?_,fun x => hC _ (mem_range_self x)⟩
  apply lipschitzWith_of_nnnorm_deriv_le (g.smooth.differentiable (by simp))
  intro x
  rw [← NNReal.coe_le_coe,coe_nnnorm]
  exact hD _ (mem_range_self x)

def scalarLip (g : PeriodicScalarField) : ℝ≥0 := (scalarField_bounds g).choose
def scalarBound (g : PeriodicScalarField) : ℝ≥0 := (scalarField_bounds g).choose_spec.choose

theorem scalarField_lipschitz (g : PeriodicScalarField) : LipschitzWith (scalarLip g) g :=
  (scalarField_bounds g).choose_spec.choose_spec.1

theorem scalarField_norm_bound (g : PeriodicScalarField) (x : ℝ) : ‖g x‖ ≤ scalarBound g :=
  (scalarField_bounds g).choose_spec.choose_spec.2 x

def scalarFlow (g : PeriodicScalarField) (t a : ℝ) : ℝ :=
  (exists_unique_global_bounded_flow (scalarField_lipschitz g) (scalarField_norm_bound g) a).exists.choose t

theorem scalarFlow_zero (g : PeriodicScalarField) (a : ℝ) : scalarFlow g 0 a=a :=
  (exists_unique_global_bounded_flow (scalarField_lipschitz g) (scalarField_norm_bound g) a).exists.choose_spec.1

theorem scalarFlow_hasDerivAt (g : PeriodicScalarField) (a t : ℝ) :
    HasDerivAt (fun u => scalarFlow g u a) (g (scalarFlow g t a)) t :=
  (exists_unique_global_bounded_flow (scalarField_lipschitz g) (scalarField_norm_bound g) a).exists.choose_spec.2 t

theorem scalarFlow_unique (g : PeriodicScalarField) {a : ℝ} {x : ℝ → ℝ}
    (h0 : x 0=a) (hx : ∀ t, HasDerivAt x (g (x t)) t) :
    x=fun t => scalarFlow g t a :=
  (exists_unique_global_bounded_flow (scalarField_lipschitz g) (scalarField_norm_bound g) a).unique
    ⟨h0,hx⟩ ⟨scalarFlow_zero g a,scalarFlow_hasDerivAt g a⟩

theorem scalarFlow_add (g : PeriodicScalarField) (t s a : ℝ) :
    scalarFlow g (t+s) a=scalarFlow g t (scalarFlow g s a) := by
  have he := scalarFlow_unique g (a:=scalarFlow g s a) (x:=fun u => scalarFlow g (u+s) a)
    (by simp only [zero_add]) (fun u => by
      convert! (scalarFlow_hasDerivAt g a (u+s)).scomp u ((hasDerivAt_id u).add_const s) using 1
      simp only [one_smul])
  exact congrFun he t

theorem scalarFlow_period_add (g : PeriodicScalarField) (t a : ℝ) :
    scalarFlow g t (a+g.period)=scalarFlow g t a+g.period := by
  have he := scalarFlow_unique g (a:=a+g.period) (x:=fun u => scalarFlow g u a+g.period)
    (by rw [scalarFlow_zero]) (fun u => by
      rw [g.periodic]
      exact (scalarFlow_hasDerivAt g a u).add_const g.period)
  exact (congrFun he t).symm

theorem scalarFlow_inverse (g : PeriodicScalarField) (t a : ℝ) :
    scalarFlow g (-t) (scalarFlow g t a)=a := by
  rw [← scalarFlow_add,neg_add_cancel,scalarFlow_zero]

theorem scalarFlow_bijective (g : PeriodicScalarField) (t : ℝ) : Function.Bijective (scalarFlow g t) := by
  constructor
  · intro a b hab
    have h := congrArg (scalarFlow g (-t)) hab
    simpa only [scalarFlow_inverse] using h
  · intro b
    refine ⟨scalarFlow g (-t) b,?_⟩
    simpa only [neg_neg] using scalarFlow_inverse g (-t) b

def scalarFlowEquiv (g : PeriodicScalarField) (t : ℝ) : ℝ ≃ ℝ where
  toFun := scalarFlow g t
  invFun := scalarFlow g (-t)
  left_inv := scalarFlow_inverse g t
  right_inv := by intro a; simpa only [neg_neg] using scalarFlow_inverse g (-t) a

theorem scalarFlow_time_smooth (g : PeriodicScalarField) (a : ℝ) :
    ContDiff ℝ ∞ (fun t => scalarFlow g t a) := by
  have hd : Differentiable ℝ (fun t => scalarFlow g t a) := fun t => (scalarFlow_hasDerivAt g a t).differentiableAt
  have he : deriv (fun t => scalarFlow g t a)=g ∘ (fun t => scalarFlow g t a) :=
    funext fun t => (scalarFlow_hasDerivAt g a t).deriv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hd.continuous
  | succ n ih =>
    rw [Nat.cast_succ,contDiff_succ_iff_deriv]
    refine ⟨hd,by simp,?_⟩
    rw [he]
    exact (contDiff_infty.mp g.smooth n).comp ih

end
end SolitonClassification.Rotating.NormalEvolution

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for ax in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Scalar reparameterization audit failed: {name} depends on {ax}"
      count := count+1
  logInfo m!"Actual periodic scalar flow audited: {count} declarations; standard axioms only."
