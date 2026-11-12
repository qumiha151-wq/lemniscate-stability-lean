import LengthGrowth.AbsoluteCurvatureCoercivity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Construct the actual Frenet data from a smooth periodic unit-speed position.
This is not a reparametrization theorem for curves given at arbitrary speed. -/
noncomputable section
open Set
open scoped ComplexConjugate ContDiff
namespace LengthGrowth

def positionCurvature (γ : ℝ → ℂ) (s : ℝ) : ℝ :=
  (conj (deriv γ s) * deriv (deriv γ) s).im

theorem periodic_actual_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {L : ℝ}
    (hp : Function.Periodic f L) (hd : Differentiable ℝ f) :
    Function.Periodic (deriv f) L := by
  intro s
  have h := (hd (s+L)).hasDerivAt.scomp s ((hasDerivAt_id s).add_const L)
  have he : (fun u => f (u+L))=f := funext hp
  simp only [one_smul] at h
  change HasDerivAt (fun u => f (u+L)) (deriv f (s+L)) s at h
  rw [he] at h
  exact h.unique (hd s).hasDerivAt

theorem position_curvature_smooth {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (positionCurvature γ) := by
  have hT := (contDiff_infty_iff_deriv.mp hγ).2
  have hA := (contDiff_infty_iff_deriv.mp hT).2
  exact Complex.imCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp hT).mul hA)

theorem unit_tangent_frenet {T : ℝ → ℂ} (hT : Differentiable ℝ T)
    (hu : ∀ s, ‖T s‖=1) (s : ℝ) :
    deriv T s=(((conj (T s)*deriv T s).im : ℝ) : ℂ)*(Complex.I*T s) := by
  have hunit (u : ℝ) : T u*conj (T u)=1 := by
    rw [Complex.mul_conj]
    simp [Complex.normSq_eq_norm_sq,hu]
  have hconst : (fun u => conj (T u)*T u)=(fun _ => (1:ℂ)) := by
    funext u
    rw [mul_comm,hunit u]
  have hd := ((hT s).hasDerivAt.star).mul (hT s).hasDerivAt
  change HasDerivAt (fun u => conj (T u)*T u)
    (conj (deriv T s)*T s+conj (T s)*deriv T s) s at hd
  rw [hconst] at hd
  have hz := hd.unique (hasDerivAt_const s (1:ℂ))
  have hre : (conj (T s)*deriv T s).re=0 := by
    have h := congrArg Complex.re hz
    simp only [Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im,
      Complex.zero_re] at h ⊢
    linarith
  have hdecomp : conj (T s)*deriv T s=
      (((conj (T s)*deriv T s).im : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp [hre]
  calc
    deriv T s = (T s*conj (T s))*deriv T s := by rw [hunit,one_mul]
    _ = T s*(conj (T s)*deriv T s) := by ring
    _ = T s*((((conj (T s)*deriv T s).im : ℝ) : ℂ)*Complex.I) :=
      congrArg (fun z => T s*z) hdecomp
    _ = _ := by ring

/-- Only the position, positive period, actual smoothness, periodicity and unit
speed are supplied. Every Frenet field is built from actual derivatives. -/
def closedFrenetCurveOfPosition (γ : ℝ → ℂ) (L : ℝ) (hL : 0<L)
    (hp : Function.Periodic γ L) (hγ : ContDiff ℝ ∞ γ)
    (hu : ∀ s, ‖deriv γ s‖=1) : ClosedFrenetCurve := by
  have hT := (contDiff_infty_iff_deriv.mp hγ).2
  have hA := (contDiff_infty_iff_deriv.mp hT).2
  have hk := position_curvature_smooth hγ
  have hk₁ := (contDiff_infty_iff_deriv.mp hk).2
  have hk₂ := (contDiff_infty_iff_deriv.mp hk₁).2
  have hpT := periodic_actual_deriv hp (hγ.differentiable (by simp))
  have hpA := periodic_actual_deriv hpT (hT.differentiable (by simp))
  have hpk : Function.Periodic (positionCurvature γ) L := by
    intro s
    simp only [positionCurvature,hpT s,hpA s]
  exact {
    period := L
    period_pos := hL
    curve := γ
    tangent := deriv γ
    curvature := positionCurvature γ
    curvature₁ := deriv (positionCurvature γ)
    curvature₂ := deriv (deriv (positionCurvature γ))
    curve_periodic := hp
    tangent_periodic := hpT
    curvature_periodic := hpk
    curvature₁_periodic := periodic_actual_deriv hpk (hk.differentiable (by simp))
    curve_deriv := fun s => (hγ.differentiable (by simp) s).hasDerivAt
    tangent_deriv := fun s => by
      have hd := (hT.differentiable (by simp) s).hasDerivAt
      rw [unit_tangent_frenet (hT.differentiable (by simp)) hu s] at hd
      exact hd
    curvature_deriv := fun s => (hk.differentiable (by simp) s).hasDerivAt
    curvature₁_deriv := fun s => (hk₁.differentiable (by simp) s).hasDerivAt
    curvature₂_continuous := hk₂.continuous
    tangent_unit := hu }

theorem actual_position_stress_coercivity (γ : ℝ → ℂ) (L : ℝ) (hL : 0<L)
    (hp : Function.Periodic γ L) (hγ : ContDiff ℝ ∞ γ)
    (hu : ∀ s, ‖deriv γ s‖=1) (s : ℝ) :
    (1/16777216:ℝ)*|positionCurvature γ s|^6 ≤
      ((∫ u in 0..L, positionCurvature γ u^2)/2)*
      (∫ u in 0..L, (deriv (deriv (positionCurvature γ)) u+
        positionCurvature γ u^3/2)^2) :=
  (closedFrenetCurveOfPosition γ L hL hp hγ hu).energy_dissipation_controls_curvature s

theorem actual_position_absolute_curvature_coercivity (γ : ℝ → ℂ) (L : ℝ) (hL : 0<L)
    (hp : Function.Periodic γ L) (hγ : ContDiff ℝ ∞ γ)
    (hu : ∀ s, ‖deriv γ s‖=1) :
    (1/262144:ℝ)*((∫ u in 0..L, positionCurvature γ u^2)/2)^5/
      (∫ u in 0..L, |positionCurvature γ u|)^6 ≤
      ∫ u in 0..L, (deriv (deriv (positionCurvature γ)) u+
        positionCurvature γ u^3/2)^2 :=
  (closedFrenetCurveOfPosition γ L hL hp hγ hu).absolute_curvature_coercivity

end LengthGrowth

#print axioms LengthGrowth.actual_position_stress_coercivity
#print axioms LengthGrowth.actual_position_absolute_curvature_coercivity

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`LengthGrowth).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Position-curve audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"LengthGrowth actual-position coercivity audit passed for {count} declarations."
