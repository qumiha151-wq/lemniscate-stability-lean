import SolitonClassification.CentreShotWinding
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set MeasureTheory OuterStress

/-- Uniformly choose the lift along each trajectory by starting its phase at
    zero. Positivity is only required before the chosen crossing time. -/
theorem centre_phase_continuous {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    (b τ : P → ℝ) (cb : Continuous b) (ct : Continuous τ)
    (hb : ∀ p, 0<b p) (ht : ∀ p, 0≤τ p)
    (safe : ∀ p, ∀ t ∈ Icc 0 (τ p), 0 < (centreData (b p) (hb p)).amplitude t) :
    let z := fun p => centreData (b p) (hb p)
    Continuous (fun p => ∫ t in 0..τ p, Angle.spin (b p)⁻¹ (z p).root
      (z p).shape (z p).slope (z p).along (z p).across t) := by
  intro z
  let g := fun (p : P) (t : ℝ) => Angle.spin (b p)⁻¹ (z p).root
    (z p).shape (z p).slope (z p).along (z p).across t
  let clip := fun u : P × ℝ => max 0 (min u.2 (τ u.1))
  have cc : Continuous clip := continuous_const.max (continuous_snd.min (ct.comp continuous_fst))
  have within (u : P × ℝ) : clip u ∈ Icc 0 (τ u.1) :=
    ⟨le_max_left _ _,max_le (ht _) (min_le_right _ _)⟩
  have cd := (cb.comp continuous_fst).inv₀ (fun u : P × ℝ => (hb u.1).ne')
  have cf := cd.sqrt
  have fp (u : P × ℝ) : 0 < Real.sqrt (b u.1)⁻¹ := Real.sqrt_pos.mpr (inv_pos.mpr (hb u.1))
  let init := fun u : P × ℝ => (![0,b u.1,0,0] : Phase)
  have ci : Continuous init := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp [init] <;> fun_prop
  have phys := continuous_solution.comp ((cc.div cf (fun u => (fp u).ne')).prodMk
    ((continuous_const (y := (1:ℝ))).prodMk ci))
  have ev (i : Fin 4) := (continuous_apply i).comp phys
  have K : Continuous (fun u : P × ℝ => (z u.1).K (clip u)) := cf.mul (ev 0)
  have V : Continuous (fun u : P × ℝ => (z u.1).V (clip u)) := cd.mul (ev 1)
  have p : Continuous (fun u : P × ℝ => (z u.1).p (clip u)) := cf.mul (ev 2)
  have q : Continuous (fun u : P × ℝ => (z u.1).q (clip u)) := cf.mul (ev 3)
  have A : Continuous (fun u : P × ℝ => (z u.1).amplitude (clip u)) :=
    ((((K.pow 2).div_const 2).pow 2).add (V.pow 2)).sqrt
  have r : Continuous (fun u : P × ℝ => (z u.1).root (clip u)) := A.sqrt
  have ap (u : P × ℝ) : 0 < (z u.1).amplitude (clip u) := safe u.1 _ (within u)
  have rp (u : P × ℝ) : 0 < (z u.1).root (clip u) := Real.sqrt_pos.mpr (ap u)
  have U : Continuous (fun u : P × ℝ => (z u.1).shape (clip u)) := K.div r fun u => (rp u).ne'
  have w : Continuous (fun u : P × ℝ => (z u.1).slope (clip u)) := V.div A fun u => (ap u).ne'
  have a : Continuous (fun u : P × ℝ => (z u.1).along (clip u)) :=
    ((((K.pow 2).div_const 2).mul q).add (V.mul p)).div A fun u => (ap u).ne'
  have k : Continuous (fun u : P × ℝ => (z u.1).across (clip u)) :=
    ((((K.pow 2).div_const 2).mul p).sub (V.mul q)).div A fun u => (ap u).ne'
  have cont : Continuous (fun u : P × ℝ => g u.1 (clip u)) := by
    apply (((continuous_const.add ((U.pow 2).div_const 2)).sqrt).div_const _).mul
    apply (r.div cd (fun u => (inv_pos.mpr (hb u.1)).ne')).add
    exact (U.mul ((w.mul a).add (((U.pow 2).div_const 2).mul k))).div
      (continuous_const.mul (r.pow 2)) (fun u => mul_ne_zero (by norm_num) (pow_ne_zero 2 (rp u).ne'))
  have cert := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ:=volume) (a₀:=0) (f:=fun p t => g p (clip (p,t))) cont ct
  apply cert.congr
  intro p
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le (ht p)]
  intro t tmem
  simp [clip,min_eq_left tmem.2,max_eq_right tmem.1,g]

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.centre_phase_continuous
