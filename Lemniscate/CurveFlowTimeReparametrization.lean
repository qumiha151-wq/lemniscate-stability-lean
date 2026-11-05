import Lemniscate.StaticCurveReparametrization
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Normal velocity and elastic force under a smooth time-dependent
orientation-preserving change of the space parameter. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff ComplexConjugate

private theorem reparametrized_time_hasDerivAt
    (Y : ℝ → ℝ → ℂ) (f : ℝ → ℝ) (t₀ c : ℝ)
    (hY : DifferentiableAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (t₀,f t₀))
    (hf : HasDerivAt f c t₀) :
    HasDerivAt (fun z => Y z (f z))
      (deriv (fun z => Y z (f t₀)) t₀+(c:ℂ)*deriv (Y t₀) (f t₀)) t₀ := by
  let L := fderiv ℝ (fun p : ℝ × ℝ => Y p.1 p.2) (t₀,f t₀)
  have htime := hY.hasFDerivAt.comp_hasDerivAt t₀
    ((hasDerivAt_id t₀).prodMk (hasDerivAt_const t₀ (f t₀)))
  change HasDerivAt (fun z => Y z (f t₀)) (L (1,0)) t₀ at htime
  have hspace := hY.hasFDerivAt.comp_hasDerivAt (f t₀)
    ((hasDerivAt_const (f t₀) t₀).prodMk (hasDerivAt_id (f t₀)))
  change HasDerivAt (Y t₀) (L (0,1)) (f t₀) at hspace
  have hchain := hY.hasFDerivAt.comp_hasDerivAt t₀ ((hasDerivAt_id t₀).prodMk hf)
  change HasDerivAt (fun z => Y z (f z)) (L (1,c)) t₀ at hchain
  have hpair : ((1:ℝ),c) = ((1:ℝ),0)+c • ((0:ℝ),1) := by
    ext <;> simp
  have hvalue : L (1,c) =
      deriv (fun z => Y z (f t₀)) t₀+(c:ℂ)*deriv (Y t₀) (f t₀) := by
    rw [htime.deriv,hspace.deriv,hpair,map_add,map_smul]
    simp only [real_smul]
  rw [hvalue] at hchain
  exact hchain

private theorem tangential_normal_pair_zero (v : ℂ) (c : ℝ) :
    (conj ((c:ℂ)*v)*(I*v/(‖v‖:ℂ))).re = 0 := by
  have hpair : conj ((c:ℂ)*v)*(I*v) = I*((c*‖v‖^2:ℝ):ℂ) := by
    rw [map_mul,Complex.conj_ofReal]
    calc
      _ = I*(c:ℂ)*(conj v*v) := by ring
      _ = _ := by rw [Complex.conj_mul']; push_cast; ring
  rw [← mul_div_assoc,Complex.div_ofReal_re,hpair]
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,one_mul,sub_zero,zero_div]

/-- A genuine time-dependent reparametrization adds the actual tangential
velocity χ_t Y_s. Its normal velocity is therefore the original normal
velocity, and its elastic force is the original elastic force evaluated
at the new parameter. No evolution equation is assumed. -/
theorem curve_flow_time_reparametrization
    (Y : ℝ → ℝ → ℂ) (χ : ℝ → ℝ → ℝ) (t₀ : ℝ) (c : ℝ → ℝ)
    (hYspace : ContDiff ℝ ∞ (Y t₀)) (hχspace : ContDiff ℝ ∞ (χ t₀))
    (hreg : ∀ s, deriv (Y t₀) s ≠ 0)
    (hpos : ∀ s, 0 < deriv (χ t₀) s)
    (hYjoint : ∀ s, DifferentiableAt ℝ (fun p : ℝ × ℝ => Y p.1 p.2)
      (t₀,χ t₀ s))
    (hχtime : ∀ s, HasDerivAt (fun z => χ z s) (c s) t₀) :
    let Γ : ℝ → ℝ → ℂ := fun t s => Y t (χ t s)
    ∀ s,
      let ν := I*deriv (Γ t₀) s/(‖deriv (Γ t₀) s‖:ℂ)
      HasDerivAt (fun z => Γ z s)
        (deriv (fun z => Y z (χ t₀ s)) t₀+(c s:ℂ)*deriv (Y t₀) (χ t₀ s)) t₀ ∧
      deriv (Γ t₀) s ≠ 0 ∧ ‖ν‖ = 1 ∧
      ν = I*deriv (Y t₀) (χ t₀ s)/(‖deriv (Y t₀) (χ t₀ s)‖:ℂ) ∧
      (conj (deriv (fun z => Γ z s) t₀)*ν).re =
        (conj (deriv (fun z => Y z (χ t₀ s)) t₀)*
          (I*deriv (Y t₀) (χ t₀ s)/(‖deriv (Y t₀) (χ t₀ s)‖:ℂ))).re ∧
      arclengthDerivative (Γ t₀)
            (arclengthDerivative (Γ t₀) (planarSignedCurvature (Γ t₀))) s+
          (1/2:ℝ)*(planarSignedCurvature (Γ t₀) s)^3 =
        arclengthDerivative (Y t₀)
            (arclengthDerivative (Y t₀) (planarSignedCurvature (Y t₀))) (χ t₀ s)+
          (1/2:ℝ)*(planarSignedCurvature (Y t₀) (χ t₀ s))^3 := by
  have hgeom := oriented_reparametrization_elastic_geometry (Y t₀) (χ t₀)
    hYspace hχspace hreg hpos
  dsimp only
  intro s
  have hnormal := (hgeom.1 s).2
  have hforce := congrArg (fun f : ℝ → ℝ => f s) hgeom.2.2.2
  dsimp only [Function.comp_def] at hnormal hforce
  have hvelocity := reparametrized_time_hasDerivAt Y (fun z => χ z s)
    t₀ (c s) (hYjoint s) (hχtime s)
  refine ⟨hvelocity,(hgeom.1 s).1,?_,hnormal,?_,hforce⟩
  · rw [hnormal]
    rw [norm_div,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (deriv (Y t₀) (χ t₀ s)))]
    exact div_self (norm_ne_zero_iff.mpr (hreg (χ t₀ s)))
  · rw [hnormal,hvelocity.deriv,map_add,add_mul,Complex.add_re,
      tangential_normal_pair_zero,add_zero]

end Lemniscate
