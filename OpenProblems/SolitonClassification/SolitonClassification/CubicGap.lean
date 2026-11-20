import SolitonClassification.SolitonDilation
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Sharp centered cubic-moment inequality for an actual periodic support
profile. Equality characterizes the centered circles, including their covers. -/
noncomputable section
namespace ClosedSimilarity.PeriodicSupportProfile
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false
variable {a b L : ℝ} (z : PeriodicSupportProfile a b L)

def totalSignedCurvature : ℝ := ∫ t in 0..L, z.k t

/-- An affine force law of nonzero slope excludes every nonconstant periodic
support orbit, even when its tangent angle has nonintegral holonomy. -/
theorem constant_curvature_of_affine_force (hL : 0 < L) {c d : ℝ} (hc : c ≠ 0)
    (haff : ∀ s, z.force s = c*z.k s+d) : ∃ K, ∀ s, z.k s = K := by
  by_contra hn
  obtain ⟨⟨x,hx⟩,y,hy⟩ := z.both_curvature_excursions_of_period hL hn
  have hr := z.curvatureRMS_pos (z.dilation_pos hL) hL
  obtain ⟨t,ht⟩ := intermediate_value_univ x y z.continuous_k
    (show (0:ℝ) ∈ Icc (z.k x) (z.k y) from ⟨by linarith,by linarith⟩)
  let H : ℝ → ℝ := fun s => (a*z.q s-b*z.p s)/c
  have cH : Continuous H :=
    ((z.continuous_q.const_mul a).sub (z.continuous_p.const_mul b)).div_const c
  have eqv (s : ℝ) : z.v s=H s*z.k s-b/c := by
    have hF := ((z.dp s).const_mul (-a)).sub ((z.dq s).const_mul b)
    change HasDerivAt z.force _ s at hF
    rw [show z.force=(fun s => c*z.k s+d) from funext haff] at hF
    have h := hF.unique (((z.dk s).const_mul c).add_const d)
    dsimp [H]
    field_simp [hc]
    linarith
  let w : ℝ → ℝ := fun s => Real.exp (-(∫ u in t..s,H u))
  have dw (s : ℝ) : HasDerivAt w (w s*(-H s)) s := by
    exact (intervalIntegral.integral_hasDerivAt_right (cH.intervalIntegrable t s)
      cH.aestronglyMeasurable.stronglyMeasurableAtFilter cH.continuousAt).neg.exp
  let G : ℝ → ℝ := fun s => w s*z.k s
  have dG (s : ℝ) : HasDerivAt G (w s*(-(b/c))) s := by
    have e : w s*(-(b/c)) = w s*(-H s)*z.k s+w s*z.v s := by rw [eqv s]; ring
    rw [e]
    exact (dw s).mul (z.dk s)
  have cG : Continuous G := continuous_iff_continuousAt.mpr fun s => (dG s).continuousAt
  have eqends : G t = G (t+L) := by simp only [G,z.periodic_k t,ht,mul_zero]
  obtain ⟨s,_,hz⟩ := exists_hasDerivAt_eq_zero (show t<t+L by linarith) cG.continuousOn
    eqends (fun s _ => dG s)
  have hb : -(b/c) = 0 := (mul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'
  have dG0 (s : ℝ) : HasDerivAt G 0 s := by simpa only [hb,mul_zero] using dG s
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=t) (b:=y)
    (fun s _ => dG0 s) (continuous_const.intervalIntegrable t y)
  simp only [intervalIntegral.integral_zero,G,ht,mul_zero,sub_zero] at hi
  have hky := (mul_eq_zero.mp hi.symm).resolve_left (Real.exp_pos _).ne'
  linarith

def centeredResidual (s : ℝ) : ℝ :=
  4*L*z.force s-z.bending*z.k s-
    (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)/L

theorem centered_cubic_exact (hL : 0 < L) :
    L * (∫ s in 0..L,(z.centeredResidual s)^2) =
      L*z.bending^3-(2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)^2 := by
  let B := z.bending
  let X := (2*L*z.cubicMoment-B*z.totalSignedCurvature)/L
  have hf := z.continuous_force
  have hk := z.continuous_k
  have hi : (∫ s in 0..L, (z.centeredResidual s)^2) =
      (4*L)^2*z.forceSquare+B^2*z.bending+L*X^2+
      (-2*(4*L)*B)*(∫ s in 0..L,z.k s*z.force s)+
      (-2*(4*L)*X)*(∫ s in 0..L,z.force s)+(2*B*X)*z.totalSignedCurvature := by
    calc
      _ = ∫ s in 0..L,(4*L)^2*(z.force s)^2+B^2*(z.k s)^2+X^2+
          (-2*(4*L)*B)*(z.k s*z.force s)+(-2*(4*L)*X)*z.force s+(2*B*X)*z.k s := by
            apply intervalIntegral.integral_congr
            intro s _
            change (4*L*z.force s-B*z.k s-X)^2 = _
            ring
      _ = _ := by
        simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
          [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,
           intervalIntegral.integral_const,sub_zero,smul_eq_mul,forceSquare,bending,
           totalSignedCurvature]
  rw [hi,z.forceSquare_eq,z.integral_k_force,z.integral_force]
  dsimp [X,B]
  field_simp [hL.ne']
  ring

theorem cubic_coupling_le (hL : 0 < L) :
    (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)^2 ≤ L*z.bending^3 := by
  have he := z.centered_cubic_exact hL
  have hn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) hL.le
    (fun s => sq_nonneg (z.centeredResidual s))
  linarith only [he,mul_nonneg hL.le hn]

/-- Strict moment constraint on every noncircular profile, for every
rotation coefficient and every positive support period. -/
theorem cubic_coupling_lt (hL : 0 < L) (hn : ¬∃ c, ∀ s, z.k s = c) :
    (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)^2 < L*z.bending^3 := by
  by_contra! hw
  have he := le_antisymm (z.cubic_coupling_le hL) hw
  have hs := z.centered_cubic_exact hL
  rw [he,sub_self] at hs
  have hi := (mul_eq_zero.mp hs).resolve_left hL.ne'
  have hR : Continuous z.centeredResidual :=
    (((z.continuous_force.const_mul _).sub (z.continuous_k.const_mul _)).sub continuous_const)
  have hpt := continuous_nonneg_zero_of_integral_zero hL (hR.pow 2)
    (fun s _ => sq_nonneg _) hi
  have hper : Function.Periodic z.centeredResidual L := by
    intro s
    simp only [centeredResidual,force,z.periodic_k s,z.periodic_p s,z.periodic_q s]
  let X := (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)/L
  apply hn
  apply z.constant_curvature_of_affine_force hL (c:=z.bending/(4*L)) (d:=X/(4*L))
    (div_ne_zero (z.bending_pos_of_period hL).ne' (by positivity))
  intro s
  obtain ⟨t,ht,heq⟩ := hper.exists_mem_Ico₀ hL s
  have hr : z.centeredResidual s = 0 := heq.trans <| sq_eq_zero_iff.mp (hpt t ⟨ht.1,ht.2.le⟩)
  change 4*L*z.force s-z.bending*z.k s-X=0 at hr
  field_simp [hL.ne']
  linarith

/-- Scale-invariant form of the moment inequality, strict on every
nonconstant orbit. At period one the two terms are twice the normalized
signed third moment and the normalized mean signed curvature. -/
theorem normalized_cubic_coupling_lt_one (hL : 0 < L) (hn : ¬∃ c, ∀ s, z.k s = c) :
    |2*(L*z.cubicMoment/(z.bending*Real.sqrt (L*z.bending)))-
      z.totalSignedCurvature/Real.sqrt (L*z.bending)| < 1 := by
  let R := Real.sqrt (L*z.bending)
  have hB := z.bending_pos_of_period hL
  have hR : 0<R := Real.sqrt_pos.mpr (mul_pos hL hB)
  have hR2 : R^2=L*z.bending := Real.sq_sqrt (mul_pos hL hB).le
  have hh := z.cubic_coupling_lt hL hn
  have he : (z.bending*R)^2 = L*z.bending^3 := by rw [mul_pow,hR2]; ring
  rw [← he,← sq_abs (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)] at hh
  have hden := mul_pos hB hR
  have ha : |2*L*z.cubicMoment-z.bending*z.totalSignedCurvature| < z.bending*R :=
    lt_of_not_ge fun h => (not_le_of_gt hh) (pow_le_pow_left₀ hden.le h 2)
  change |2*(L*z.cubicMoment/(z.bending*R))-z.totalSignedCurvature/R|<1
  rw [show 2*(L*z.cubicMoment/(z.bending*R))-z.totalSignedCurvature/R =
      (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)/(z.bending*R) by
    field_simp [hB.ne',hR.ne'], abs_div,abs_of_pos hden]
  exact (div_lt_one hden).mpr ha

/-- Equality singles out exactly the centered round support profiles. -/
theorem cubic_coupling_eq_iff_centered_circle (hL : 0 < L) :
    (2*L*z.cubicMoment-z.bending*z.totalSignedCurvature)^2 = L*z.bending^3 ↔
      ∃ c : ℝ, c ≠ 0 ∧ c^4 = 2*a ∧ (∀ s, z.k s = c) ∧
        (∀ s, z.v s = 0) ∧ (∀ s, z.p s = -1/c) ∧ (∀ s, z.q s = 0) := by
  constructor
  · intro he
    have hconst : ∃ c, ∀ s,z.k s=c := by
      by_contra hn
      exact (z.cubic_coupling_lt hL hn).ne he
    obtain ⟨c,hc⟩ := hconst
    apply z.one_sign_centered_circle_of_period hL
    rcases le_total 0 c with hp | hp
    · exact Or.inl (fun s => (hc s).symm ▸ hp)
    · exact Or.inr (fun s => (hc s).symm ▸ hp)
  · rintro ⟨c,_,_,hk,_,_,_⟩
    simp only [cubicMoment,bending,totalSignedCurvature,hk,intervalIntegral.integral_const,
      sub_zero,smul_eq_mul]
    ring

end ClosedSimilarity.PeriodicSupportProfile

open Lean Elab Command in
run_cmd do
  let names := #[`ClosedSimilarity.PeriodicSupportProfile.constant_curvature_of_affine_force,
    `ClosedSimilarity.PeriodicSupportProfile.centered_cubic_exact,
    `ClosedSimilarity.PeriodicSupportProfile.cubic_coupling_le,
    `ClosedSimilarity.PeriodicSupportProfile.cubic_coupling_lt,
    `ClosedSimilarity.PeriodicSupportProfile.normalized_cubic_coupling_lt_one,
    `ClosedSimilarity.PeriodicSupportProfile.cubic_coupling_eq_iff_centered_circle]
  for n in names do
    for ax in (← collectAxioms n) do
      unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains ax do
        throwError "Unexpected axiom {ax} for {n}"
  logInfo m!"CUBIC_GAP_AUDIT: {names.size} declarations passed."
