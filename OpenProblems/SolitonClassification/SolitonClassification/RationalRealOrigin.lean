import SolitonClassification.RationalPoleMean
import SolitonClassification.RationalPoleSum
import Mathlib.Algebra.Polynomial.Splits

noncomputable section
open Polynomial Lagrange Set Function MeasureTheory
open scoped Polynomial
namespace ClosedSimilarity.RationalArclength

theorem bounded_polynomial_part {A B : ℂ[X]} (bn : B≠0) (h : A.degree ≤ B.degree) :
    ∃ c : ℂ, (A-C c*B).degree < B.degree := by
  rcases h.lt_or_eq with lt|eq
  · exact ⟨0,by simpa using lt⟩
  · have an : A≠0 := fun az => bn (Polynomial.degree_eq_bot.mp (eq ▸ (az ▸ degree_zero)))
    let c := A.leadingCoeff / B.leadingCoeff
    have cn : c≠0 := div_ne_zero (leadingCoeff_ne_zero.mpr an) (leadingCoeff_ne_zero.mpr bn)
    have eq' : A.degree = (C c*B).degree := eq.trans (degree_C_mul cn).symm
    have top : A.leadingCoeff = (C c*B).leadingCoeff := by
      rw [leadingCoeff_mul,leadingCoeff_C]
      exact (div_mul_cancel₀ _ (leadingCoeff_ne_zero.mpr bn)).symm
    refine ⟨c,?_⟩
    rw [←eq]
    exact degree_sub_lt_left eq' an top

private theorem factor_simple {B : ℂ[X]} (bn : B≠0) (split : B.Splits)
    (simple : ∀ α, B.eval α=0 → B.rootMultiplicity α=1) :
    B=C B.leadingCoeff * nodal B.roots.toFinset id := by
  classical
  have nd : B.roots.Nodup := Multiset.nodup_iff_count_le_one.mpr (fun α => by
    by_cases mem : α ∈ B.roots
    · rw [count_roots, simple α ((Polynomial.mem_roots bn).mp mem)]
    · simp [Multiset.count_eq_zero.mpr mem])
  have eq := split.eq_prod_roots
  convert! eq using 2
  change ((B.roots.toFinset.val).map (fun z : ℂ => X-C z)).prod = _
  rw [Multiset.toFinset_val,nd.dedup]

/-- All values on the unit circle are real, so the constant part has zero
imaginary part by angular averaging. Evaluating the same fractions at zero
then makes the value at zero real as well. -/
theorem real_origin_of_unit_circle_of_splits {A B : ℂ[X]} (bn : B≠0) (split : B.Splits) (b0 : B.eval 0≠0)
    (deg : A.degree≤B.degree) (simple : ∀ α, B.eval α=0 → B.rootMultiplicity α=1)
    (residue : ∀ α, B.eval α=0 → ∃r : ℝ, A.eval α/B.derivative.eval α=(r:ℂ)*α)
    (safe : ∀s, B.eval (unitPhase s)≠0)
    (reality : ∀s, (A.eval (unitPhase s)/B.eval (unitPhase s)).im=0) :
    (A.eval 0/B.eval 0).im=0 := by
  classical
  let S := B.roots.toFinset
  have hb : B.leadingCoeff≠0 := leadingCoeff_ne_zero.mpr bn
  have fac := factor_simple bn split simple
  obtain ⟨v,p⟩ := bounded_polynomial_part bn deg
  let r := fun α => (A.eval α/(α*B.derivative.eval α)).re
  have scalar (α : ℂ) (mem : α∈S) :
      A.eval α/B.derivative.eval α = (r α : ℂ)*α ∧ (A.eval α/(α*B.derivative.eval α)).im=0 := by
    have root : B.eval α=0 := (mem_roots bn).mp (Multiset.mem_toFinset.mp mem)
    have az : α≠0 := fun eq => b0 (eq ▸ root)
    obtain ⟨q,eq⟩ := residue α root
    have z : A.eval α/(α*B.derivative.eval α) = (q:ℂ) := by
      rw [mul_comm α,div_mul_eq_div_div,eq,mul_div_cancel_right₀ _ az]
    simp [r,z,eq]
  let P := 2*Real.pi
  have point (s : ℝ) : -v.im = ∑ α ∈ S,r α*(α/(unitPhase s-α)).im := by
    have f := partial_fraction_nonroot S A B B.leadingCoeff v hb fac p (unitPhase s) (safe s)
    have h := congrArg Complex.im f
    rw [Complex.sub_im,reality,zero_sub,Complex.im_sum] at h
    refine h.trans (Finset.sum_congr rfl (fun α ha => ?_))
    rw [(scalar α ha).1,mul_div_assoc,Complex.im_ofReal_mul]
  have cont (α : ℂ) (ha : α∈S) : Continuous (fun s => r α*(α/(unitPhase s-α)).im) := by
    have root : B.eval α=0 := (mem_roots bn).mp (Multiset.mem_toFinset.mp ha)
    have neq (s : ℝ) : unitPhase s-α≠0 := fun eq => safe s ((sub_eq_zero.mp eq).symm ▸ root)
    have phase : Continuous unitPhase := by unfold unitPhase;fun_prop
    exact continuous_const.mul (Complex.continuous_im.comp (continuous_const.div (phase.sub continuous_const) neq))
  have zero : ∀ α∈S, (∫s in 0..P, r α*(α/(unitPhase s-α)).im)=0 := by
    intro α _
    rw [intervalIntegral.integral_const_mul,pole_imaginary_average,mul_zero]
  have integ := congrArg (fun f : ℝ→ℝ => ∫s in 0..P,f s) (funext point)
  change (∫_s in (0:ℝ)..P,-v.im) = ∫s in 0..P,∑ α ∈ S,r α*(α/(unitPhase s-α)).im at integ
  rw [intervalIntegral.integral_finsetSum (fun i hi => (cont i hi).intervalIntegrable ..),
    Finset.sum_eq_zero zero,intervalIntegral.integral_const,sub_zero,smul_eq_mul] at integ
  have vv := (mul_eq_zero.mp integ).resolve_left (show P≠0 by dsimp [P];positivity)
  have t := congrArg Complex.im (pole_sum_at_zero S A B B.leadingCoeff v hb fac b0 p)
  rw [Complex.sub_im,Complex.neg_im,Complex.im_sum,Finset.sum_eq_zero (fun α ha => (scalar α ha).2)] at t
  linarith

end ClosedSimilarity.RationalArclength
#print axioms ClosedSimilarity.RationalArclength.real_origin_of_unit_circle_of_splits

