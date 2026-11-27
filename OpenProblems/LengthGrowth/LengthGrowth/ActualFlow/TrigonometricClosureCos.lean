import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Real Set MeasureTheory
namespace LengthGrowth.Multicover.Outward.TrigonometricClosure

private theorem primitive_nonneg {f g : ℝ→ℝ} (df : ∀x, HasDerivAt f (g x) x)
    (zero : f 0=0) (hg : ∀x,0≤x → 0≤g x) : ∀x,0≤x → 0≤f x := by
  have cont : Continuous f := continuous_iff_continuousAt.mpr (fun x=>(df x).continuousAt)
  have mon := monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ)) cont.continuousOn
    (fun x _=>(df x).differentiableAt.differentiableWithinAt)
    (fun x hx=>by rw [(df x).deriv];exact hg x (interior_subset hx))
  intro x hx
  simpa only [zero] using mon (show (0:ℝ)∈Ici 0 by simp) (Set.mem_Ici.mpr hx) hx

private theorem cos_bounds_pos : ∀x:ℝ, 0≤x →
    1-x^2/2+x^4/24-x^6/720≤cos x ∧ cos x≤1-x^2/2+x^4/24-x^6/720+x^8/40320 := by
  have h0 (x:ℝ) (_hx : 0≤x) : 0≤1-cos x := sub_nonneg.mpr (cos_le_one x)
  have h1 : ∀x:ℝ,0≤x → 0≤x-sin x := by
    apply primitive_nonneg (g:=fun x=>1-cos x) _ (by norm_num) h0
    intro x
    convert! ((hasDerivAt_id x).sub (hasDerivAt_sin x)) using 1
  have h2 : ∀x:ℝ,0≤x → 0≤x^2/2-1+cos x := by
    apply primitive_nonneg (g:=fun x=>x-sin x) _ (by norm_num) h1
    intro x
    convert! (((((hasDerivAt_id x).pow 2).div_const 2).sub (hasDerivAt_const x (1:ℝ))).add (hasDerivAt_cos x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h3 : ∀x:ℝ,0≤x → 0≤x^3/6-x+sin x := by
    apply primitive_nonneg (g:=fun x=>x^2/2-1+cos x) _ (by norm_num) h2
    intro x
    convert! (((((hasDerivAt_id x).pow 3).div_const 6).sub (hasDerivAt_id x)).add (hasDerivAt_sin x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h4 : ∀x:ℝ,0≤x → 0≤x^4/24-x^2/2+1-cos x := by
    apply primitive_nonneg (g:=fun x=>x^3/6-x+sin x) _ (by norm_num) h3
    intro x
    convert! ((((((hasDerivAt_id x).pow 4).div_const 24).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (hasDerivAt_const x (1:ℝ))).sub (hasDerivAt_cos x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h5 : ∀x:ℝ,0≤x → 0≤x^5/120-x^3/6+x-sin x := by
    apply primitive_nonneg (g:=fun x=>x^4/24-x^2/2+1-cos x) _ (by norm_num) h4
    intro x
    convert! ((((((hasDerivAt_id x).pow 5).div_const 120).sub (((hasDerivAt_id x).pow 3).div_const 6)).add (hasDerivAt_id x)).sub (hasDerivAt_sin x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h6 : ∀x:ℝ,0≤x → 0≤x^6/720-x^4/24+x^2/2-1+cos x := by
    apply primitive_nonneg (g:=fun x=>x^5/120-x^3/6+x-sin x) _ (by norm_num) h5
    intro x
    convert! (((((((hasDerivAt_id x).pow 6).div_const 720).sub (((hasDerivAt_id x).pow 4).div_const 24)).add (((hasDerivAt_id x).pow 2).div_const 2)).sub (hasDerivAt_const x (1:ℝ))).add (hasDerivAt_cos x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h7 : ∀x:ℝ,0≤x → 0≤x^7/5040-x^5/120+x^3/6-x+sin x := by
    apply primitive_nonneg (g:=fun x=>x^6/720-x^4/24+x^2/2-1+cos x) _ (by norm_num) h6
    intro x
    convert! (((((((hasDerivAt_id x).pow 7).div_const 5040).sub (((hasDerivAt_id x).pow 5).div_const 120)).add (((hasDerivAt_id x).pow 3).div_const 6)).sub (hasDerivAt_id x)).add (hasDerivAt_sin x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  have h8 : ∀x:ℝ,0≤x → 0≤x^8/40320-x^6/720+x^4/24-x^2/2+1-cos x := by
    apply primitive_nonneg (g:=fun x=>x^7/5040-x^5/120+x^3/6-x+sin x) _ (by norm_num) h7
    intro x
    convert! ((((((((hasDerivAt_id x).pow 8).div_const 40320).sub (((hasDerivAt_id x).pow 6).div_const 720)).add (((hasDerivAt_id x).pow 4).div_const 24)).sub (((hasDerivAt_id x).pow 2).div_const 2)).add (hasDerivAt_const x (1:ℝ))).sub (hasDerivAt_cos x)) using 1
    all_goals simp only [id_eq]
    all_goals ring
  intro x hx
  constructor <;> linarith only [h6 x hx,h8 x hx]

theorem cos_bounds (x : ℝ) :
    1-x^2/2+x^4/24-x^6/720≤cos x ∧ cos x≤1-x^2/2+x^4/24-x^6/720+x^8/40320 := by
  rcases le_total 0 x with hx|hx
  · exact cos_bounds_pos x hx
  · have h := cos_bounds_pos (-x) (neg_nonneg.mpr hx)
    simpa only [cos_neg,neg_sq,show (-x)^4=x^4 by ring,show (-x)^6=x^6 by ring,
      show (-x)^8=x^8 by ring] using h

end LengthGrowth.Multicover.Outward.TrigonometricClosure
#print axioms LengthGrowth.Multicover.Outward.TrigonometricClosure.cos_bounds
