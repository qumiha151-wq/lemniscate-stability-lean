import Lemniscate.NormalGraphPhaseSlice
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Differentiating the same normal projections selected for the H2 entry.
The parameter dependence is obtained from the finite-dimensional implicit
function theorem and uniqueness of the actual local projection roots. -/
noncomputable section
namespace Lemniscate
open Complex Set Filter
open scoped Topology ContDiff ComplexConjugate

private theorem selected_scalar_root_smooth
    (F : ℝ × ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (D : Set ℝ) (hD : IsOpen D) (u : ℝ → ℝ) (s r : ℝ)
    (hbound : ∀ θ ∈ D, |u θ-s| < r)
    (hroot : ∀ θ ∈ D, F (θ,u θ) = 0)
    (hpartial : ∀ θ ∈ D, deriv (fun x => F (θ,x)) (u θ) ≠ 0)
    (hunique : ∀ θ ∈ D, ∀ x, |x-s| ≤ r → F (θ,x) = 0 → x = u θ) :
    ∀ θ ∈ D, ContDiffAt ℝ ∞ u θ := by
  intro θ hθ
  let d := deriv (fun x => F (θ,x)) (u θ)
  have hdne : d ≠ 0 := hpartial θ hθ
  have hp : HasDerivAt (fun x => F (θ,x)) d (u θ) :=
    ((hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (u θ)).hasDerivAt
  have hpd : fderiv ℝ F (θ,u θ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d :=
    ((hp.hasFDerivAt).unique
      ((hF.differentiable (by simp) (θ,u θ)).hasFDerivAt.comp (u θ)
        (hasFDerivAt_prodMk_right θ (u θ)))).symm
  have hi : (fderiv ℝ F (θ,u θ) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    rw [hpd]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
    · ext x
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul]
      field_simp [hdne]
    · ext x
      simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.id_apply,smul_eq_mul]
      field_simp [hdne]
  let g := (hF.contDiffAt (x := (θ,u θ))).implicitFunction (by simp) hi
  have hg : ContDiffAt ℝ ∞ g θ :=
    (hF.contDiffAt (x := (θ,u θ))).contDiffAt_implicitFunction (by simp) hi
  have hself : g θ = u θ :=
    (hF.contDiffAt (x := (θ,u θ))).implicitFunction_apply_self (by simp) hi
  have hgin : ∀ᶠ t in 𝓝 θ, |g t-s| < r :=
    (hg.continuousAt.sub_const s).abs.eventually_lt continuousAt_const
      (by rw [hself]; exact hbound θ hθ)
  have hgeq := (hF.contDiffAt (x := (θ,u θ))).eventually_apply_implicitFunction (by simp) hi
  have hevent : u =ᶠ[𝓝 θ] g := by
    filter_upwards [hgin,hgeq,hD.mem_nhds hθ] with t ht he hDt
    exact (hunique t hDt (g t) ht.le (he.trans (hroot θ hθ))).symm
  exact hg.congr_of_eventuallyEq hevent

private def inverseRotation (θ : ℝ) : ℂ := Complex.exp ((-θ:ℝ)*I)

private theorem inverse_rotation_norm (θ : ℝ) : ‖inverseRotation θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (-θ)

private theorem inverse_rotation_deriv (θ : ℝ) :
    HasDerivAt inverseRotation (-I*inverseRotation θ) θ := by
  have hp := (((hasDerivAt_id θ).neg).ofReal_comp.mul_const I).cexp
  apply hp.congr_deriv
  simp only [inverseRotation,id_eq,Pi.neg_apply,Complex.ofReal_neg,Complex.ofReal_one]
  ring

/-- For any family of the actual local normal projections of a rotated
curve, the angular derivative of its height is minus the geometric
rotation field. The chosen projections (and hence their H2 norm bounds)
are preserved; no differentiability in the angular parameter is assumed. -/
theorem normal_graph_rotation_phase_derivative
    (γ β Tγ Tβ : ℝ → ℂ) (k : ℝ → ℝ)
    (hγsmooth : ContDiff ℝ ∞ γ)
    (hγ : ∀ s, HasDerivAt γ (Tγ s) s)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (huγ : ∀ s, ‖Tγ s‖ = 1) (huβ : ∀ s, ‖Tβ s‖ = 1)
    (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε)
    (hk : ∀ s, |k s| ≤ K) (hsmall : ε+K*(4*ε) ≤ 1/2)
    (a b : ℝ) (χ h : ℝ → ℝ → ℝ)
    (htangent : ∀ θ ∈ Ioo a b, ∀ s,
      ‖Complex.exp ((-θ:ℝ)*I)*Tγ s-Tβ s‖ ≤ ε)
    (hχsmooth : ∀ θ ∈ Ioo a b, ContDiff ℝ ∞ (χ θ))
    (hhsmooth : ∀ θ ∈ Ioo a b, ContDiff ℝ ∞ (h θ))
    (hgraph : ∀ θ ∈ Ioo a b, ∀ s,
      Complex.exp ((-θ:ℝ)*I)*γ (χ θ s) = β s+I*(h θ s:ℂ)*Tβ s)
    (hshift : ∀ θ ∈ Ioo a b, ∀ s, |χ θ s-s| ≤ 2*ε)
    (hχlower : ∀ θ ∈ Ioo a b, ∀ s, (1/4:ℝ) ≤ deriv (χ θ) s) :
    ∀ θ ∈ Ioo a b, ∀ s,
      0 < 1-k s*h θ s ∧
      HasDerivAt (fun t => h t s)
        (-((conj (Tβ s)*β s).re+
          ((conj (Tβ s)*β s).im+h θ s)*deriv (h θ) s/(1-k s*h θ s))) θ := by
  have hgraphR : ∀ θ ∈ Ioo a b, ∀ s,
      inverseRotation θ*γ (χ θ s) = β s+I*(h θ s:ℂ)*Tβ s := hgraph
  have hTlip (x y : ℝ) : ‖Tβ y-Tβ x‖ ≤ K*|y-x| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := K)
        (fun u _ => (hTβ u).hasDerivWithinAt)
        (fun u _ => by simpa only [norm_mul,Complex.norm_I,Complex.norm_real,
          Real.norm_eq_abs,huβ u,one_mul,mul_one] using hk u)
        convex_univ (mem_univ x) (mem_univ y)
  have hself (s : ℝ) : conj (Tβ s)*Tβ s = 1 := by
    rw [Complex.conj_mul',huβ s]
    norm_num
  let P : ℝ → ℝ → ℝ := fun θ s =>
    (conj (Tβ s)*(inverseRotation θ*Tγ (χ θ s))).re
  have hpositive (θ : ℝ) (hθ : θ ∈ Ioo a b) (s : ℝ) : 1/2 ≤ P θ s := by
    have hdist : ‖inverseRotation θ*Tγ (χ θ s)-Tβ s‖ ≤ ε+K*(4*ε) := by
      calc
        _ ≤ ‖inverseRotation θ*Tγ (χ θ s)-Tβ (χ θ s)‖+
            ‖Tβ (χ θ s)-Tβ s‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε+K*|χ θ s-s| := add_le_add (htangent θ hθ _) (hTlip s _)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
          ((hshift θ hθ s).trans (by linarith)) hK)
    have heq : 1-P θ s =
        (conj (Tβ s)*(Tβ s-inverseRotation θ*Tγ (χ θ s))).re := by
      dsimp only [P]
      rw [mul_sub,hself,Complex.sub_re,Complex.one_re]
    have hb : |1-P θ s| ≤ 1/2 := by
      rw [heq]
      have hn : ‖conj (Tβ s)*(Tβ s-inverseRotation θ*Tγ (χ θ s))‖ ≤ ε+K*(4*ε) := by
        rw [norm_mul,Complex.norm_conj,huβ s,one_mul,norm_sub_rev]
        exact hdist
      exact (Complex.abs_re_le_norm _).trans
        (hn.trans hsmall)
    linarith only [(abs_le.mp hb).1,(abs_le.mp hb).2]
  have hroot (θ : ℝ) (hθ : θ ∈ Ioo a b) (s : ℝ) :
      (conj (Tβ s)*(inverseRotation θ*γ (χ θ s)-β s)).re = 0 := by
    rw [hgraphR θ hθ s,add_sub_cancel_left]
    have heq : conj (Tβ s)*(I*(h θ s:ℂ)*Tβ s) = I*(h θ s:ℂ) := by
      calc
        _ = I*(h θ s:ℂ)*(conj (Tβ s)*Tβ s) := by ring
        _ = _ := by rw [hself,mul_one]
    rw [heq]
    simp only [Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
  have hparam (s θ : ℝ) (hθ : θ ∈ Ioo a b) : ContDiffAt ℝ ∞ (fun t => χ t s) θ := by
    let F : ℝ × ℝ → ℝ := fun z =>
      (conj (Tβ s)*(inverseRotation z.1*γ z.2-β s)).re
    have hF : ContDiff ℝ ∞ F := by
      have hcast : ContDiff ℝ ∞ (fun z : ℝ × ℝ => ((-z.1:ℝ):ℂ)) :=
        Complex.ofRealCLM.contDiff.comp contDiff_fst.neg
      have hC : ContDiff ℝ ∞ (fun z : ℝ × ℝ =>
          conj (Tβ s)*(Complex.exp ((-z.1:ℝ)*I)*γ z.2-β s)) := by
        exact contDiff_const.mul
          (((hcast.mul contDiff_const).cexp.mul (hγsmooth.comp contDiff_snd)).sub contDiff_const)
      simpa only [F,inverseRotation,Function.comp_def,Complex.reCLM_apply] using
        Complex.reCLM.contDiff.comp hC
    apply selected_scalar_root_smooth F hF (Ioo a b) isOpen_Ioo
      (fun t => χ t s) s (4*ε) ?_ ?_ ?_ ?_ θ hθ
    · intro t ht
      exact (hshift t ht s).trans_lt (by linarith)
    · exact fun t ht => hroot t ht s
    · intro t ht
      have hd : HasDerivAt (fun x => F (t,x)) (P t s) (χ t s) := by
        simpa only [F,P,Function.comp_def,Complex.reCLM_apply] using
          Complex.reCLM.hasFDerivAt.comp_hasDerivAt (χ t s)
            (((hγ (χ t s)).const_mul (inverseRotation t)).sub_const (β s)
              |>.const_mul (conj (Tβ s)))
      rw [hd.deriv]
      exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hpositive t ht s))
    · intro t ht x hx heq
      have hd := normal_projection_height_comparison
        (fun u => inverseRotation t*γ u) (fun u => inverseRotation t*γ u)
        β (fun u => inverseRotation t*Tγ u) Tβ k
        (fun u => (hγ u).const_mul (inverseRotation t)) hTβ
        (fun u => by rw [norm_mul,inverse_rotation_norm,huγ u,one_mul]) huβ
        K ε (4*ε) hK hk (htangent t ht) hsmall s x (χ t s)
        hx ((hshift t ht s).trans (by linarith)) heq (hroot t ht s)
      have hz : |x-χ t s| = 0 := le_antisymm
        (by simpa only [sub_self,norm_zero,mul_zero] using hd.1) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
  intro θ hθ s
  let W : ℂ := conj (Tβ s)*(inverseRotation θ*Tγ (χ θ s))
  let Z : ℂ := conj (Tβ s)*β s
  let u : ℝ := deriv (fun t => χ t s) θ
  let g : ℝ := deriv (χ θ) s
  let A : ℝ := 1-k s*h θ s
  have hd : 0<W.re := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hpositive θ hθ s)
  have hg : 0<g := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (hχlower θ hθ s)
  let Q : ℝ → ℂ := fun t => conj (Tβ s)*(inverseRotation t*γ (χ t s)-β s)
  have hχd : HasDerivAt (fun t => χ t s) u θ :=
    ((hparam s θ hθ).differentiableAt (by simp)).hasDerivAt
  have hQraw := (((inverse_rotation_deriv θ).mul
    ((hγ (χ θ s)).scomp θ hχd)).sub_const (β s)).const_mul (conj (Tβ s))
  have hQ : HasDerivAt Q (-I*(Z+I*(h θ s:ℂ))+(u:ℂ)*W) θ := by
    apply hQraw.congr_deriv
    simp only [real_smul,Function.comp_def]
    calc
      _ = -I*(conj (Tβ s)*(inverseRotation θ*γ (χ θ s)))+(u:ℂ)*W := by
        dsimp only [W]
        ring
      _ = _ := by
        rw [hgraphR θ hθ s]
        dsimp only [Z]
        calc
          _ = -I*(conj (Tβ s)*β s+I*(h θ s:ℂ)*(conj (Tβ s)*Tβ s))+(u:ℂ)*W := by ring
          _ = _ := by rw [hself,mul_one]
  have hreQ : (fun t => (Q t).re) =ᶠ[𝓝 θ] fun _ => (0:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact hroot t ht s
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ hQ
  simp only [Function.comp_def,Complex.reCLM_apply] at hreal
  have hconstraint := (hreal.congr_of_eventuallyEq hreQ.symm).unique (hasDerivAt_const θ (0:ℝ))
  have hconstraint' : Z.im+h θ s+u*W.re = 0 := by
    simpa only [Complex.add_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,Complex.mul_im,zero_mul,mul_zero,
      one_mul,mul_one,sub_zero,zero_add,add_zero,neg_zero,neg_neg,neg_one_mul,zero_sub] using hconstraint
  have himag := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ hQ
  simp only [Function.comp_def,Complex.imCLM_apply] at himag
  have hheight : (fun t => (Q t).im) =ᶠ[𝓝 θ] fun t => h t s := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    dsimp only [Q]
    rw [hgraphR t ht s,add_sub_cancel_left]
    have heq : conj (Tβ s)*(I*(h t s:ℂ)*Tβ s) = I*(h t s:ℂ) := by
      calc
        _ = I*(h t s:ℂ)*(conj (Tβ s)*Tβ s) := by ring
        _ = _ := by rw [hself,mul_one]
    rw [heq]
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,one_mul,zero_add]
  have hheightd : HasDerivAt (fun t => h t s) (-Z.re+u*W.im) θ := by
    convert! himag.congr_of_eventuallyEq hheight.symm using 1
    simp only [Complex.add_im,Complex.mul_im,Complex.neg_im,Complex.neg_re,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,Complex.mul_re,zero_mul,mul_zero,
      one_mul,mul_one,sub_zero,zero_add,add_zero,zero_sub]
    ring
  have hχs : HasDerivAt (χ θ) g s := ((hχsmooth θ hθ).differentiable (by simp) s).hasDerivAt
  have hhs : HasDerivAt (h θ) (deriv (h θ) s) s :=
    ((hhsmooth θ hθ).differentiable (by simp) s).hasDerivAt
  have hleft : HasDerivAt (fun v => inverseRotation θ*γ (χ θ v))
      ((g:ℂ)*(inverseRotation θ*Tγ (χ θ s))) s := by
    simpa only [real_smul,mul_left_comm,Function.comp_def] using!
      ((hγ (χ θ s)).scomp s hχs).const_mul (inverseRotation θ)
  have hright := (hβ s).add ((hhs.ofReal_comp.const_mul I).mul (hTβ s))
  have heq : (fun v => inverseRotation θ*γ (χ θ v)) =
      fun v => β v+I*(h θ v:ℂ)*Tβ v := funext (hgraphR θ hθ)
  rw [heq] at hleft
  have hframe := hleft.unique hright
  have hframe' : (g:ℂ)*W = (A:ℂ)+I*((deriv (h θ) s:ℝ):ℂ) := by
    have hc := congrArg (fun z : ℂ => conj (Tβ s)*z) hframe
    dsimp only [W,A]
    simp only [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
    calc
      _ = conj (Tβ s)*((g:ℂ)*(inverseRotation θ*Tγ (χ θ s))) := by ring
      _ = conj (Tβ s)*
          (Tβ s+(I*((deriv (h θ) s:ℝ):ℂ)*Tβ s+I*(h θ s:ℂ)*(I*(k s:ℂ)*Tβ s))) := hc
      _ = (1-(k s:ℂ)*(h θ s:ℂ)+I*((deriv (h θ) s:ℝ):ℂ))*(conj (Tβ s)*Tβ s) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = _ := by rw [hself,mul_one]
  have hA : A = g*W.re := by
    have hc := congrArg Complex.re hframe'
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero] using hc.symm
  have hB : deriv (h θ) s = g*W.im := by
    have hc := congrArg Complex.im hframe'
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,add_zero,zero_add] using hc.symm
  have hApos : 0<A := by rw [hA]; exact mul_pos hg hd
  refine ⟨hApos,hheightd.congr_deriv ?_⟩
  change -Z.re+u*W.im = -(Z.re+(Z.im+h θ s)*deriv (h θ) s/A)
  rw [hA,hB]
  field_simp [ne_of_gt hg,ne_of_gt hd]
  nlinarith only [mul_eq_zero_of_left hconstraint' W.im]

end Lemniscate
