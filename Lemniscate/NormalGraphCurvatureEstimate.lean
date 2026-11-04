import Lemniscate.NormalGraphGeometry
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! A pointwise curvature estimate for the actual normal projection.
Only C2 regularity of the parameter and height is used. The second
derivative of the parameter cancels in the signed-curvature determinant.
-/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate

private theorem unit_speed_reparametrization
    (γ T : ℝ → ℂ) (k χ : ℝ → ℝ)
    (hγ : ∀ s, HasDerivAt γ (T s) s)
    (hT : ∀ s, HasDerivAt T (I*(k s:ℂ)*T s) s)
    (hu : ∀ s, ‖T s‖ = 1) (hχ : ContDiff ℝ 2 χ)
    (s : ℝ) (hg : 0 < deriv χ s) :
    HasDerivAt (γ ∘ χ) (((deriv χ s:ℝ):ℂ)*T (χ s)) s ∧
      ‖deriv (γ ∘ χ) s‖ = deriv χ s ∧
      planarSignedCurvature (γ ∘ χ) s = k (χ s) := by
  let g := deriv χ
  let g₁ := deriv g
  have hχd (u : ℝ) : HasDerivAt χ (g u) u :=
    (hχ.differentiable (by norm_num) u).hasDerivAt
  have hgd (u : ℝ) : HasDerivAt g (g₁ u) u :=
    (hχ.differentiable_deriv_two u).hasDerivAt
  have hfirst (u : ℝ) : HasDerivAt (γ ∘ χ) ((g u:ℂ)*T (χ u)) u := by
    simpa only [real_smul] using! (hγ (χ u)).scomp u (hχd u)
  have hderiv : deriv (γ ∘ χ) = fun u => (g u:ℂ)*T (χ u) :=
    funext fun u => (hfirst u).deriv
  have hsecond : HasDerivAt (deriv (γ ∘ χ))
      ((g₁ s:ℂ)*T (χ s)+(g s:ℂ)^2*(I*(k (χ s):ℂ)*T (χ s))) s := by
    rw [hderiv]
    convert! (hgd s).ofReal_comp.mul ((hT (χ s)).scomp s (hχd s)) using 1
    simp only [real_smul,Function.comp_def]
    ring
  have hspeed : ‖deriv (γ ∘ χ) s‖ = g s := by
    rw [(hfirst s).deriv,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hg,hu,mul_one]
  have hunit : conj (T (χ s))*T (χ s) = 1 := by
    rw [Complex.conj_mul',hu]
    norm_num
  have hcross :
      (conj ((g s:ℂ)*T (χ s))*
        ((g₁ s:ℂ)*T (χ s)+(g s:ℂ)^2*(I*(k (χ s):ℂ)*T (χ s)))).im =
      k (χ s)*(g s)^3 := by
    have hc : conj ((g s:ℂ)*T (χ s))*
        ((g₁ s:ℂ)*T (χ s)+(g s:ℂ)^2*(I*(k (χ s):ℂ)*T (χ s))) =
        ((g s:ℂ)*(g₁ s:ℂ)+I*(k (χ s):ℂ)*(g s:ℂ)^3)*
          (conj (T (χ s))*T (χ s)) := by
      simp only [map_mul,Complex.conj_ofReal]
      ring
    rw [hc,hunit,mul_one]
    have heq : (g s:ℂ)*(g₁ s:ℂ)+I*(k (χ s):ℂ)*(g s:ℂ)^3 =
        ((g s*g₁ s:ℝ):ℂ)+I*((k (χ s)*(g s)^3:ℝ):ℂ) := by
      push_cast
      ring
    rw [heq]
    simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,one_mul,zero_add,add_zero]
  refine ⟨hfirst s,hspeed,?_⟩
  change (conj (deriv (γ ∘ χ) s)*deriv (deriv (γ ∘ χ)) s).im/
    ‖deriv (γ ∘ χ) s‖^3 = k (χ s)
  rw [hspeed,(hfirst s).deriv,hsecond.deriv,hcross]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 3 (ne_of_gt hg))

private theorem normal_graph_curvature_identity
    (γ β Tγ Tβ : ℝ → ℂ) (kγ k ks χ h : ℝ → ℝ)
    (hγ : ∀ s, HasDerivAt γ (Tγ s) s)
    (hTγ : ∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (huγ : ∀ s, ‖Tγ s‖ = 1) (huβ : ∀ s, ‖Tβ s‖ = 1)
    (hχ : ContDiff ℝ 2 χ) (hh : ContDiff ℝ 2 h)
    (hgraph : ∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s)
    (s : ℝ) (hg : 0 < deriv χ s) :
    let A := 1-k s*h s
    let B := deriv h s
    let g := deriv χ s
    (g:ℂ)*Tγ (χ s) = ((A:ℂ)+I*(B:ℂ))*Tβ s ∧
      A*deriv (deriv h) s = kγ (χ s)*g^3-k s*A^2-
        ks s*h s*B-2*k s*B^2 := by
  let n : ℝ → ℂ := fun u => I*Tβ u
  have ht (u : ℝ) : HasDerivAt Tβ ((k u:ℂ)*n u) u := by
    convert! hTβ u using 1 <;> dsimp only [n] <;> ring
  have hn (u : ℝ) : HasDerivAt n (-(k u:ℂ)*Tβ u) u := by
    convert! (hTβ u).const_mul I using 1
    ring_nf
    rw [Complex.I_sq]
    ring
  have hh₁ (u : ℝ) : HasDerivAt h (deriv h u) u :=
    (hh.differentiable (by norm_num) u).hasDerivAt
  have hh₂ (u : ℝ) : HasDerivAt (deriv h) (deriv (deriv h) u) u :=
    (hh.differentiable_deriv_two u).hasDerivAt
  have hgeo := normal_graph_geometry β Tβ n k ks h (deriv h) (deriv (deriv h))
    hβ ht hn hk hh₁ hh₂ huβ (fun _ => rfl) s
  dsimp only at hgeo
  have hcomp : γ ∘ χ = normalGraphCurve β n h := by
    funext u
    change γ (χ u) = _
    rw [hgraph]
    dsimp only [normalGraphCurve,n]
    ring
  have hparam := unit_speed_reparametrization γ Tγ kγ χ hγ hTγ huγ hχ s hg
  have hframe : ((deriv χ s:ℝ):ℂ)*Tγ (χ s) =
      (((1-k s*h s:ℝ):ℂ)+I*((deriv h s:ℝ):ℂ))*Tβ s := by
    calc
      _ = deriv (γ ∘ χ) s := hparam.1.deriv.symm
      _ = deriv (normalGraphCurve β n h) s := congrArg (fun F => deriv F s) hcomp
      _ = _ := by rw [hgeo.1.deriv]; dsimp only [n]; ring
  have hspeed : deriv χ s = Real.sqrt ((1-k s*h s)^2+(deriv h s)^2) :=
    hparam.2.1.symm.trans ((congrArg (fun F => ‖deriv F s‖) hcomp).trans hgeo.2.2.1)
  have hc : kγ (χ s) =
      (k s*(1-k s*h s)^2+(1-k s*h s)*deriv (deriv h) s+
        ks s*h s*deriv h s+2*k s*(deriv h s)^2)/(deriv χ s)^3 := by
    calc
      _ = planarSignedCurvature (γ ∘ χ) s := hparam.2.2.symm
      _ = planarSignedCurvature (normalGraphCurve β n h) s :=
        congrArg (fun F => planarSignedCurvature F s) hcomp
      _ = _ := by rw [hgeo.2.2.2.1,← hspeed]
  refine ⟨hframe,?_⟩
  have hnum := (eq_div_iff (pow_ne_zero 3 (ne_of_gt hg))).mp hc
  linear_combination -hnum

private theorem abs_six_terms (x y z u v w : ℝ) :
    |x+y+z-u-v-w| ≤ |x|+|y|+|z|+|u|+|v|+|w| := by
  calc
    _ ≤ |x+y+z-u-v|+|w| := abs_sub _ _
    _ ≤ (|x+y+z-u|+|v|)+|w| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ ((|x+y+z|+|u|)+|v|)+|w| := add_le_add
      (add_le_add (abs_sub _ _) le_rfl) le_rfl
    _ ≤ (((|x+y|+|z|)+|u|)+|v|)+|w| := add_le_add
      (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add
      (abs_add_le _ _) le_rfl) le_rfl) le_rfl) le_rfl

private theorem scalar_curvature_height_bound
    (K K₁ B H δ A g k ks h b h₂ kc kt : ℝ)
    (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hA : (1/4:ℝ) ≤ A) (hA₂ : A ≤ 2)
    (hg : 0 ≤ g) (hg₄ : g ≤ 4)
    (hg₁ : |g-1| ≤ H*δ) (hA₁ : |A-1| ≤ 3*K*δ)
    (hk : |k| ≤ K) (hks : |ks| ≤ K₁)
    (hh : |h| ≤ 3*δ) (hb : |b| ≤ B*δ)
    (hshift : |kt-k| ≤ 2*K₁*δ)
    (hid : A*h₂ = kc*g^3-k*A^2-ks*h*b-2*k*b^2) :
    let Q := 128*K₁+K*(21*H+9*K)+3*K₁*B+2*K*B^2
    |h₂| ≤ 4*(64+Q+1)*(|kc-kt|+δ) := by
  let Q := 128*K₁+K*(21*H+9*K)+3*K₁*B+2*K*B^2
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hδsq : δ^2 ≤ δ := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
  have hg₂ : g^2 ≤ 16 := by nlinarith only [mul_self_le_mul_self hg hg₄]
  have hg₃ : |g^3| ≤ 64 := by
    rw [abs_of_nonneg (pow_nonneg hg 3),pow_succ]
    exact (mul_le_mul hg₂ hg₄ hg (by norm_num)).trans_eq (by norm_num)
  have hgFactor : 0 ≤ g^2+g+1 := by positivity
  have hgFactor₂ : g^2+g+1 ≤ 21 := by linarith
  have hgcube : |g^3-1| ≤ 21*H*δ := by
    have heq : g^3-1 = (g-1)*(g^2+g+1) := by ring
    rw [heq,abs_mul,abs_of_nonneg hgFactor]
    exact (mul_le_mul hg₁ hgFactor₂ hgFactor (mul_nonneg hH hδ)).trans_eq (by ring)
  have hA₀ : 0 ≤ A := le_trans (by norm_num) hA
  have hAFactor : |A+1| ≤ 3 := by rw [abs_of_nonneg (by positivity)]; linarith
  have hAsq : |A^2-1| ≤ 9*K*δ := by
    have heq : A^2-1 = (A-1)*(A+1) := by ring
    rw [heq,abs_mul]
    exact (mul_le_mul hA₁ hAFactor (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hterm₁ : |(kc-kt)*g^3| ≤ 64*|kc-kt| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hg₃ (abs_nonneg _)).trans_eq (by ring)
  have hterm₂ : |(kt-k)*g^3| ≤ (128*K₁)*δ := by
    rw [abs_mul]
    exact (mul_le_mul hshift hg₃ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hterm₃ : |k*(g^3-1)| ≤ (21*K*H)*δ := by
    rw [abs_mul]
    exact (mul_le_mul hk hgcube (abs_nonneg _) hK).trans_eq (by ring)
  have hterm₄ : |k*(A^2-1)| ≤ (9*K^2)*δ := by
    rw [abs_mul]
    exact (mul_le_mul hk hAsq (abs_nonneg _) hK).trans_eq (by ring)
  have hterm₅ : |ks*h*b| ≤ (3*K₁*B)*δ := by
    have ht : |ks*h*b| ≤ K₁*(3*δ)*(B*δ) := by
      simp only [abs_mul]
      exact mul_le_mul (mul_le_mul hks hh (abs_nonneg _) hK₁) hb
        (abs_nonneg _) (by positivity)
    calc
      _ ≤ (3*K₁*B)*δ^2 := ht.trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left hδsq (by positivity)
  have hb₂ : |b|^2 ≤ (B*δ)^2 := by nlinarith only [mul_self_le_mul_self (abs_nonneg b) hb]
  have hterm₆ : |2*k*b^2| ≤ (2*K*B^2)*δ := by
    have ht : |2*k*b^2| ≤ (2*K)*(B*δ)^2 := by
      rw [abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2),abs_pow]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hb₂
        (sq_nonneg _) (by positivity)
    calc
      _ ≤ (2*K*B^2)*δ^2 := ht.trans_eq (by ring)
      _ ≤ _ := mul_le_mul_of_nonneg_left hδsq (by positivity)
  have hnum : |A*h₂| ≤ 64*|kc-kt|+Q*δ := by
    have heq : kc*g^3-k*A^2-ks*h*b-2*k*b^2 =
        (kc-kt)*g^3+(kt-k)*g^3+k*(g^3-1)-k*(A^2-1)-ks*h*b-2*k*b^2 := by ring
    calc
      _ ≤ |(kc-kt)*g^3|+|(kt-k)*g^3|+|k*(g^3-1)|+
          |k*(A^2-1)|+|ks*h*b|+|2*k*b^2| := by rw [hid,heq]; exact abs_six_terms _ _ _ _ _ _
      _ ≤ 64*|kc-kt|+(128*K₁)*δ+(21*K*H)*δ+(9*K^2)*δ+
          (3*K₁*B)*δ+(2*K*B^2)*δ := add_le_add
        (add_le_add (add_le_add (add_le_add (add_le_add hterm₁ hterm₂) hterm₃) hterm₄) hterm₅) hterm₆
      _ = _ := by dsimp only [Q]; ring
  have hscale : |h₂| ≤ 4*|A*h₂| := by
    rw [abs_mul,abs_of_nonneg hA₀]
    nlinarith only [mul_le_mul_of_nonneg_right hA (abs_nonneg h₂)]
  calc
    _ ≤ 4*(64*|kc-kt|+Q*δ) := hscale.trans
      (mul_le_mul_of_nonneg_left hnum (by norm_num))
    _ ≤ _ := by
      have hrem : 0 ≤ 4*((Q+1)*|kc-kt|+65*δ) := by positivity
      nlinarith only [hrem]

/-- The second derivative of the projected normal height is controlled by
the curvature difference and the C1 projection error. The constant is
chosen from the reference curvature bounds before the nearby curve and
the projection error are specified. -/
theorem normal_graph_curvature_estimate
    (β Tβ : ℝ → ℂ) (k ks : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s) (huβ : ∀ s, ‖Tβ s‖ = 1)
    (K K₁ : ℝ) (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hcurvature : ∀ s, |k s| ≤ K) (hcurvatureDerivative : ∀ s, |ks s| ≤ K₁) :
    ∃ C > 0, ∀ (γ Tγ : ℝ → ℂ) (kγ χ h : ℝ → ℝ) (δ : ℝ),
      (∀ s, HasDerivAt γ (Tγ s) s) →
      (∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s) →
      (∀ s, ‖Tγ s‖ = 1) → ContDiff ℝ 2 χ → ContDiff ℝ 2 h →
      (∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s) →
      0 < δ → δ+2*K*δ < 1/2 →
      (∀ s, |h s| ≤ 3*δ) →
      (∀ s, |deriv h s| ≤ 4*(δ+2*K*δ)) →
      (∀ s, |χ s-s| ≤ 2*δ) →
      (∀ s, (1/4:ℝ) ≤ deriv χ s ∧ deriv χ s ≤ 4) →
      ∀ s, |deriv (deriv h) s| ≤ C*(|kγ (χ s)-k (χ s)|+δ) := by
  let B : ℝ := 4*(1+2*K)
  let H : ℝ := 3*K+B
  let Q : ℝ := 128*K₁+K*(21*H+9*K)+3*K₁*B+2*K*B^2
  let C : ℝ := 4*(64+Q+1)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hklip (a b : ℝ) : |k b-k a| ≤ K₁*|b-a| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := K₁)
        (fun x _ => (hk x).hasDerivWithinAt)
        (fun x _ => by simpa only [Real.norm_eq_abs] using hcurvatureDerivative x)
        convex_univ (mem_univ a) (mem_univ b)
  refine ⟨C,hC,?_⟩
  intro γ Tγ kγ χ h δ hγ hTγ huγ hχ hh hgraph hδ hsmall hhsmall hbsmall hχsmall hχbounds s
  let A : ℝ := 1-k s*h s
  let b : ℝ := deriv h s
  let g : ℝ := deriv χ s
  have hgpos : 0 < g := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) (hχbounds s).1
  have hgeo := normal_graph_curvature_identity γ β Tγ Tβ kγ k ks χ h
    hγ hTγ hβ hTβ hk huγ huβ hχ hh hgraph s hgpos
  have hkh : |k s*h s| ≤ 3*K*δ := by
    rw [abs_mul]
    exact (mul_le_mul (hcurvature s) (hhsmall s) (abs_nonneg _) hK).trans_eq (by ring)
  have hKd : K*δ < 1/4 := by nlinarith only [hsmall,hδ]
  have hδ₁ : δ ≤ 1 := by nlinarith only [hsmall,mul_nonneg hK hδ.le]
  have hA : (1/4:ℝ) ≤ A := by
    dsimp only [A]
    nlinarith only [(abs_le.mp hkh).2,hKd]
  have hA₂ : A ≤ 2 := by
    dsimp only [A]
    nlinarith only [(abs_le.mp hkh).1,hKd]
  have hA₁ : |A-1| ≤ 3*K*δ := by
    have heq : A-1 = -(k s*h s) := by dsimp only [A]; ring
    rw [heq,abs_neg]
    exact hkh
  have hb : |b| ≤ B*δ := (hbsmall s).trans_eq (by dsimp only [B]; ring)
  have hframe : (g:ℂ)*Tγ (χ s) = ((A:ℂ)+I*(b:ℂ))*Tβ s := hgeo.1
  have hnorm : g = ‖(A:ℂ)+I*(b:ℂ)‖ := by
    calc
      _ = ‖(g:ℂ)*Tγ (χ s)‖ := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hgpos,huγ,mul_one]
      _ = ‖((A:ℂ)+I*(b:ℂ))*Tβ s‖ := congrArg norm hframe
      _ = _ := by rw [norm_mul,huβ,mul_one]
  have hg₁ : |g-1| ≤ H*δ := by
    have heq : (A:ℂ)+I*(b:ℂ)-1 = ((A-1:ℝ):ℂ)+I*(b:ℂ) := by push_cast; ring
    calc
      _ = |‖(A:ℂ)+I*(b:ℂ)‖-‖(1:ℂ)‖| := by rw [hnorm,norm_one]
      _ ≤ ‖(A:ℂ)+I*(b:ℂ)-1‖ := abs_norm_sub_norm_le _ _
      _ ≤ |A-1|+|b| := by
        rw [heq]
        exact (norm_add_le _ _).trans_eq (by
          rw [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,
            Complex.norm_real,Real.norm_eq_abs,one_mul])
      _ ≤ 3*K*δ+B*δ := add_le_add hA₁ hb
      _ = _ := by dsimp only [H]; ring
  have hshift : |k (χ s)-k s| ≤ 2*K₁*δ :=
    (hklip s (χ s)).trans ((mul_le_mul_of_nonneg_left (hχsmall s) hK₁).trans_eq (by ring))
  have he := scalar_curvature_height_bound K K₁ B H δ A g (k s) (ks s) (h s) b
    (deriv (deriv h) s) (kγ (χ s)) (k (χ s))
    hK hK₁ hB hH hδ.le hδ₁ hA hA₂ hgpos.le (hχbounds s).2 hg₁ hA₁
    (hcurvature s) (hcurvatureDerivative s) (hhsmall s) hb hshift hgeo.2
  simpa only [C,Q] using he

end Lemniscate
