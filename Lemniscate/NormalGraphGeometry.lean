import Lemniscate.BernoulliExpander

/-! Exact geometry of a normal graph over a unit-speed planar curve.

The orientation is n=i*t, with t_s=k*n and n_s=-k*t. The background
position components b+i*eta=conj(t)*beta are derived from the actual frame.
No curvature-variation, support-variation or linearization formula is assumed.
-/
noncomputable section
namespace Lemniscate
open Complex
open scoped ComplexConjugate

def normalGraphCurve (β n : ℝ → ℂ) (h : ℝ → ℝ) (s : ℝ) : ℂ :=
  β s+(h s:ℂ)*n s

private theorem unit_frame_pairing (t z w : ℂ) (ht : ‖t‖ = 1) :
    conj (z*t)*(w*t) = conj z*w := by
  have hunit : conj t*t = 1 := by rw [Complex.conj_mul',ht]; norm_num
  rw [map_mul]
  calc
    (conj z*conj t)*(w*t) = (conj z*w)*(conj t*t) := by ring
    _ = conj z*w := by rw [hunit,mul_one]

private theorem unit_frame_reconstruction (t z : ℂ) (ht : ‖t‖ = 1) :
    ((((conj t*z).re:ℂ)+I*((conj t*z).im:ℂ))*t) = z := by
  have hcoord : (((conj t*z).re:ℂ)+I*((conj t*z).im:ℂ)) = conj t*z := by
    simpa only [mul_comm I] using Complex.re_add_im (conj t*z)
  have hunit : conj t*t = 1 := by rw [Complex.conj_mul',ht]; norm_num
  rw [hcoord]
  calc
    (conj t*z)*t = (conj t*t)*z := by ring
    _ = z := by rw [hunit,one_mul]

private theorem unit_frame_norm (t : ℂ) (a b : ℝ) (ht : ‖t‖ = 1) :
    ‖((a:ℂ)+I*(b:ℂ))*t‖ = Real.sqrt (a^2+b^2) := by
  rw [norm_mul,ht,mul_one,Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,one_mul,sub_zero,
    zero_sub,add_zero,zero_add]
  ring

private theorem unit_frame_cross (t : ℂ) (a b c d : ℝ) (ht : ‖t‖ = 1) :
    (conj (((a:ℂ)+I*(b:ℂ))*t)*(((c:ℂ)+I*(d:ℂ))*t)).im = a*d-b*c := by
  rw [unit_frame_pairing t _ _ ht]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,
    Complex.mul_im,Complex.mul_re,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,one_mul,
    add_zero,zero_add,sub_zero,zero_sub]
  ring

theorem normal_graph_geometry
    (β t n : ℝ → ℂ) (k ks h h₁ h₂ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t ((k s:ℂ)*n s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (hh : ∀ s, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s, HasDerivAt h₁ (h₂ s) s)
    (htunit : ∀ s, ‖t s‖ = 1) (hnormal : ∀ s, n s = I*t s) (s : ℝ) :
    let γ := normalGraphCurve β n h
    let A := 1-k s*h s
    let B := h₁ s
    let g := Real.sqrt (A^2+B^2)
    let b := (conj (t s)*β s).re
    let eta := (conj (t s)*β s).im
    HasDerivAt γ ((A:ℂ)*t s+(B:ℂ)*n s) s ∧
    HasDerivAt (deriv γ)
      (((-ks s*h s-2*k s*h₁ s:ℝ):ℂ)*t s+((k s*A+h₂ s:ℝ):ℂ)*n s) s ∧
    ‖deriv γ s‖ = g ∧
    planarSignedCurvature γ s =
      (k s*A^2+A*h₂ s+ks s*h s*h₁ s+2*k s*(h₁ s)^2)/g^3 ∧
    planarNormalSupport γ s = (A*(eta+h s)-b*h₁ s)/g ∧
    (0 < A → deriv γ s ≠ 0) := by
  let γ := normalGraphCurve β n h
  let A : ℝ → ℝ := fun u => 1-k u*h u
  let B : ℝ → ℝ := h₁
  let C : ℝ → ℝ := fun u => -ks u*h u-2*k u*h₁ u
  let D : ℝ → ℝ := fun u => k u*A u+h₂ u
  let V : ℝ → ℂ := fun u => (A u:ℂ)*t u+(B u:ℂ)*n u
  let W : ℝ → ℂ := fun u => (C u:ℂ)*t u+(D u:ℂ)*n u
  let g := Real.sqrt ((A s)^2+(B s)^2)
  let b := (conj (t s)*β s).re
  let eta := (conj (t s)*β s).im
  have hγ (u : ℝ) : HasDerivAt γ (V u) u := by
    convert! (hβ u).add ((hh u).ofReal_comp.mul (hn u)) using 1 <;>
      dsimp only [γ,normalGraphCurve,V,A,B] <;> push_cast <;> ring
  have hdγ : deriv γ = V := funext fun u => (hγ u).deriv
  have hV (u : ℝ) : HasDerivAt V (W u) u := by
    have hA : HasDerivAt A (-(ks u*h u+k u*h₁ u)) u :=
      ((hk u).mul (hh u)).const_sub 1
    convert! (hA.ofReal_comp.mul (ht u)).add ((hh₁ u).ofReal_comp.mul (hn u)) using 1 <;>
      dsimp only [V,W,A,B,C,D] <;> push_cast <;> ring
  have hγ₂ : HasDerivAt (deriv γ) (W s) s := by rw [hdγ]; exact hV s
  have hVframe : V s = ((A s:ℂ)+I*(B s:ℂ))*t s := by
    dsimp only [V]
    rw [hnormal s]
    ring
  have hWframe : W s = ((C s:ℂ)+I*(D s:ℂ))*t s := by
    dsimp only [W]
    rw [hnormal s]
    ring
  have hspeed : ‖V s‖ = g := by
    rw [hVframe]
    exact unit_frame_norm (t s) (A s) (B s) (htunit s)
  have hcross : (conj (V s)*W s).im =
      k s*(A s)^2+A s*h₂ s+ks s*h s*h₁ s+2*k s*(h₁ s)^2 := by
    rw [hVframe,hWframe,unit_frame_cross (t s) (A s) (B s) (C s) (D s) (htunit s)]
    dsimp only [A,B,C,D]
    ring
  have hβframe : β s = ((b:ℂ)+I*(eta:ℂ))*t s :=
    (unit_frame_reconstruction (t s) (β s) (htunit s)).symm
  have hposition : γ s = ((b:ℂ)+I*((eta+h s:ℝ):ℂ))*t s := by
    dsimp only [γ,normalGraphCurve]
    rw [hβframe,hnormal s]
    push_cast
    ring
  have hsupport : -(conj (γ s)*V s).im = A s*(eta+h s)-b*h₁ s := by
    rw [hposition,hVframe,
      unit_frame_cross (t s) b (eta+h s) (A s) (B s) (htunit s)]
    dsimp only [B]
    ring
  refine ⟨hγ s,hγ₂,?_,?_,?_,?_⟩
  · rw [(hγ s).deriv]
    exact hspeed
  · dsimp only [planarSignedCurvature]
    rw [(hγ s).deriv,hγ₂.deriv,hcross,hspeed]
  · dsimp only [planarNormalSupport]
    rw [(hγ s).deriv]
    change (-(conj (γ s)*V s).im)/‖V s‖ = _
    rw [hsupport,hspeed]
  · intro hA
    apply norm_pos_iff.mp
    rw [(hγ s).deriv,hspeed]
    apply Real.sqrt_pos.mpr
    have hAsq : 0 < (A s)^2 := sq_pos_of_pos hA
    nlinarith only [hAsq,sq_nonneg (B s)]

end Lemniscate
