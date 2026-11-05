import Lemniscate.NormalGraphRotationGeometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-! Equivalence of a rotating normal graph's actual normal velocity
and its scalar height equation, with arbitrary prescribed normal forcing.
The same identity handles geometric flow and rotation of a fixed curve. -/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ComplexConjugate

/-- A unit complex rotation preserves the Hermitian pairing. -/
theorem unit_complex_pairing (R z w : ℂ) (hR : ‖R‖=1) :
    conj (R*z)*(R*w)=conj z*w := by
  have hu : conj R*R=1 := by rw [Complex.conj_mul',hR]; norm_num
  rw [map_mul]
  calc
    _ = (conj R*R)*(conj z*w) := by ring
    _ = _ := by rw [hu,one_mul]

/-- The real normal component is linear in real velocity components. -/
theorem real_normal_pairing_add (a b : ℝ) (z w n : ℂ) :
    (conj ((a:ℂ)*z+(b:ℂ)*w)*n).re=
      a*(conj z*n).re+b*(conj w*n).re := by
  simp only [map_add,map_mul,Complex.conj_ofReal,add_mul,Complex.add_re,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  ring

/-- For the actual rotating graph and its true time derivative within J,
a prescribed normal velocity is equivalent to its scalar height equation
with the geometric rotation term. The normal is formed from the actual
spatial curve; the forcing may in particular be zero. -/
theorem normal_graph_rotating_velocity_equivalence
    (β t n : ℝ → ℂ) (k : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (θ : ℝ → ℝ) (J : Set ℝ) (τ ω : ℝ) (v h₁ F : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖=1) (hN : ∀ s, n s=I*t s)
    (hspace : ∀ s, HasDerivAt (H τ) (h₁ s) s)
    (htime : ∀ s, HasDerivWithinAt (fun z => H z s) (v s) J τ)
    (hθ : HasDerivWithinAt θ ω J τ) (hregular : ∀ s, 0<1-k s*H τ s) :
    let γ := normalGraphCurve β n (H τ)
    let R : ℝ → ℂ := fun z => Complex.exp ((θ z:ℂ)*I)
    let X : ℝ → ℝ → ℂ := fun z s => R z*normalGraphCurve β n (H z) s
    let V : ℝ → ℂ := fun s => R τ*(I*(ω:ℂ)*γ s+(v s:ℂ)*n s)
    (∀ s, deriv γ s≠0 ∧ ‖I*deriv γ s/(‖deriv γ s‖:ℂ)‖=1) ∧
    ∀ s, HasDerivWithinAt (fun z => X z s) (V s) J τ ∧
      ((conj (V s)*(R τ*(I*deriv γ s/(‖deriv γ s‖:ℂ)))).re=
        -F s ↔
        v s+ω*((conj (t s)*β s).re+
          ((conj (t s)*β s).im+H τ s)*h₁ s/(1-k s*H τ s))=
            -(‖deriv γ s‖/(1-k s*H τ s)*F s)) := by
  let γ := normalGraphCurve β n (H τ)
  let R : ℝ → ℂ := fun z => Complex.exp ((θ z:ℂ)*I)
  let X : ℝ → ℝ → ℂ := fun z s => R z*normalGraphCurve β n (H z) s
  let V : ℝ → ℂ := fun s => R τ*(I*(ω:ℂ)*γ s+(v s:ℂ)*n s)
  have hR : ‖R τ‖=1 := Complex.norm_exp_ofReal_mul_I (θ τ)
  have hRd : HasDerivWithinAt R (R τ*(I*(ω:ℂ))) J τ := by
    apply (hθ.ofReal_comp.mul_const I).cexp.congr_deriv
    ring
  have hrotation (s : ℝ) := normal_graph_rotation_height β t n k (H τ) h₁ s
    (hβ s) (hn s) (hspace s) (hu s) (hN s) (hregular s)
  refine ⟨fun s => ⟨(hrotation s).1,(hrotation s).2.1⟩,?_⟩
  intro s
  let A := 1-k s*H τ s
  let g := ‖deriv γ s‖
  let ν := I*deriv γ s/(g:ℂ)
  have hg : g≠0 := norm_ne_zero_iff.mpr (hrotation s).1
  have hA : A≠0 := ne_of_gt (hregular s)
  have hderiv : HasDerivAt γ ((A:ℂ)*t s+(h₁ s:ℂ)*n s) s := by
    convert! (hβ s).add ((hspace s).ofReal_comp.mul (hn s)) using 1
    dsimp only [γ,normalGraphCurve,A]
    push_cast
    ring
  have hself : conj (t s)*t s=1 := by rw [Complex.conj_mul',hu s]; norm_num
  have hnpair : (conj (n s)*ν).re=A/g := by
    dsimp only [ν]
    rw [← mul_div_assoc,Complex.div_ofReal_re,hderiv.deriv,hN s]
    have heq : conj (I*t s)*(I*((A:ℂ)*t s+(h₁ s:ℂ)*(I*t s)))=
        (A:ℂ)+I*(h₁ s:ℂ) := by
      rw [map_mul,Complex.conj_I]
      calc
        _ = ((A:ℂ)+I*(h₁ s:ℂ))*(conj (t s)*t s) := by
          ring_nf
          rw [show (I:ℂ)^3 = -I by rw [pow_succ,Complex.I_sq]; ring,
            Complex.I_sq]
          ring
        _ = _ := by rw [hself,mul_one]
    rw [heq]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero]
  have hrotpair : (conj (I*γ s)*ν).re=
      A/g*((conj (t s)*β s).re+((conj (t s)*β s).im+H τ s)*h₁ s/A) := by
    have he := (hrotation s).2.2
    change (g/A)*(conj (I*γ s)*ν).re=_ at he
    calc
      _ = A/g*((g/A)*(conj (I*γ s)*ν).re) := by field_simp [hg,hA] <;> ring
      _ = _ := congrArg (fun z : ℝ => A/g*z) he
  have hXd : HasDerivWithinAt (fun z => X z s) (V s) J τ := by
    have hh := hRd.mul ((htime s).ofReal_comp.mul_const (n s) |>.const_add (β s))
    apply hh.congr_deriv
    dsimp only [V,γ,normalGraphCurve]
    ring
  refine ⟨hXd,?_⟩
  have hvelocity : (conj (V s)*(R τ*ν)).re=
      A/g*(v s+ω*((conj (t s)*β s).re+
        ((conj (t s)*β s).im+H τ s)*h₁ s/A)) := by
    dsimp only [V]
    rw [unit_complex_pairing _ _ _ hR]
    have hvpair : (conj (I*(ω:ℂ)*γ s+(v s:ℂ)*n s)*ν).re=
        ω*(conj (I*γ s)*ν).re+v s*(conj (n s)*ν).re := by
      rw [show I*(ω:ℂ)*γ s=(ω:ℂ)*(I*γ s) by ring]
      exact real_normal_pairing_add ω (v s) (I*γ s) (n s) ν
    rw [hvpair,hnpair,hrotpair]
    ring
  rw [hvelocity]
  change A/g*(v s+ω*((conj (t s)*β s).re+
      ((conj (t s)*β s).im+H τ s)*h₁ s/A))=
        -F s ↔
    v s+ω*((conj (t s)*β s).re+
      ((conj (t s)*β s).im+H τ s)*h₁ s/A)=
        -(g/A*F s)
  constructor
  · intro hp
    calc
      _ = g/A*(A/g*(v s+ω*((conj (t s)*β s).re+
          ((conj (t s)*β s).im+H τ s)*h₁ s/A))) := by
            field_simp [hg,hA] <;> ring
      _ = g/A*(-F s) :=
        congrArg (fun z : ℝ => g/A*z) hp
      _ = _ := by ring
  · intro hp
    rw [hp]
    field_simp [hg,hA] <;> ring

end Lemniscate
