import LengthGrowth.ActualFlow.FamilyDerivatives
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Rigidity of the affine-force equality system on an open time interval. -/

noncomputable section
open Set
open scoped ContDiff Topology
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.AffineForce

def g (l m y : ℝ) : ℝ := -(y^3)/2+l*y+m
def gp (l y : ℝ) : ℝ := -3*y^2/2+l
def H (l m y : ℝ) : ℝ := l*y^2+m*y
def Hp (l m y : ℝ) : ℝ := 2*l*y+m
def p (l m v y : ℝ) : ℝ := -l*y^3/2-m*y^2+(v-l^2)*y-l*m
def p₁ (l m v y : ℝ) : ℝ := -3*l*y^2/2-2*m*y+v-l^2
def p₂ (l m y : ℝ) : ℝ := -3*l*y-2*m
def firstPoly (l m A y : ℝ) : ℝ := -(y^4)/4+l*y^2+2*m*y+A
def compat (l m v A y : ℝ) : ℝ :=
    (p₂ l m y-Hp l m y)*firstPoly l m A y
    +(p₁ l m v y+2*(v-H l m y))*g l m y-gp l y*p l m v y

private theorem g_deriv (l m y : ℝ) : HasDerivAt (g l m) (gp l y) y := by
  convert! (((((hasDerivAt_id y).pow 3).neg.div_const 2).add
    ((hasDerivAt_id y).const_mul l)).add_const m) using 1
  dsimp [g,gp]
  ring

private theorem H_deriv (l m y : ℝ) : HasDerivAt (H l m) (Hp l m y) y := by
  convert! ((((hasDerivAt_id y).pow 2).const_mul l).add
    ((hasDerivAt_id y).const_mul m)) using 1
  dsimp [H,Hp]
  ring

private theorem p_deriv (l m v y : ℝ) : HasDerivAt (p l m v) (p₁ l m v y) y := by
  convert! (((((((hasDerivAt_id y).pow 3).const_mul (-l)).div_const 2).sub
    (((hasDerivAt_id y).pow 2).const_mul m)).add
    ((hasDerivAt_id y).const_mul (v-l^2))).sub_const (l*m)) using 1
  dsimp [p,p₁]
  ring

private theorem p₁_deriv (l m v y : ℝ) : HasDerivAt (p₁ l m v) (p₂ l m y) y := by
  convert! (((((((hasDerivAt_id y).pow 2).const_mul (-3*l)).div_const 2).sub
    ((hasDerivAt_id y).const_mul (2*m))).add_const v).sub_const (l^2)) using 1
  dsimp [p₁,p₂]
  ring

theorem spatial_first_integral {k : ℝ → ℝ} (l m : ℝ)
    (hk : Differentiable ℝ k) (hk' : Differentiable ℝ (deriv k))
    (hode : ∀ x, deriv (deriv k) x = g l m (k x)) :
    ∃ A, ∀ x, deriv k x ^ 2 = firstPoly l m A (k x) := by
  let e (x : ℝ) := deriv k x ^ 2 + k x ^ 4 / 4 - l * k x ^ 2 - 2*m*k x
  have hd (x : ℝ) : HasDerivAt e 0 x := by
    have hu := (hk' x).hasDerivAt
    rw [hode x] at hu
    have h := (((hu.pow 2).add (((hk x).hasDerivAt.pow 4).div_const 4)).sub
      (((hk x).hasDerivAt.pow 2).const_mul l)).sub ((hk x).hasDerivAt.const_mul (2*m))
    convert! h using 1
    dsimp [g]
    ring
  refine ⟨e 0, fun x => ?_⟩
  have h := is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt)
    (fun z => (hd z).deriv) x 0
  dsimp only [firstPoly]
  change deriv k x^2 + k x^4/4-l*k x^2-2*m*k x = e 0 at h
  linarith

private theorem expanded (l m v A y : ℝ) :
    compat l m v A y =
      9*l/4*y^5 + 5*m/4*y^4 -9*l^2*y^3
      -21*l*m*y^2 + (-5*l*A-10*m^2+2*l*v)*y
      -3*m*A+3*m*v := by
  dsimp [compat, firstPoly, p₂, Hp, p₁, H, g, gp, p]
  ring

/-- Six points of a nondegenerate interval detect the degree-five term. -/
theorem constant_of_compat_polynomial {k : ℝ → ℝ} {l m v A : ℝ}
    (hl : l ≠ 0) (hk : Continuous k) (h : ∀ x, compat l m v A (k x) = 0)
    (u z : ℝ) : k u = k z := by
  have noLt (a b : ℝ) (hab : k a < k b) : False := by
    let d := (k b-k a)/5
    have hd : 0 < d := by dsimp [d]; linarith
    have hzero (n : ℝ) (hn : 0 ≤ n) (hn' : n ≤ 5) :
        compat l m v A (k a+n*d)=0 := by
      have hv : k a+n*d ∈ Icc (k a) (k b) := by
        constructor
        · nlinarith [mul_nonneg hn hd.le]
        · have heq : k a+5*d=k b := by dsimp [d]; ring
          nlinarith [mul_nonneg (sub_nonneg.mpr hn') hd.le]
      obtain ⟨x,hx⟩ := intermediate_value_univ a b hk hv
      exact hx ▸ h x
    have h0 := hzero 0 (by norm_num) (by norm_num)
    have h1 := hzero 1 (by norm_num) (by norm_num)
    have h2 := hzero 2 (by norm_num) (by norm_num)
    have h3 := hzero 3 (by norm_num) (by norm_num)
    have h4 := hzero 4 (by norm_num) (by norm_num)
    have h5 := hzero 5 (by norm_num) (by norm_num)
    have hdiff : 270*l*d^5 = 0 := by
      rw [expanded] at h0 h1 h2 h3 h4 h5
      linear_combination h5-5*h4+10*h3-10*h2+5*h1-h0
    exact (mul_ne_zero (mul_ne_zero (by norm_num) hl) (pow_ne_zero 5 hd.ne')) hdiff
  exact le_antisymm (le_of_not_gt (fun hlt => noLt z u hlt))
    (le_of_not_gt (fun hlt => noLt u z hlt))

/-- The normalized time evolution and its spatial oscillator force every
curvature slice on an open time interval to be spatially constant. -/
theorem spatially_constant_on_time_interval
    {I : Set ℝ} {K w : ℝ → ℝ → ℝ} {l m v : ℝ} (hl : l ≠ 0)
    (hI : IsOpen I)
    (hK : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => K z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (hw : ∀ t ∈ I, Differentiable ℝ (w t))
    (osc : ∀ t ∈ I, ∀ x, deriv (deriv (K t)) x = g l m (K t x))
    (gauge : ∀ t ∈ I, ∀ x, deriv (w t) x = v-H l m (K t x))
    (evol : ∀ t ∈ I, ∀ x, deriv (fun s => K s x) t =
      p l m v (K t x)+w t x*deriv (K t) x)
    {t : ℝ} (ht : t ∈ I) (a b : ℝ) : K t a = K t b := by
  let k := K t
  have hslice := joint_smooth_space_slice hK ht
  have hk : Differentiable ℝ k := hslice.differentiable (by simp)
  have hk' : Differentiable ℝ (deriv k) :=
    (joint_smooth_space_slice (f := fun s => deriv (K s)) (joint_smooth_deriv_space hI hK)
      ht).differentiable (by simp)
  have hks (x : ℝ) : HasDerivAt (deriv k) (g l m (k x)) x := by
    rw [← osc t ht x]
    exact (hk' x).hasDerivAt
  have hws (x : ℝ) : HasDerivAt (w t) (v-H l m (k x)) x := by
    rw [← gauge t ht x]
    exact (hw t ht x).hasDerivAt
  obtain ⟨A,hA⟩ := spatial_first_integral l m hk hk' (osc t ht)
  apply constant_of_compat_polynomial (k := k) (l := l) (m := m) (v := v) (A := A)
    hl hk.continuous _ a b
  intro x
  have mixed (y : ℝ) : deriv (fun s => deriv (deriv (K s)) y) t =
      deriv (deriv (fun z => deriv (fun s => K s z) t)) y := by
    rw [actual_time_space_deriv_commute (f := fun s => deriv (K s)) hI
      (joint_smooth_deriv_space hI hK) ht y]
    congr 1
    funext z
    exact actual_time_space_deriv_commute hI hK ht z
  have gt : deriv (fun s => deriv (deriv (K s)) x) t =
      gp l (k x)*(p l m v (k x)+w t x*deriv k x) := by
    calc
      _ = deriv (fun s => g l m (K s x)) t := by
        apply Filter.EventuallyEq.deriv_eq
        filter_upwards [hI.mem_nhds ht] with s hs
        exact osc s hs x
      _ = _ := by
        have h := ((g_deriv l m (K t x)).comp t (joint_smooth_time_hasDerivAt hI hK ht x)).deriv
        rw [evol t ht x] at h
        exact h
  let P (y : ℝ) := p₁ l m v (k y)*deriv k y +
    ((v-H l m (k y))*deriv k y+w t y*g l m (k y))
  have first : deriv (fun z => deriv (fun s => K s z) t) = P := by
    have he : (fun z => deriv (fun s => K s z) t) =
        fun z => p l m v (k z)+w t z*deriv k z := funext (evol t ht)
    rw [he]
    funext y
    exact (((p_deriv l m v (k y)).comp y (hk y).hasDerivAt).add
      ((hws y).mul (hks y))).deriv
  have hx := (hk x).hasDerivAt
  have sp := (((p₁_deriv l m v (k x)).comp x hx).mul (hks x)).add
    (((((H_deriv l m (k x)).comp x hx).const_sub v).mul (hks x)).add
      ((hws x).mul ((g_deriv l m (k x)).comp x hx)))
  have h2 := mixed x
  rw [gt,first] at h2
  have identity := h2.trans sp.deriv
  simp only [Function.comp_apply] at identity
  dsimp only [compat]
  rw [← hA x]
  linear_combination -identity

/-- The affine-force equation, periodic-gauge derivative, and divergence-form
curvature evolution imply rigidity without a polynomial constraint hypothesis. -/
theorem spatially_constant_of_affine_force_evolution
    {I : Set ℝ} {K w : ℝ → ℝ → ℝ} {l m v : ℝ} (hl : l ≠ 0)
    (hI : IsOpen I)
    (hK : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => K z.1 z.2) (I ×ˢ (univ : Set ℝ)))
    (hw : ∀ t ∈ I, Differentiable ℝ (w t))
    (force : ∀ t ∈ I, ∀ x, deriv (deriv (K t)) x+(K t x)^3/2=l*K t x+m)
    (gauge : ∀ t ∈ I, ∀ x, deriv (w t) x = v-K t x*(l*K t x+m))
    (evol : ∀ t ∈ I, ∀ x, deriv (fun s => K s x) t =
      -l*deriv (deriv (K t)) x+deriv (fun y => K t y*w t y) x)
    {t : ℝ} (ht : t ∈ I) (a b : ℝ) : K t a = K t b := by
  have osc (r : ℝ) (hr : r ∈ I) (x : ℝ) : deriv (deriv (K r)) x = g l m (K r x) := by
    dsimp only [g]
    linarith [force r hr x]
  apply spatially_constant_on_time_interval (v := v) hl hI hK hw osc _ _ ht a b
  · intro r hr x
    rw [gauge r hr x]
    dsimp only [H]
    ring
  · intro r hr x
    have hk := ((joint_smooth_space_slice hK hr).differentiable (by simp) x).hasDerivAt
    have hprod : deriv (fun y => K r y*w r y) x =
        deriv (K r) x*w r x+K r x*deriv (w r) x := (hk.mul (hw r hr x).hasDerivAt).deriv
    rw [evol r hr x,hprod,osc r hr x,gauge r hr x]
    dsimp only [g,p]
    ring

#print axioms spatial_first_integral
#print axioms constant_of_compat_polynomial
#print axioms spatially_constant_on_time_interval
#print axioms spatially_constant_of_affine_force_evolution
end LengthGrowth.ActualFlow.AffineForce
