import Migration.DilationDefect

/-! A polynomial periodic primitive for the projected expander equation.
The following module constructs the frame from actual arclength coordinates. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Adjoint

structure Frame (rate L : ℝ) where
  k : ℝ → ℝ
  v : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  h : ℝ → ℝ
  u : ℝ → ℝ
  n : ℝ → ℝ
  kD (s : ℝ) : HasDerivAt k (v s) s
  vD (s : ℝ) : HasDerivAt v (-(k s)^3/2-rate*p s) s
  pD (s : ℝ) : HasDerivAt p (-k s*q s) s
  qD (s : ℝ) : HasDerivAt q (1+k s*p s) s
  hD (s : ℝ) : HasDerivAt h (u s) s
  uD (s : ℝ) : HasDerivAt u (k s*n s) s
  nD (s : ℝ) : HasDerivAt n (-k s*u s) s
  decompose (s : ℝ) : h s=q s*u s+p s*n s
  periodic (s : ℝ) : k (s+L)=k s ∧ v (s+L)=v s ∧ p (s+L)=p s ∧ q (s+L)=q s ∧
    h (s+L)=h s ∧ u (s+L)=u s ∧ n (s+L)=n s

namespace Frame
variable {rate L : ℝ} (f : Frame rate L)

def weight (R s : ℝ) := (R^2+(f.p s)^2+(f.q s)^2)/2
def stress (s : ℝ) := (f.k s)^2/2*f.u s+f.v s*f.n s
def virial (s : ℝ) := f.v s*f.p s+(f.k s)^2/2*f.q s
def density (R s : ℝ) := rate*R^2+(f.k s)^2/2+2*rate*(f.q s)^2+
  rate*f.k s*f.p s*f.weight R s
def primitive (R s : ℝ) := f.weight R s*(rate*f.q s*f.h s-f.stress s)+
  f.q s*f.k s*f.n s-(1+f.k s*f.p s)*f.u s+f.virial s*f.h s

theorem weightD (R s : ℝ) : HasDerivAt (f.weight R) (f.q s) s := by
  apply (((((f.pD s).pow 2).const_add (R^2)).add ((f.qD s).pow 2)).div_const 2).congr_deriv
  ring

theorem stressD (s : ℝ) : HasDerivAt f.stress (-rate*f.p s*f.n s) s := by
  apply (((((f.kD s).pow 2).div_const 2).mul (f.uD s)).add ((f.vD s).mul (f.nD s))).congr_deriv
  simp only [Pi.pow_apply]
  ring

theorem virialD (s : ℝ) : HasDerivAt f.virial ((f.k s)^2/2-rate*(f.p s)^2) s := by
  apply (((f.vD s).mul (f.pD s)).add ((((f.kD s).pow 2).div_const 2).mul (f.qD s))).congr_deriv
  simp only [Pi.pow_apply]
  ring

theorem primitiveD (R s : ℝ) : HasDerivAt (f.primitive R) (f.density R s*f.h s) s := by
  have hm : HasDerivAt (fun x => rate*f.q x*f.h x-f.stress x)
      (rate*(2+f.k s*f.p s)*f.h s) s := by
    apply ((((f.qD s).const_mul rate).mul (f.hD s)).sub (f.stressD s)).congr_deriv
    rw [f.decompose s]
    ring
  apply (((((f.weightD R s).mul hm).add (((f.qD s).mul (f.kD s)).mul (f.nD s))).sub
    ((((f.kD s).mul (f.pD s)).const_add 1).mul (f.uD s))).add ((f.virialD s).mul (f.hD s))).congr_deriv
  dsimp [density,weight,stress,virial]
  ring

theorem weighted_height_integral (R : ℝ) : (∫ s in 0..L, f.density R s*f.h s)=0 := by
  have hk : Continuous f.k := continuous_iff_continuousAt.mpr (fun s => (f.kD s).continuousAt)
  have hp : Continuous f.p := continuous_iff_continuousAt.mpr (fun s => (f.pD s).continuousAt)
  have hq : Continuous f.q := continuous_iff_continuousAt.mpr (fun s => (f.qD s).continuousAt)
  have hh : Continuous f.h := continuous_iff_continuousAt.mpr (fun s => (f.hD s).continuousAt)
  have hc : Continuous (fun s => f.density R s*f.h s) := by
    dsimp [density,weight]
    fun_prop
  have hd := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
    (fun s _ => f.primitiveD R s) (hc.intervalIntegrable 0 L)
  obtain ⟨hk',hv',hp',hq',hh',hu',hn'⟩ := f.periodic 0
  simp only [zero_add] at hk' hv' hp' hq' hh' hu' hn'
  simpa only [primitive,weight,stress,virial,hk',hv',hp',hq',hh',hu',hn',sub_self] using hd

theorem density_nonneg_bound {R : ℝ} (hr : 0<rate) (hcap : rate*R^4≤2)
    (s : ℝ) (hb : (f.p s)^2+(f.q s)^2≤R^2) : 2*rate*(f.q s)^2 ≤ f.density R s := by
  let w := f.weight R s
  have hw0 : 0≤w := by dsimp [w,weight]; positivity
  have hw : w≤R^2 := by dsimp [w,weight]; linarith
  have hw2 := pow_le_pow_left₀ hw0 hw 2
  have hp : (f.p s)^2≤R^2 := by linarith [sq_nonneg (f.q s)]
  have hprod := mul_le_mul hp hw2 (sq_nonneg w) (sq_nonneg R)
  have hc : rate*(f.p s)^2*w^2≤2*R^2 := by
    have h1 := mul_le_mul_of_nonneg_left hprod hr.le
    have h2 := mul_le_mul_of_nonneg_right hcap (sq_nonneg R)
    nlinarith only [h1,h2]
  have hs := sq_nonneg (f.k s+rate*f.p s*w)
  change _ ≤ rate*R^2+(f.k s)^2/2+2*rate*(f.q s)^2+rate*f.k s*f.p s*w
  nlinarith only [hs,mul_le_mul_of_nonneg_left hc hr.le]

end Frame
end MigrationGeometry.Adjoint
