import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Uniform scalar implicit roots on an open parameter set. The scalar
contraction supplies the same selected root used by the local implicit
function theorem; the parameters need no global extension or cutoff. -/
noncomputable section
namespace Lemniscate
open Filter Set Function
open scoped Topology ContDiff NNReal

private theorem scalar_map_invertible (d : ℝ) (hd : d ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ d).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := ContinuousLinearMap.toSpanSingleton ℝ d⁻¹)
  · ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp
  · ext x
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul]
    field_simp

/-- A uniform contraction in the scalar variable gives a unique root
strictly inside the scalar interval, with the same nonzero regularity
order as the equation on the open parameter set. Only an open scalar
domain containing the closed contraction interval is required.
Its size is bounded by twice the residual at zero, allowing continuous
identification with a zero-displacement root at a boundary parameter. -/
theorem uniform_scalar_implicit_root
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    (n : ℕ∞ω) (hn : n ≠ 0) (U : Set P) (hU : IsOpen U)
    (V : Set ℝ) (hV : IsOpen V) (f : P × ℝ → ℝ)
    (hf : ContDiffOn ℝ n f (U ×ˢ V))
    (r : ℝ) (hr : 0 < r) (hrV : Metric.closedBall (0:ℝ) r ⊆ V)
    (c : ℝ≥0) (hc : (c:ℝ) < 1/2)
    (hzero : ∀ p ∈ U, |f (p,0)| ≤ r/2)
    (hderiv : ∀ p ∈ U, ∀ x : ℝ, |x| ≤ r →
      |1-deriv (fun y => f (p,y)) x| ≤ c) :
    ∃ ξ : P → ℝ, ContDiffOn ℝ n ξ U ∧
      (∀ p ∈ U, |ξ p| < r ∧ f (p,ξ p) = 0 ∧ |ξ p| ≤ 2*|f (p,0)|) ∧
      ∀ p ∈ U, ∀ x : ℝ, |x| ≤ r → f (p,x) = 0 → x = ξ p := by
  classical
  have hfAt (p : P) (hp : p ∈ U) (x : ℝ) (hx : x ∈ V) :
      ContDiffAt ℝ n f (p,x) := hf.contDiffAt ((hU.prod hV).mem_nhds ⟨hp,hx⟩)
  let F : P → ℝ → ℝ := fun p x => x-f (p,x)
  let Ball := Metric.closedBall (0:ℝ) r
  have hzeroBall : (0:ℝ) ∈ Ball := by simp [Ball,hr.le]
  have hp (p : U) (x : ℝ) (hx : x ∈ Ball) : HasDerivAt (fun y => f ((p:P),y))
      (deriv (fun y => f ((p:P),y)) x) x :=
    (((hfAt p p.property x (hrV hx)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt hn).hasDerivAt
  have hFd (p : U) (x : ℝ) (hx : x ∈ Ball) : HasDerivAt (F p)
      (1-deriv (fun y => f ((p:P),y)) x) x := (hasDerivAt_id x).sub (hp p x hx)
  have hLip (p : U) : LipschitzOnWith c (F p) Ball := by
    apply (convex_closedBall (0:ℝ) r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hFd p x hx).hasDerivWithinAt)
    intro x hx
    have hx' : |x| ≤ r := by simpa [Ball,Real.dist_eq] using hx
    have hb : ‖1-deriv (fun y => f ((p:P),y)) x‖ ≤ (c:ℝ) := by
      simpa only [Real.norm_eq_abs] using hderiv p p.property x hx'
    exact_mod_cast hb
  have hstrict (p : U) (x : ℝ) (hx : x ∈ Ball) : |F p x| < r := by
    have hx' : |x| ≤ r := by simpa [Ball,Real.dist_eq] using hx
    have hl : |F p x-F p 0| ≤ (c:ℝ)*|x| := by
      simpa only [Real.dist_eq,sub_zero] using (hLip p).dist_le_mul x hx 0 hzeroBall
    have hz : |F p 0| ≤ r/2 := by simpa [F] using hzero p p.property
    have ht : |F p x| ≤ |F p x-F p 0|+|F p 0| := by
      simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add (F p x) (F p 0)
    have hc0 : (0:ℝ) ≤ c := c.property
    have hcr := mul_lt_mul_of_pos_right hc hr
    have hcx := mul_le_mul_of_nonneg_left hx' hc0
    linarith
  let G : U → Ball → Ball := fun p x =>
    ⟨F p x,by simpa [Ball,Real.dist_eq] using (hstrict p x x.property).le⟩
  have hG (p : U) : ContractingWith c (G p) := by
    refine ⟨by exact_mod_cast (hc.trans (by norm_num : (1/2:ℝ) < 1)),?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hLip p).dist_le_mul x x.property y y.property
  letI : Nonempty Ball := ⟨⟨0,hzeroBall⟩⟩
  let ξU : U → ℝ := fun p => ((hG p).fixedPoint (G p)).val
  have hfix (p : U) : F p (ξU p) = ξU p :=
    congrArg Subtype.val (hG p).fixedPoint_isFixedPt
  have hroot (p : U) : |ξU p| < r ∧ f ((p:P),ξU p) = 0 := by
    have hb := ((hG p).fixedPoint (G p)).property
    have hs := hstrict p (ξU p) hb
    rw [hfix p] at hs
    exact ⟨hs,by have heq := hfix p; dsimp only [F] at heq; linarith⟩
  have huniq (p : U) (x : ℝ) (hx : |x| ≤ r) (heq : f ((p:P),x) = 0) : x = ξU p := by
    let y : Ball := ⟨x,by simpa [Ball,Real.dist_eq] using hx⟩
    have hy : IsFixedPt (G p) y := by
      apply Subtype.ext
      change x-f ((p:P),x) = x
      rw [heq,sub_zero]
    exact congrArg Subtype.val ((hG p).fixedPoint_unique hy)
  have hbound (p : U) : |ξU p| ≤ 2*|f ((p:P),0)| := by
    have hb := ((hG p).fixedPoint (G p)).property
    have hl := (hLip p).dist_le_mul (ξU p) hb 0 hzeroBall
    simp only [Real.dist_eq,sub_zero,hfix p] at hl
    have hz : |F p 0| = |f ((p:P),0)| := by simp [F]
    have ht := norm_le_norm_sub_add (ξU p) (F p 0)
    simp only [Real.norm_eq_abs,hz] at ht
    have hcξ := mul_le_mul_of_nonneg_right hc.le (abs_nonneg (ξU p))
    linarith only [hl,ht,hcξ]
  let ξ : P → ℝ := fun p => if hp : p ∈ U then ξU ⟨p,hp⟩ else 0
  have hinside (p : P) (hp : p ∈ U) :
      |ξ p| < r ∧ f (p,ξ p) = 0 ∧ |ξ p| ≤ 2*|f (p,0)| := by
    have hdata := hroot ⟨p,hp⟩
    simpa only [ξ,dif_pos hp] using
      And.intro hdata.1 (And.intro hdata.2 (hbound ⟨p,hp⟩))
  have hunique (p : P) (hp : p ∈ U) (x : ℝ) (hx : |x| ≤ r)
      (heq : f (p,x) = 0) : x = ξ p := by
    simpa only [ξ,dif_pos hp] using huniq ⟨p,hp⟩ x hx heq
  refine ⟨ξ,?_,hinside,hunique⟩
  intro p hpU
  let d := deriv (fun y => f (p,y)) (ξ p)
  have hd : d ≠ 0 := by
    have hb := hderiv p hpU (ξ p) (hinside p hpU).1.le
    intro hz
    change d = 0 at hz
    change |1-d| ≤ (c:ℝ) at hb
    rw [hz,sub_zero,abs_one] at hb
    linarith
  have hξBall : ξ p ∈ Ball := by
    simpa [Ball,Real.dist_eq] using (hinside p hpU).1.le
  have hAt := hfAt p hpU (ξ p) (hrV hξBall)
  have hpartial : fderiv ℝ f (p,ξ p) ∘L ContinuousLinearMap.inr ℝ P ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d := by
    exact ((hp ⟨p,hpU⟩ (ξ p) hξBall).hasFDerivAt.unique
      ((hAt.differentiableAt hn).hasFDerivAt.comp (ξ p)
        (hasFDerivAt_prodMk_right p (ξ p)))).symm
  have hinv : (fderiv ℝ f (p,ξ p) ∘L ContinuousLinearMap.inr ℝ P ℝ).IsInvertible := by
    rw [hpartial]
    exact scalar_map_invertible d hd
  let g := hAt.implicitFunction hn hinv
  have hg : ContDiffAt ℝ n g p := hAt.contDiffAt_implicitFunction hn hinv
  have hgself : g p = ξ p := hAt.implicitFunction_apply_self hn hinv
  have hgin : ∀ᶠ q in 𝓝 p, |g q| < r :=
    hg.continuousAt.abs.eventually_lt continuousAt_const
      (by rw [hgself]; exact (hinside p hpU).1)
  have hgeq := hAt.eventually_apply_implicitFunction hn hinv
  have hevent : ξ =ᶠ[𝓝 p] g := by
    filter_upwards [hgin,hgeq,hU.mem_nhds hpU] with q hq he hqU
    exact (hunique q hqU (g q) hq.le (he.trans (hinside p hpU).2.1)).symm
  exact (hg.congr_of_eventuallyEq hevent).contDiffWithinAt

end Lemniscate
