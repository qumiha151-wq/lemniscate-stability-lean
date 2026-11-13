module

public import SolitonClassification.Rotating.MidpointDerivative

@[expose] public section

namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem quadraticMidpoint_fderiv_at {f : E → F} {K : ℝ≥0} (hf : LipschitzWith K f)
    {c : E} {R C : ℝ} (hC : 0 ≤ C)
    (hmid : ∀ a ∈ Metric.ball c R, ∀ b ∈ Metric.ball c R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2)
    {x : E} (hx : x ∈ Metric.ball c R) :
    HasFDerivAt f (fderiv ℝ f x) x ∧
      ∀ u, ‖u‖<R-dist x c → ‖f (x+u)-f x-fderiv ℝ f x u‖ ≤ 4*C*‖u‖^2 := by
  have hR : 0<R-dist x c := sub_pos.mpr hx
  have hs : Metric.ball x (R-dist x c) ⊆ Metric.ball c R := by
    intro a ha
    have hd := dist_triangle a x c
    change dist a x < R-dist x c at ha
    change dist a c < R
    linarith
  obtain ⟨A,hA,_,hr⟩ := exists_hasFDerivAt_of_quadratic_midpoints hf hR hC
    (fun a ha b hb => hmid a (hs ha) b (hs hb))
  exact ⟨hA.differentiableAt.hasFDerivAt, by simpa only [hA.fderiv] using hr⟩

omit [CompleteSpace F] in
lemma quadraticMidpoint_rectangle {f : E → F} {c x y v : E} {R C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hmid : ∀ a ∈ Metric.ball c R, ∀ b ∈ Metric.ball c R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2)
    (hx : x ∈ Metric.ball c R) (hy : y ∈ Metric.ball c R)
    (hxv : x+v ∈ Metric.ball c R) (hyv : y+v ∈ Metric.ball c R)
    (hxy : ‖x-y‖ ≤ d) (hv : ‖v‖ ≤ d) :
    ‖f (x+v)-f x-(f (y+v)-f y)‖ ≤ 16*C*d^2 := by
  have h1 := hmid x hx (y+v) hyv
  have h2 := hmid y hy (x+v) hxv
  have hm : (1/2:ℝ) • (y+(x+v))=(1/2:ℝ) • (x+(y+v)) := by module
  rw [hm] at h2
  have hn1 : ‖x-(y+v)‖ ≤ 2*d := by
    have hh := norm_sub_le (x-y) v
    rw [sub_sub] at hh
    linarith
  have hn2 : ‖y-(x+v)‖ ≤ 2*d := by
    have hh := norm_sub_le (y-x) v
    rw [sub_sub,norm_sub_rev y x] at hh
    linarith
  have hs1 := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn1) hC
  have hs2 := mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn2) hC
  let q1 := f ((1/2:ℝ) • (x+(y+v)))-(1/2:ℝ) • (f x+f (y+v))
  let q2 := f ((1/2:ℝ) • (x+(y+v)))-(1/2:ℝ) • (f y+f (x+v))
  have he : f (x+v)-f x-(f (y+v)-f y)=(2:ℝ) • (q1-q2) := by
    dsimp [q1,q2]
    module
  rw [he,norm_smul]
  norm_num
  have hn := norm_sub_le q1 q2
  change ‖q1‖ ≤ _ at h1
  change ‖q2‖ ≤ _ at h2
  nlinarith

/-- The genuine derivative constructed from the midpoint estimate is
Lipschitz on a smaller ball. No Hessian is assumed to exist. -/
theorem quadraticMidpoint_fderiv_variation {f : E → F} {K : ℝ≥0}
    (hf : LipschitzWith K f) {c : E} {R C : ℝ} (_hR : 0<R) (hC : 0 ≤ C)
    (hmid : ∀ a ∈ Metric.ball c R, ∀ b ∈ Metric.ball c R,
      ‖f ((1/2:ℝ) • (a+b))-(1/2:ℝ) • (f a+f b)‖ ≤ C*‖a-b‖^2)
    {x y : E} (hx : x ∈ Metric.ball c (R/4)) (hy : y ∈ Metric.ball c (R/4)) :
    ‖fderiv ℝ f x-fderiv ℝ f y‖ ≤ 24*C*dist x y := by
  by_cases heq : x=y
  · simp [heq]
  let d := ‖x-y‖
  have hd : 0<d := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hx' : dist x c < R/4 := hx
  have hy' : dist y c < R/4 := hy
  have hdsmall : d<R/2 := by
    have ht := dist_triangle x c y
    rw [dist_comm c y,dist_eq_norm x y] at ht
    linarith
  have hxR : x ∈ Metric.ball c R := by change dist x c<R; linarith
  have hyR : y ∈ Metric.ball c R := by change dist y c<R; linarith
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro u hu
  let v := d • u
  have hv : ‖v‖=d := by simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos hd,hu]
  have hxv : x+v ∈ Metric.ball c R := by
    have ht := dist_triangle (x+v) x c
    simp only [dist_eq_norm (x+v) x,add_sub_cancel_left,hv] at ht
    change dist (x+v) c<R
    linarith
  have hyv : y+v ∈ Metric.ball c R := by
    have ht := dist_triangle (y+v) y c
    simp only [dist_eq_norm (y+v) y,add_sub_cancel_left,hv] at ht
    change dist (y+v) c<R
    linarith
  have hrx := (quadraticMidpoint_fderiv_at hf hC hmid hxR).2 v (by rw [hv]; linarith)
  have hry := (quadraticMidpoint_fderiv_at hf hC hmid hyR).2 v (by rw [hv]; linarith)
  have hrect := quadraticMidpoint_rectangle hC hd.le hmid hxR hyR hxv hyv le_rfl hv.le
  rw [hv] at hrx hry
  let rx := f (x+v)-f x-fderiv ℝ f x v
  let ry := f (y+v)-f y-fderiv ℝ f y v
  have he : (fderiv ℝ f x-fderiv ℝ f y) v =
      (f (x+v)-f x-(f (y+v)-f y))-rx+ry := by
    dsimp [rx,ry]
    simp only [sub_apply]
    abel
  have hn := norm_add_le ((f (x+v)-f x-(f (y+v)-f y))-rx) ry
  have hn' := norm_sub_le (f (x+v)-f x-(f (y+v)-f y)) rx
  have hb : ‖(fderiv ℝ f x-fderiv ℝ f y) v‖ ≤ 24*C*d^2 := by
    rw [he]
    change ‖rx‖ ≤ _ at hrx
    change ‖ry‖ ≤ _ at hry
    nlinarith
  apply (mul_le_mul_iff_right₀ hd).mp
  calc
    d*‖(fderiv ℝ f x-fderiv ℝ f y) u‖ = ‖(fderiv ℝ f x-fderiv ℝ f y) v‖ := by
      simp [v,norm_smul,Real.norm_eq_abs,abs_of_pos hd]
    _ ≤ 24*C*d^2 := hb
    _ = d*(24*C*dist x y) := by rw [dist_eq_norm]; dsimp [d]; ring

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.quadraticMidpoint_fderiv_variation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"Derivative-variation audit passed for {checked} declarations."


end
