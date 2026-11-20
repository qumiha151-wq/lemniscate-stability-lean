import SolitonClassification.Rotating.BanachRoot
import SolitonClassification.SupportODE
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Uniform continuation and pitch secants for an actual shooting map obeying
a preconditioned derivative bound. Realization of a particular derivative
bound by its ODE certificate is a separate hypothesis. -/
noncomputable section
namespace SolitonClassification.Rotating.PitchContinuation
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common center budget fits every shifted target in a whole interval. -/
theorem roots_for_shifted_targets [CompleteSpace E]
    (F : E → E) (D : E → E →L[ℝ] E) (B : E →L[ℝ] E) (p e : E)
    {r η τ : ℝ} (q : ℝ≥0) (hr : 0 ≤ r) (hq : q < 1) (hB : Function.Injective B)
    (hF : ∀ x ∈ closedBall p r, HasFDerivAt F (D x) x)
    (hD : ∀ x ∈ closedBall p r, ‖ContinuousLinearMap.id ℝ E - B.comp (D x)‖ ≤ (q:ℝ))
    (hcenter : ‖B (F p)‖ ≤ η) (hself : η+τ*‖B e‖+(q:ℝ)*r ≤ r)
    (t : ℝ) (ht : |t| ≤ τ) :
    ∃ x ∈ closedBall p r, F x = t • e ∧
      ∀ y ∈ closedBall p r, F y = t • e → y=x := by
  let G : E → E := fun x => F x - t • e
  have dG (x : E) (hx : x ∈ closedBall p r) : HasFDerivAt G (D x) x :=
    (hF x hx).sub_const _
  have hG : ‖B (G p)‖ ≤ η+τ*‖B e‖ := by
    dsimp only [G]
    rw [map_sub, map_smul]
    have hn := norm_sub_le (B (F p)) (t • B e)
    rw [norm_smul, Real.norm_eq_abs] at hn
    exact hn.trans (add_le_add hcenter (mul_le_mul_of_nonneg_right ht (norm_nonneg _)))
  obtain ⟨x,hx,hzero,huniq⟩ :=
    exists_unique_zero_of_preconditioned_bounds G D B p r (η+τ*‖B e‖) q
      hr hq hB dG hD hG hself
  exact ⟨x,hx,sub_eq_zero.mp hzero,fun y hy he => huniq y hy (sub_eq_zero.mpr he)⟩

/-- Both the Lipschitz bound for the genuine solution and the error around
the preconditioned secant are independent of the choice of two targets. -/
theorem shooting_secants (F : E → E) (D : E → E →L[ℝ] E) (B : E →L[ℝ] E) (p e : E)
    {r s t q : ℝ} (hq : q < 1) (hq0 : 0 ≤ q) {x y : E}
    (hx : x ∈ closedBall p r) (hy : y ∈ closedBall p r)
    (hF : ∀ z ∈ closedBall p r, HasFDerivAt F (D z) z)
    (hD : ∀ z ∈ closedBall p r, ‖ContinuousLinearMap.id ℝ E - B.comp (D z)‖ ≤ q)
    (hFx : F x = t • e) (hFy : F y = s • e) :
    ‖x-y‖ ≤ |t-s| * ‖B e‖/(1-q) ∧
    ‖x-y-(t-s) • B e‖ ≤ q*(|t-s| * ‖B e‖/(1-q)) := by
  let T : E → E := fun z => z-B (F z)
  have dT (z : E) (hz : z ∈ closedBall p r) :
      HasFDerivAt T (ContinuousLinearMap.id ℝ E-B.comp (D z)) z :=
    (hasFDerivAt_id z).sub (B.hasFDerivAt.comp z (hF z hz))
  have herr := (convex_closedBall p r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (dT z hz).hasFDerivWithinAt) hD hy hx
  have hid : T x-T y = x-y-(t-s) • B e := by
    dsimp only [T]
    rw [hFx,hFy,map_smul,map_smul,sub_smul]
    abel
  rw [hid] at herr
  have hsum := norm_sub_le_norm_sub_add_norm_sub (x-y) ((t-s) • B e) 0
  simp only [sub_zero, norm_smul, Real.norm_eq_abs] at hsum
  have hxy : ‖x-y‖ ≤ |t-s| * ‖B e‖/(1-q) :=
    (le_div_iff₀ (sub_pos.mpr hq)).mpr (by nlinarith only [herr,hsum])
  exact ⟨hxy,herr.trans (mul_le_mul_of_nonneg_left hxy hq0)⟩

/-- A coordinate of the normalized shooting parameters inherits a signed
secant slope bound in the actual sup norm. -/
theorem coordinate_slope {n : ℕ} {x y v : Fin n → ℝ} (i : Fin n) {s t δ : ℝ}
    (hst : s < t) (herr : ‖x-y-(t-s) • v‖ ≤ δ*(t-s)) :
    |(x i-y i)/(t-s)-v i| ≤ δ := by
  have hi := (norm_le_pi_norm (x-y-(t-s) • v) i).trans herr
  change ‖(x i-y i)-(t-s)*v i‖ ≤ _ at hi
  rw [Real.norm_eq_abs] at hi
  have ht := sub_pos.mpr hst
  rw [show (x i-y i)/(t-s)-v i = ((x i-y i)-(t-s)*v i)/(t-s) by
    field_simp [ht.ne'], abs_div, abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr hi

/-- For every subinterval of the pitch image there is a parameter there
whose true turning angle is a rational multiple of two pi. -/
theorem rational_holonomy_pitch_dense {a d θ : ℝ} {pitch : ℝ → ℝ}
    (had : a ≤ d) (hc : ContinuousOn pitch (Icc a d)) (ha : StrictAntiOn pitch (Icc a d))
    {x y : ℝ} (hx : pitch d ≤ x) (hxy : x < y) (hy : y ≤ pitch a) :
    ∃ t ∈ Icc a d, x < pitch t ∧ pitch t < y ∧
      ∃ u : ℚ, θ+t=2*Real.pi*(u:ℝ) := by
  have hd := hc.surjOn_Icc (Set.right_mem_Icc.mpr had) (Set.left_mem_Icc.mpr had)
  obtain ⟨s,hs,hes⟩ := hd (show y ∈ Icc (pitch d) (pitch a) from ⟨hx.trans hxy.le,hy⟩)
  obtain ⟨v,hv,hev⟩ := hd (show x ∈ Icc (pitch d) (pitch a) from ⟨hx,hxy.le.trans hy⟩)
  have hsv : s < v := by
    by_contra! hvs
    have := ha.antitoneOn hv hs hvs
    linarith
  have hp : 0 < 2*Real.pi := by positivity
  obtain ⟨u,hu,hv'⟩ := exists_rat_btwn
    (div_lt_div_of_pos_right (show θ+s < θ+v by linarith) hp)
  let t : ℝ := (2*Real.pi)*(u:ℝ)-θ
  have hst : s<t := by dsimp only [t]; linarith [(div_lt_iff₀ hp).mp hu]
  have htv : t<v := by dsimp only [t]; linarith [(lt_div_iff₀ hp).mp hv']
  have ht : t ∈ Icc a d := ⟨hs.1.trans hst.le,htv.le.trans hv.2⟩
  refine ⟨t,ht,?_,?_,u,by dsimp [t]; ring⟩
  · rw [← hev]; exact ha ht hv htv
  · rw [← hes]; exact ha hs ht hst

/-- The actual differentiable shooting map and its uniform preconditioned
derivative enclosure produce one strictly decreasing pitch branch. Each
open subinterval of the image contains a root of rational holonomy. -/
theorem dense_pitch_of_certificate {n : ℕ} (i : Fin n)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (D : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (p e : Fin n → ℝ)
    {r η τ θ : ℝ} (q : ℝ≥0) (hr : 0 ≤ r) (hτ : 0 < τ)
    (hq : q < 1) (hB : Function.Injective B)
    (hF : ∀ x ∈ closedBall p r, HasFDerivAt F (D x) x)
    (hD : ∀ x ∈ closedBall p r,
      ‖ContinuousLinearMap.id ℝ (Fin n → ℝ) - B.comp (D x)‖ ≤ (q:ℝ))
    (hcenter : ‖B (F p)‖ ≤ η) (hself : η+τ*‖B e‖+(q:ℝ)*r ≤ r)
    (hnegative : (B e) i+(q:ℝ)*‖B e‖/(1-(q:ℝ)) < 0) :
    ∃ c : ℝ → (Fin n → ℝ),
      (∀ t ∈ Icc (-τ) τ, c t ∈ closedBall p r ∧ F (c t) = t • e) ∧
      ContinuousOn c (Icc (-τ) τ) ∧ StrictAntiOn (fun t => c t i) (Icc (-τ) τ) ∧
      ∀ x y, c τ i ≤ x → x < y → y ≤ c (-τ) i →
        ∃ t ∈ Icc (-τ) τ, x < c t i ∧ c t i < y ∧ ∃ u : ℚ, θ+t=2*Real.pi*(u:ℝ) := by
  classical
  have ex (t : ℝ) : ∃ v : Fin n → ℝ, t ∈ Icc (-τ) τ →
      v ∈ closedBall p r ∧ F v = t • e := by
    by_cases ht : t ∈ Icc (-τ) τ
    · obtain ⟨v,hv,he,_⟩ :=
        roots_for_shifted_targets F D B p e q hr hq hB hF hD hcenter hself t (abs_le.mpr ht)
      exact ⟨v,fun _ => ⟨hv,he⟩⟩
    · exact ⟨p,fun h => (ht h).elim⟩
  choose c hc using ex
  have hq' : (q:ℝ)<1 := hq
  have hp : 0<1-(q:ℝ) := sub_pos.mpr hq'
  have sec {s t : ℝ} (hs : s ∈ Icc (-τ) τ) (ht : t ∈ Icc (-τ) τ) :=
    shooting_secants F D B p e hq' q.coe_nonneg (hc t ht).1 (hc s hs).1
      hF hD (hc t ht).2 (hc s hs).2
  have hLip : LipschitzOnWith ⟨‖B e‖/(1-(q:ℝ)), div_nonneg (norm_nonneg _) hp.le⟩
      c (Icc (-τ) τ) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht s hs
    rw [dist_eq_norm, Real.dist_eq]
    change ‖c t-c s‖ ≤ ‖B e‖/(1-(q:ℝ))*|t-s|
    calc
      _ ≤ _ := (sec hs ht).1
      _ = _ := by ring
  have anti : StrictAntiOn (fun t => c t i) (Icc (-τ) τ) := by
    intro s hs t ht hst
    let δ := (q:ℝ)*‖B e‖/(1-(q:ℝ))
    have err : ‖c t-c s-(t-s) • B e‖ ≤ δ*(t-s) := by
      calc
        _ ≤ _ := (sec hs ht).2
        _ = _ := by rw [abs_of_pos (sub_pos.mpr hst)]; dsimp only [δ]; ring
    have slope := (abs_le.mp (coordinate_slope i hst err)).2
    have hn : (c t i-c s i)/(t-s) < 0 := by dsimp [δ] at slope; linarith
    have neg := (div_lt_iff₀ (sub_pos.mpr hst)).mp hn
    dsimp only
    linarith
  refine ⟨c,hc,hLip.continuousOn,anti,?_⟩
  intro x y hx hxy hy
  exact rational_holonomy_pitch_dense (by linarith : -τ ≤ τ)
    ((continuous_apply i).comp_continuousOn hLip.continuousOn) anti hx hxy hy

/-- Rational block holonomy closes the reconstructed planar curve after
the actual rational denominator many support periods. -/
theorem rational_holonomy_closed_reconstruction (p q θ : ℝ → ℝ) (P : ℝ) (u : ℚ)
    (hp : Function.Periodic p P) (hq : Function.Periodic q P)
    (hθ : ∀ s, θ (s+P) = θ s + 2*Real.pi*(u:ℝ)) :
    Function.Periodic (ClosedSimilarity.profileX p q θ) ((u.den:ℝ)*P) ∧
    Function.Periodic (ClosedSimilarity.profileY p q θ) ((u.den:ℝ)*P) := by
  have iter (s : ℝ) (n : ℕ) : θ (s+(n:ℝ)*P) = θ s+(n:ℝ)*(2*Real.pi*(u:ℝ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, hθ, ih]
      ring
  apply ClosedSimilarity.profile_periodic p q θ _ u.num (hp.nat_mul _) (hq.nat_mul _)
  intro s
  rw [iter, Rat.cast_def]
  have hd : (u.den:ℝ) ≠ 0 := by exact_mod_cast u.den_nz
  field_simp [hd]

end SolitonClassification.Rotating.PitchContinuation

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf n then
      for ax in (← collectAxioms n) do
        unless (#[`propext, `Classical.choice, `Quot.sound] : Array Name).contains ax do
          throwError "Pitch continuation axiom audit failed for {n} at {ax}"
      count := count+1
  logInfo m!"Pitch continuation audit passed for {count} declarations."
