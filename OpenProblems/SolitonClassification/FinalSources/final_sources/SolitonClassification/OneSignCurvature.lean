module

public import SolitonClassification.SupportODE
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Lean.Util.CollectAxioms

@[expose] public section

/-!
# Curvature moments of actual periodic similarity profiles

The support equations include the dilation coefficient `a` and rotation
coefficient `b`. The integral identities below are consequences of the actual
ODE and periodicity; none is included as a premise of the profile structure.
Four support variables being periodic does not imply tangent-angle holonomy.
The final closed reconstruction theorem explicitly supplies that extra
condition before asserting the period and integer covering relation.
-/

namespace ClosedSimilarity
noncomputable section
open MeasureTheory Set
set_option backward.isDefEq.respectTransparency false

lemma interval_integral_cauchy_sq {f g : ℝ → ℝ} {L : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hL : 0 ≤ L) :
    (∫ s in 0..L, f s * g s)^2 ≤
      (∫ s in 0..L, (f s)^2) * (∫ s in 0..L, (g s)^2) := by
  have hpoly : ∀ t : ℝ, 0 ≤ (∫ s in 0..L, (g s)^2) * (t * t) +
      (2 * (∫ s in 0..L, f s * g s)) * t + (∫ s in 0..L, (f s)^2) := by
    intro t
    have hpos := intervalIntegral.integral_nonneg_of_forall (μ := volume) hL
      (fun s => sq_nonneg (f s + t * g s))
    have he : (∫ s in 0..L, (f s + t * g s)^2) =
        (t * t) * (∫ s in 0..L, (g s)^2) +
        (2 * t) * (∫ s in 0..L, f s * g s) + (∫ s in 0..L, (f s)^2) := by
      calc
        (∫ s in 0..L, (f s + t * g s)^2) =
            (∫ s in 0..L, ((t*t) * (g s)^2 + (2*t) * (f s*g s)) + (f s)^2) := by
          apply intervalIntegral.integral_congr
          intro s _
          ring
        _ = _ := by
          rw [intervalIntegral.integral_add
            (f := fun s => (t*t) * (g s)^2 + (2*t) * (f s*g s))
            (g := fun s => (f s)^2)
            ((((hg.pow 2).const_mul (t*t)).add ((hf.mul hg).const_mul (2*t))).intervalIntegrable 0 L)
            ((hf.pow 2).intervalIntegrable 0 L),
            intervalIntegral.integral_add
            (f := fun s => (t*t) * (g s)^2) (g := fun s => (2*t) * (f s*g s))
            (((hg.pow 2).const_mul (t*t)).intervalIntegrable 0 L)
            (((hf.mul hg).const_mul (2*t)).intervalIntegrable 0 L),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [he] at hpos
    nlinarith
  have hd := discrim_le_zero hpoly
  dsimp [discrim] at hd
  nlinarith

lemma continuous_nonneg_zero_of_integral_zero {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Continuous f)
    (hn : ∀ s ∈ Icc 0 L, 0 ≤ f s) (hi : (∫ s in 0..L, f s) = 0) :
    ∀ s ∈ Icc 0 L, f s = 0 := by
  intro s hs
  by_contra hh
  have hpos : 0 < f s := lt_of_le_of_ne (hn s hs) (Ne.symm hh)
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (f := fun _ : ℝ => (0 : ℝ)) (g := f) hL continuous_const.continuousOn hf.continuousOn
    (fun x hx => hn x (Ioc_subset_Icc_self hx)) ⟨s, hs, hpos⟩
  simp only [intervalIntegral.integral_zero, hi, lt_self_iff_false] at hlt

/-- The pointwise cubic converts the signed third-moment bound into rigidity.
The proof uses continuous zero-integral arguments, not a sampled range test. -/
lemma cubic_moment_rigidity {f : ℝ → ℝ} {L R : ℝ}
    (hf : Continuous f) (hL : 0 < L) (hR : 0 < R)
    (hB : (∫ s in 0..L, (f s)^2) = L * R^2)
    (hC : (∫ s in 0..L, (f s)^3) ≤ L * R^3)
    (hpinch : ∀ s ∈ Icc 0 L, -R/2 ≤ f s) :
    ∀ s ∈ Icc 0 L, f s = R := by
  let P : ℝ → ℝ := fun s => (f s + R/2) * (f s - R)^2
  have hPc : Continuous P := (hf.add continuous_const).mul ((hf.sub continuous_const).pow 2)
  have hPn : ∀ s ∈ Icc 0 L, 0 ≤ P s := by
    intro s hs
    exact mul_nonneg (by linarith [hpinch s hs]) (sq_nonneg _)
  have hPi : (∫ s in 0..L, P s) = (∫ s in 0..L, (f s)^3) - L * R^3 := by
    calc
      (∫ s in 0..L, P s) =
          (∫ s in 0..L, ((f s)^3 - (3*R/2) * (f s)^2) + R^3/2) := by
        apply intervalIntegral.integral_congr
        intro s _
        dsimp [P]
        ring
      _ = (∫ s in 0..L, (f s)^3) - (3*R/2) * (∫ s in 0..L, (f s)^2) + L*(R^3/2) := by
        rw [intervalIntegral.integral_add
          (f := fun s => (f s)^3 - (3*R/2) * (f s)^2) (g := fun _ : ℝ => R^3/2)
          (((hf.pow 3).sub ((hf.pow 2).const_mul (3*R/2))).intervalIntegrable 0 L)
          (continuous_const.intervalIntegrable 0 L),
          intervalIntegral.integral_sub (f := fun s => (f s)^3)
          (g := fun s => (3*R/2) * (f s)^2)
          ((hf.pow 3).intervalIntegrable 0 L)
          (((hf.pow 2).const_mul (3*R/2)).intervalIntegrable 0 L),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
      _ = _ := by rw [hB]; ring
  have hPzero : (∫ s in 0..L, P s) = 0 := by
    have hn := intervalIntegral.integral_nonneg (μ := volume) hL.le hPn
    rw [hPi] at hn ⊢
    linarith
  have hPpoint := continuous_nonneg_zero_of_integral_zero hL hPc hPn hPzero
  have hrange : ∀ s ∈ Icc 0 L, f s = -R/2 ∨ f s = R := by
    intro s hs
    rcases mul_eq_zero.mp (hPpoint s hs) with hh | hh
    · left
      linarith
    · right
      nlinarith [sq_nonneg (f s - R)]
  have hdefn : ∀ s ∈ Icc 0 L, 0 ≤ R^2 - (f s)^2 := by
    intro s hs
    rcases hrange s hs with hh | hh
    · rw [hh]
      nlinarith [sq_nonneg R]
    · rw [hh, sub_self]
  have hdefi : (∫ s in 0..L, R^2 - (f s)^2) = 0 := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => R^2) (g := fun s => (f s)^2)
      (continuous_const.intervalIntegrable 0 L) ((hf.pow 2).intervalIntegrable 0 L),
      intervalIntegral.integral_const, hB]
    simp
  have hdef := continuous_nonneg_zero_of_integral_zero hL
    (continuous_const.sub (hf.pow 2)) hdefn hdefi
  intro s hs
  rcases hrange s hs with hh | hh
  · have hm := hdef s hs
    change R^2 - (f s)^2 = 0 at hm
    rw [hh] at hm
    nlinarith [sq_pos_of_pos hR]
  · exact hh

structure PeriodicSupportProfile (a b L : ℝ) where
  k : ℝ → ℝ
  v : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  dk : ∀ s, HasDerivAt k (v s) s
  dv : ∀ s, HasDerivAt v (-(k s)^3 / 2 - a * p s - b * q s) s
  dp : ∀ s, HasDerivAt p (-k s * q s) s
  dq : ∀ s, HasDerivAt q (1 + k s * p s) s
  periodic_k : Function.Periodic k L
  periodic_v : Function.Periodic v L
  periodic_p : Function.Periodic p L
  periodic_q : Function.Periodic q L

namespace PeriodicSupportProfile
variable {a b L : ℝ} (z : PeriodicSupportProfile a b L)

def force (s : ℝ) : ℝ := -a * z.p s - b * z.q s
def bending : ℝ := ∫ s in 0..L, (z.k s)^2
def cubicMoment : ℝ := ∫ s in 0..L, (z.k s)^3
def forceSquare : ℝ := ∫ s in 0..L, (z.force s)^2
def dilationStress (s : ℝ) : ℝ := z.v s * z.p s + (z.k s)^2 / 2 * z.q s
def rotationStress (s : ℝ) : ℝ := z.v s * z.q s - (z.k s)^2 / 2 * z.p s - z.k s

lemma continuous_k : Continuous z.k := continuous_iff_continuousAt.mpr fun s => (z.dk s).continuousAt
lemma continuous_v : Continuous z.v := continuous_iff_continuousAt.mpr fun s => (z.dv s).continuousAt
lemma continuous_p : Continuous z.p := continuous_iff_continuousAt.mpr fun s => (z.dp s).continuousAt
lemma continuous_q : Continuous z.q := continuous_iff_continuousAt.mpr fun s => (z.dq s).continuousAt
lemma continuous_force : Continuous z.force := by
  unfold force
  exact (continuous_const.mul z.continuous_p).sub (continuous_const.mul z.continuous_q)

lemma dilationStress_hasDerivAt (s : ℝ) :
    HasDerivAt z.dilationStress (z.force s * z.p s + (z.k s)^2 / 2) s := by
  convert ((z.dv s).mul (z.dp s)).add ((((z.dk s).pow 2).div_const 2).mul (z.dq s)) using 1 <;>
    first | rfl | dsimp [dilationStress, force]; ring

lemma rotationStress_hasDerivAt (s : ℝ) :
    HasDerivAt z.rotationStress (z.force s * z.q s) s := by
  convert (((z.dv s).mul (z.dq s)).sub
    ((((z.dk s).pow 2).div_const 2).mul (z.dp s))).sub (z.dk s) using 1 <;>
    first | rfl | dsimp [rotationStress, force]; ring

private lemma integral_periodic_derivative {f g : ℝ → ℝ}
    (hd : ∀ s, HasDerivAt f (g s) s) (hg : Continuous g) (he : f L = f 0) :
    (∫ s in 0..L, g s) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hg.intervalIntegrable _ _), he, sub_self]

lemma integral_kq : (∫ s in 0..L, z.k s * z.q s) = 0 := by
  have hp0 : z.p L = z.p 0 := by simpa using z.periodic_p 0
  have hh := integral_periodic_derivative z.dp
    (z.continuous_k.neg.mul z.continuous_q) hp0
  simp only [neg_mul, intervalIntegral.integral_neg] at hh
  linarith

lemma integral_kp : (∫ s in 0..L, z.k s * z.p s) = -L := by
  have hq0 : z.q L = z.q 0 := by simpa using z.periodic_q 0
  have hh := integral_periodic_derivative z.dq
    (continuous_const.add (z.continuous_k.mul z.continuous_p)) hq0
  rw [intervalIntegral.integral_add (f := fun _ : ℝ => (1 : ℝ))
    (g := fun s => z.k s * z.p s) (continuous_const.intervalIntegrable 0 L)
    ((z.continuous_k.mul z.continuous_p).intervalIntegrable 0 L),
    intervalIntegral.integral_const] at hh
  simp only [sub_zero, smul_eq_mul, mul_one] at hh
  linarith

theorem integral_k_force : (∫ s in 0..L, z.k s * z.force s) = a * L := by
  calc
    (∫ s in 0..L, z.k s * z.force s) =
        (∫ s in 0..L, -a * (z.k s * z.p s) - b * (z.k s * z.q s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [force]
      ring
    _ = -a * (∫ s in 0..L, z.k s * z.p s) -
        b * (∫ s in 0..L, z.k s * z.q s) := by
      rw [intervalIntegral.integral_sub
        (f := fun s => -a * (z.k s * z.p s)) (g := fun s => b * (z.k s * z.q s))
        ((continuous_const.mul (z.continuous_k.mul z.continuous_p)).intervalIntegrable 0 L)
        ((continuous_const.mul (z.continuous_k.mul z.continuous_q)).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = a * L := by rw [z.integral_kp, z.integral_kq]; ring

theorem integral_force : (∫ s in 0..L, z.force s) = z.cubicMoment / 2 := by
  have hv0 : z.v L = z.v 0 := by simpa using z.periodic_v 0
  have hd : ∀ s, HasDerivAt z.v (z.force s - (z.k s)^3 / 2) s := by
    intro s
    convert z.dv s using 1; dsimp [force]; ring
  have hh := integral_periodic_derivative hd
    (z.continuous_force.sub ((z.continuous_k.pow 3).div_const 2)) hv0
  rw [intervalIntegral.integral_sub (f := z.force) (g := fun s => (z.k s)^3 / 2)
    (z.continuous_force.intervalIntegrable 0 L)
    (((z.continuous_k.pow 3).div_const 2).intervalIntegrable 0 L),
    intervalIntegral.integral_div] at hh
  dsimp [cubicMoment]
  linarith

lemma integral_force_p : (∫ s in 0..L, z.force s * z.p s) = -z.bending / 2 := by
  have he : z.dilationStress L = z.dilationStress 0 := by
    dsimp [dilationStress]
    simp only [show z.v L = z.v 0 by simpa using z.periodic_v 0,
      show z.p L = z.p 0 by simpa using z.periodic_p 0,
      show z.k L = z.k 0 by simpa using z.periodic_k 0,
      show z.q L = z.q 0 by simpa using z.periodic_q 0]
  have hh := integral_periodic_derivative z.dilationStress_hasDerivAt
    ((z.continuous_force.mul z.continuous_p).add ((z.continuous_k.pow 2).div_const 2)) he
  rw [intervalIntegral.integral_add (f := fun s => z.force s * z.p s)
    (g := fun s => (z.k s)^2 / 2) ((z.continuous_force.mul z.continuous_p).intervalIntegrable 0 L)
    (((z.continuous_k.pow 2).div_const 2).intervalIntegrable 0 L),
    intervalIntegral.integral_div] at hh
  dsimp [bending]
  linarith

lemma integral_force_q : (∫ s in 0..L, z.force s * z.q s) = 0 := by
  have he : z.rotationStress L = z.rotationStress 0 := by
    dsimp [rotationStress]
    simp only [show z.v L = z.v 0 by simpa using z.periodic_v 0,
      show z.p L = z.p 0 by simpa using z.periodic_p 0,
      show z.k L = z.k 0 by simpa using z.periodic_k 0,
      show z.q L = z.q 0 by simpa using z.periodic_q 0]
  exact integral_periodic_derivative z.rotationStress_hasDerivAt
    (z.continuous_force.mul z.continuous_q) he

theorem forceSquare_eq : z.forceSquare = a * z.bending / 2 := by
  calc
    z.forceSquare = (∫ s in 0..L, -a * (z.force s * z.p s) - b * (z.force s * z.q s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [force]
      ring
    _ = -a * (∫ s in 0..L, z.force s * z.p s) - b * (∫ s in 0..L, z.force s * z.q s) := by
      rw [intervalIntegral.integral_sub
        (f := fun s => -a * (z.force s * z.p s))
        (g := fun s => b * (z.force s * z.q s))
        ((continuous_const.mul (z.continuous_force.mul z.continuous_p)).intervalIntegrable 0 L)
        ((continuous_const.mul (z.continuous_force.mul z.continuous_q)).intervalIntegrable 0 L),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = a * z.bending / 2 := by rw [z.integral_force_p, z.integral_force_q]; ring

lemma bending_nonneg (hL : 0 ≤ L) : 0 ≤ z.bending :=
  intervalIntegral.integral_nonneg_of_forall hL fun s => sq_nonneg (z.k s)

theorem bending_sq_lower (ha : 0 < a) (hL : 0 ≤ L) :
    2 * a * L^2 ≤ z.bending^2 := by
  have hc := interval_integral_cauchy_sq z.continuous_k z.continuous_force hL
  rw [z.integral_k_force] at hc
  change (a * L)^2 ≤ z.bending * z.forceSquare at hc
  rw [z.forceSquare_eq] at hc
  have hh : 0 ≤ a * (z.bending^2 - 2*a*L^2) := by nlinarith
  have := (mul_nonneg_iff_of_pos_left ha).mp hh
  linarith

theorem bending_pos (ha : 0 < a) (hL : 0 < L) : 0 < z.bending := by
  have hn := z.bending_nonneg hL.le
  have hl := z.bending_sq_lower ha hL.le
  have hp : 0 < 2*a*L^2 := mul_pos (mul_pos (by norm_num) ha) (sq_pos_of_pos hL)
  nlinarith

theorem cubic_sq_upper (hL : 0 ≤ L) :
    z.cubicMoment^2 ≤ 2*a*L*z.bending := by
  have hc := interval_integral_cauchy_sq z.continuous_force
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))) hL
  simp only [mul_one, one_pow, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hc
  rw [z.integral_force] at hc
  change (z.cubicMoment / 2)^2 ≤ z.forceSquare * L at hc
  rw [z.forceSquare_eq] at hc
  nlinarith

theorem cubic_sq_mul_length_le (ha : 0 < a) (hL : 0 ≤ L) :
    z.cubicMoment^2 * L ≤ z.bending^3 := by
  have h₁ := mul_le_mul_of_nonneg_right (z.cubic_sq_upper hL) hL
  have h₂ := mul_le_mul_of_nonneg_right (z.bending_sq_lower ha hL) (z.bending_nonneg hL)
  nlinarith

def curvatureRMS : ℝ := Real.sqrt (z.bending / L)

lemma curvatureRMS_pos (ha : 0 < a) (hL : 0 < L) : 0 < z.curvatureRMS := by
  exact Real.sqrt_pos.mpr (div_pos (z.bending_pos ha hL) hL)

lemma bending_eq_length_rms_sq (hL : 0 < L) :
    z.bending = L * z.curvatureRMS^2 := by
  have hh := Real.sq_sqrt (div_nonneg (z.bending_nonneg hL.le) hL.le)
  change z.curvatureRMS^2 = z.bending / L at hh
  rw [hh]
  field_simp

theorem cubic_le_length_rms_cube (ha : 0 < a) (hL : 0 < L) :
    z.cubicMoment ≤ L * z.curvatureRMS^3 := by
  have hc : z.cubicMoment^2 * L ≤ (L * z.curvatureRMS^3)^2 * L := by
    calc
      z.cubicMoment^2 * L ≤ z.bending^3 := z.cubic_sq_mul_length_le ha hL.le
      _ = (L * z.curvatureRMS^3)^2 * L := by
        rw [z.bending_eq_length_rms_sq hL]
        ring
  exact le_of_sq_le_sq (le_of_mul_le_mul_right hc hL)
    (mul_nonneg hL.le (pow_nonneg (z.curvatureRMS_pos ha hL).le _))

/-- A genuine periodic support-ODE profile satisfying the half-RMS pinching
condition has constant positive curvature everywhere. -/
theorem curvature_constant_of_half_rms (ha : 0 < a) (hL : 0 < L)
    (hpinch : ∀ s, -z.curvatureRMS/2 ≤ z.k s) :
    ∀ s, z.k s = z.curvatureRMS := by
  have hc := cubic_moment_rigidity z.continuous_k hL (z.curvatureRMS_pos ha hL)
    (z.bending_eq_length_rms_sq hL) (z.cubic_le_length_rms_cube ha hL)
    (fun s _ => hpinch s)
  intro s
  obtain ⟨t, ht, he⟩ := z.periodic_k.exists_mem_Ico₀ hL s
  exact he.trans (hc t ⟨ht.1, ht.2.le⟩)

theorem curvature_constant_of_nonneg (ha : 0 < a) (hL : 0 < L)
    (hkn : ∀ s, 0 ≤ z.k s) : ∀ s, z.k s = z.curvatureRMS := by
  apply z.curvature_constant_of_half_rms ha hL
  intro s
  have hR := z.curvatureRMS_pos ha hL
  linarith [hkn s]

theorem neg_cubic_le_length_rms_cube (ha : 0 < a) (hL : 0 < L) :
    -z.cubicMoment ≤ L * z.curvatureRMS^3 := by
  have hc : (-z.cubicMoment)^2 * L ≤ (L * z.curvatureRMS^3)^2 * L := by
    calc
      (-z.cubicMoment)^2 * L = z.cubicMoment^2 * L := by ring
      _ ≤ z.bending^3 := z.cubic_sq_mul_length_le ha hL.le
      _ = (L * z.curvatureRMS^3)^2 * L := by
        rw [z.bending_eq_length_rms_sq hL]
        ring
  exact le_of_sq_le_sq (le_of_mul_le_mul_right hc hL)
    (mul_nonneg hL.le (pow_nonneg (z.curvatureRMS_pos ha hL).le _))

theorem curvature_constant_of_upper_half_rms (ha : 0 < a) (hL : 0 < L)
    (hpinch : ∀ s, z.k s ≤ z.curvatureRMS/2) :
    ∀ s, z.k s = -z.curvatureRMS := by
  have hB : (∫ s in 0..L, (-z.k s)^2) = L * z.curvatureRMS^2 := by
    simpa only [neg_sq, bending] using z.bending_eq_length_rms_sq hL
  have hC : (∫ s in 0..L, (-z.k s)^3) ≤ L * z.curvatureRMS^3 := by
    calc
      (∫ s in 0..L, (-z.k s)^3) = (∫ s in 0..L, -(z.k s)^3) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = -z.cubicMoment := by rw [intervalIntegral.integral_neg]; rfl
      _ ≤ _ := z.neg_cubic_le_length_rms_cube ha hL
  have hc := cubic_moment_rigidity z.continuous_k.neg hL (z.curvatureRMS_pos ha hL) hB hC
    (fun s _ => by change -z.curvatureRMS/2 ≤ -z.k s; linarith [hpinch s])
  intro s
  obtain ⟨t, ht, he⟩ := z.periodic_k.exists_mem_Ico₀ hL s
  have hh := hc t ⟨ht.1, ht.2.le⟩
  change -z.k t = z.curvatureRMS at hh
  linarith

theorem curvature_constant_of_nonpos (ha : 0 < a) (hL : 0 < L)
    (hkn : ∀ s, z.k s ≤ 0) : ∀ s, z.k s = -z.curvatureRMS := by
  apply z.curvature_constant_of_upper_half_rms ha hL
  intro s
  have hR := z.curvatureRMS_pos ha hL
  linarith [hkn s]

/-- Every nonconstant periodic soliton curvature has both quantitatively large
positive and negative excursions. These are pointwise statements on the
continuous ODE solution, not tests on a finite sample. -/
theorem both_curvature_excursions (ha : 0 < a) (hL : 0 < L)
    (hnonconstant : ¬∃ c : ℝ, ∀ s, z.k s = c) :
    (∃ s, z.k s < -z.curvatureRMS/2) ∧ (∃ s, z.curvatureRMS/2 < z.k s) := by
  constructor
  · by_contra hh
    push Not at hh
    exact hnonconstant ⟨z.curvatureRMS, z.curvature_constant_of_half_rms ha hL hh⟩
  · by_contra hh
    push Not at hh
    exact hnonconstant ⟨-z.curvatureRMS, z.curvature_constant_of_upper_half_rms ha hL hh⟩

/-- Constant nonzero curvature in the actual support system fixes the center
as well as the radius; a translated circle cannot satisfy this profile ODE. -/
theorem constant_curvature_support (ha : 0 < a) {c : ℝ} (hc : c ≠ 0)
    (hk : ∀ s, z.k s = c) :
    c^4 = 2*a ∧ (∀ s, z.v s = 0) ∧ (∀ s, z.p s = -1/c) ∧ (∀ s, z.q s = 0) := by
  have hkfun : z.k = fun _ => c := funext hk
  have hv : ∀ s, z.v s = 0 := by
    intro s
    have hd : HasDerivAt z.k 0 s := by rw [hkfun]; exact hasDerivAt_const s c
    exact (z.dk s).unique hd
  have hvfun : z.v = fun _ => 0 := funext hv
  have hA : ∀ s, a*z.p s+b*z.q s = -c^3/2 := by
    intro s
    have hd : HasDerivAt z.v 0 s := by rw [hvfun]; exact hasDerivAt_const s 0
    have hh := (z.dv s).unique hd
    rw [hk s] at hh
    linarith
  have hAfun : (fun s => a*z.p s+b*z.q s) = fun _ => -c^3/2 := funext hA
  have hS : ∀ s, c*(a*z.q s-b*z.p s) = b := by
    intro s
    have hd := ((z.dp s).const_mul a).add ((z.dq s).const_mul b)
    have hcst : HasDerivAt (fun s => a*z.p s+b*z.q s) 0 s := by
      rw [hAfun]
      exact hasDerivAt_const s (-c^3/2)
    have hh := hd.unique hcst
    rw [hk s] at hh
    nlinarith
  have hSfun : (fun s => c*(a*z.q s-b*z.p s)) = fun _ => b := funext hS
  have hc4 : c^4 = 2*a := by
    have hd := (((z.dq 0).const_mul a).sub ((z.dp 0).const_mul b)).const_mul c
    have hcst : HasDerivAt (fun s => c*(a*z.q s-b*z.p s)) 0 0 := by
      rw [hSfun]
      exact hasDerivAt_const 0 b
    have hh := hd.unique hcst
    rw [hk 0] at hh
    have hfactor : c * (a-c^4/2) = 0 := by
      linear_combination hh - c^2 * hA 0
    have := (mul_eq_zero.mp hfactor).resolve_left hc
    linarith
  have hdet : a^2+b^2 ≠ 0 := by
    have hapos := sq_pos_of_pos ha
    nlinarith [sq_nonneg b]
  have hpq : ∀ s, 1+c*z.p s = 0 ∧ c*z.q s = 0 := by
    intro s
    have hx : a*(1+c*z.p s)+b*(c*z.q s) = 0 := by
      linear_combination c * hA s - hc4 / 2
    have hy : a*(c*z.q s)-b*(1+c*z.p s) = 0 := by
      linear_combination hS s
    have hpx : (a^2+b^2)*(1+c*z.p s) = 0 := by
      linear_combination a*hx-b*hy
    have hqx : (a^2+b^2)*(c*z.q s) = 0 := by
      linear_combination b*hx+a*hy
    exact ⟨(mul_eq_zero.mp hpx).resolve_left hdet, (mul_eq_zero.mp hqx).resolve_left hdet⟩
  refine ⟨hc4, hv, ?_, ?_⟩
  · intro s
    apply (eq_div_iff hc).2
    nlinarith [(hpq s).1]
  · intro s
    exact (mul_eq_zero.mp (hpq s).2).resolve_left hc

theorem centered_circle_of_half_rms (ha : 0 < a) (hL : 0 < L)
    (hpinch : ∀ s, -z.curvatureRMS/2 ≤ z.k s) :
    z.curvatureRMS^4 = 2*a ∧
      (∀ s, z.k s = z.curvatureRMS) ∧
      (∀ s, z.v s = 0) ∧ (∀ s, z.p s = -1/z.curvatureRMS) ∧
      (∀ s, z.q s = 0) := by
  have hk := z.curvature_constant_of_half_rms ha hL hpinch
  obtain ⟨hr, hv, hp, hq⟩ := z.constant_curvature_support ha (z.curvatureRMS_pos ha hL).ne' hk
  exact ⟨hr, hk, hv, hp, hq⟩

theorem reconstructed_circle_of_half_rms (ha : 0 < a) (hL : 0 < L)
    (hpinch : ∀ s, -z.curvatureRMS/2 ≤ z.k s) (theta : ℝ → ℝ) (s : ℝ) :
    (profileX z.p z.q theta s)^2 + (profileY z.p z.q theta s)^2 =
      (1/z.curvatureRMS)^2 := by
  obtain ⟨_, _, _, hp, hq⟩ := z.centered_circle_of_half_rms ha hL hpinch
  have ht := Real.sin_sq_add_cos_sq (theta s)
  dsimp [profileX, profileY]
  rw [hp s, hq s]
  linear_combination (1/z.curvatureRMS)^2 * ht

/-- One-sign curvature in the actual periodic support ODE fixes a nonzero
constant curvature, its radius, and the support coordinates of the centered
circle. Combining with `SupportODE` reconstructs a unit-speed circle. -/
theorem one_sign_centered_circle (ha : 0 < a) (hL : 0 < L)
    (hsign : (∀ s, 0 ≤ z.k s) ∨ (∀ s, z.k s ≤ 0)) :
    ∃ c : ℝ, c ≠ 0 ∧ c^4 = 2*a ∧ (∀ s, z.k s = c) ∧
      (∀ s, z.v s = 0) ∧ (∀ s, z.p s = -1/c) ∧ (∀ s, z.q s = 0) := by
  rcases hsign with hkn | hkn
  · have hk := z.curvature_constant_of_nonneg ha hL hkn
    have hc := (z.curvatureRMS_pos ha hL).ne'
    obtain ⟨hr, hv, hp, hq⟩ := z.constant_curvature_support ha hc hk
    exact ⟨z.curvatureRMS, hc, hr, hk, hv, hp, hq⟩
  · have hk := z.curvature_constant_of_nonpos ha hL hkn
    have hc : -z.curvatureRMS ≠ 0 := neg_ne_zero.mpr (z.curvatureRMS_pos ha hL).ne'
    obtain ⟨hr, hv, hp, hq⟩ := z.constant_curvature_support ha hc hk
    exact ⟨-z.curvatureRMS, hc, hr, hk, hv, hp, hq⟩

/-- The geometric closed-curve conclusion retains the explicit angle holonomy
premise. It includes the actual unit-speed derivative and integer covering
relation, rather than equating support periodicity with planar closure. -/
theorem one_sign_closed_reconstruction (ha : 0 < a) (hL : 0 < L)
    (hsign : (∀ s, 0 ≤ z.k s) ∨ (∀ s, z.k s ≤ 0))
    (theta : ℝ → ℝ) (n : ℤ)
    (ht : ∀ s, HasDerivAt theta (z.k s) s)
    (hhol : ∀ s, theta (s+L) = theta s + n*(2*Real.pi)) :
    ∃ c : ℝ, c ≠ 0 ∧ c^4 = 2*a ∧ c*L = n*(2*Real.pi) ∧
      Function.Periodic (profileX z.p z.q theta) L ∧
      Function.Periodic (profileY z.p z.q theta) L ∧
      (∀ s, (profileX z.p z.q theta s)^2 + (profileY z.p z.q theta s)^2 = (1/c)^2) ∧
      (∀ s, (deriv (profileX z.p z.q theta) s)^2 +
        (deriv (profileY z.p z.q theta) s)^2 = 1) := by
  obtain ⟨c, hc, hc4, hk, _, hp, hq⟩ := z.one_sign_centered_circle ha hL hsign
  have hcover : c*L = n*(2*Real.pi) := by
    have hi : (∫ s in 0..L, c) = theta L - theta 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro s _
        simpa only [hk s] using ht s
      · exact continuous_const.intervalIntegrable 0 L
    rw [intervalIntegral.integral_const] at hi
    have hh := hhol 0
    simp only [zero_add] at hh
    simp only [sub_zero, smul_eq_mul] at hi
    linarith
  obtain ⟨hpx, hpy⟩ := profile_periodic z.p z.q theta L n z.periodic_p z.periodic_q hhol
  refine ⟨c, hc, hc4, hcover, hpx, hpy, ?_, ?_⟩
  · intro s
    have hcirc := Real.sin_sq_add_cos_sq (theta s)
    dsimp [profileX, profileY]
    rw [hp s, hq s]
    linear_combination (1/c)^2 * hcirc
  · intro s
    exact profile_unit_speed z.k z.p z.q theta s (z.dp s) (z.dq s) (ht s)

end PeriodicSupportProfile
end
end ClosedSimilarity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`ClosedSimilarity).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "OneSignCurvature audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  logInfo m!"OneSignCurvature audit passed: {checked} declarations, standard axioms only."
