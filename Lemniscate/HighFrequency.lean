import Lemniscate.CoarseArithmetic
import Lemniscate.QuarticTail

/-! The four actual rational quartic bounds in the paper, proved uniformly
beyond their respective cutoffs. This module does not assume rounded table
entries: each cutoff comparison is computed from the defining coefficients.
The Fourier-row majorizations by these quartics are a separate obligation. -/
namespace Lemniscate.HighFrequency
open CoarseArithmetic

structure Quartic where
  leading : ℚ
  shift : ℚ
  quadratic : ℚ
  linear : ℚ
  constant : ℚ

def value (p : Quartic) (x : ℚ) : ℚ :=
  -p.leading*(x-p.shift)^4+p.quadratic*x^2+p.linear*x+p.constant
def first (p : Quartic) (x : ℚ) : ℚ :=
  -4*p.leading*(x-p.shift)^3+2*p.quadratic*x+p.linear
def secondHalf (p : Quartic) (x : ℚ) : ℚ :=
  -6*p.leading*(x-p.shift)^2+p.quadratic

noncomputable def realValue (p : Quartic) (x : ℝ) : ℝ :=
  shiftedQuartic p.leading p.shift p.quadratic p.linear p.constant x

def certificate (p : Quartic) (cutoff bound : ℚ) : Prop :=
  0 ≤ p.leading ∧ p.shift ≤ cutoff ∧ first p cutoff ≤ 0 ∧
    secondHalf p cutoff ≤ 0 ∧ value p cutoff < bound
instance (p : Quartic) (cutoff bound : ℚ) : Decidable (certificate p cutoff bound) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

theorem certificate_sound (p : Quartic) (cutoff bound : ℚ)
    (h : certificate p cutoff bound) :
    ∀ x : ℝ, (cutoff:ℝ) ≤ x → realValue p x < (bound:ℝ) := by
  rcases h with ⟨hc, hs, h1, h2, hb⟩
  apply shiftedQuartic_uniform_bound
  · exact_mod_cast hc
  · exact_mod_cast hs
  · dsimp [first] at h1
    exact_mod_cast h1
  · dsimp [secondHalf] at h2
    exact_mod_cast h2
  · dsimp [value] at hb
    unfold shiftedQuartic
    exact_mod_cast hb

def singlePeriod (weightRatio : ℚ) : Quartic :=
  ⟨4*rlo^2, 0,
    45*rhi+C*(moment 1 (qb/weightRatio)+moment 1 (qb*weightRatio)),
    2*C*moment 2 (qb*weightRatio), C*moment 3 (qb*weightRatio)⟩

def E : ℚ := 45*rhi*H
def s2 : ℚ := moment 1 (qb/a)+moment 1 (qb*a)
def s1 : ℚ := 2*moment 2 (qb*a)
def s0 : ℚ := moment 3 (qb*a)/3

def odd : Quartic := ⟨4*rlo^2, 0, 45*rhi+8+E*s2, E*s1, E*s0⟩
def even : Quartic :=
  ⟨4*rlo^2, 1/2, 45*rhi+5*E*s2+1,
    45*rhi+5*E*(4*s2+s1)+4,
    45*rhi/4+5*E*(4*s2+2*s1+s0)+4⟩

set_option maxRecDepth 100000 in
theorem cosine_certificate : certificate (singlePeriod a) 18 (-8000) := by decide +kernel
set_option maxRecDepth 100000 in
theorem sine_certificate : certificate (singlePeriod 1) 8 (-3308) := by decide +kernel
set_option maxRecDepth 100000 in
theorem odd_certificate : certificate odd (25/2) (-3112) := by decide +kernel
set_option maxRecDepth 100000 in
theorem even_certificate : certificate even 32 (-481088) := by decide +kernel

theorem cosine_high_bound (x : ℝ) (hx : 18 ≤ x) :
    realValue (singlePeriod a) x < -8000 := by
  simpa using certificate_sound _ _ _ cosine_certificate x (by norm_num; exact hx)
theorem sine_high_bound (x : ℝ) (hx : 8 ≤ x) :
    realValue (singlePeriod 1) x < -3308 := by
  simpa using certificate_sound _ _ _ sine_certificate x (by norm_num; exact hx)
theorem odd_high_bound (x : ℝ) (hx : 25/2 ≤ x) :
    realValue odd x < -3112 := by
  simpa using certificate_sound _ _ _ odd_certificate x (by norm_num; exact hx)
theorem even_high_bound (x : ℝ) (hx : 32 ≤ x) :
    realValue even x < -481088 := by
  simpa using certificate_sound _ _ _ even_certificate x (by norm_num; exact hx)

end Lemniscate.HighFrequency
