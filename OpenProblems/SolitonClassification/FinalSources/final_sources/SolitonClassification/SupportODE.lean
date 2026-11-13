module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!+# Reconstruction from the nonsingular support-coordinate soliton ODE

This module proves actual derivative and unit-speed identities. It does not
assert existence of a periodic ODE orbit, classify all such orbits, or exclude
rotating profiles. The scalar coefficient `omega` is allowed to be nonzero.
-/

namespace ClosedSimilarity
noncomputable section

def profileX (p q theta : ℝ → ℝ) (s : ℝ) : ℝ :=
  q s * Real.cos (theta s) - p s * Real.sin (theta s)

def profileY (p q theta : ℝ → ℝ) (s : ℝ) : ℝ :=
  q s * Real.sin (theta s) + p s * Real.cos (theta s)

theorem profileX_hasDerivAt (k p q theta : ℝ → ℝ) (s : ℝ)
    (hp : HasDerivAt p (-k s * q s) s)
    (hq : HasDerivAt q (1 + k s * p s) s)
    (ht : HasDerivAt theta (k s) s) :
    HasDerivAt (profileX p q theta) (Real.cos (theta s)) s := by
  convert (hq.mul ht.cos).sub (hp.mul ht.sin) using 1 <;>
    first | rfl | ring

theorem profileY_hasDerivAt (k p q theta : ℝ → ℝ) (s : ℝ)
    (hp : HasDerivAt p (-k s * q s) s)
    (hq : HasDerivAt q (1 + k s * p s) s)
    (ht : HasDerivAt theta (k s) s) :
    HasDerivAt (profileY p q theta) (Real.sin (theta s)) s := by
  convert (hq.mul ht.sin).add (hp.mul ht.cos) using 1 <;>
    first | rfl | ring

theorem profile_unit_speed (k p q theta : ℝ → ℝ) (s : ℝ)
    (hp : HasDerivAt p (-k s * q s) s)
    (hq : HasDerivAt q (1 + k s * p s) s)
    (ht : HasDerivAt theta (k s) s) :
    deriv (profileX p q theta) s ^ 2 +
      deriv (profileY p q theta) s ^ 2 = 1 := by
  rw [(profileX_hasDerivAt k p q theta s hp hq ht).deriv,
    (profileY_hasDerivAt k p q theta s hp hq ht).deriv]
  exact Real.cos_sq_add_sin_sq (theta s)

theorem normal_support (p q theta : ℝ → ℝ) (s : ℝ) :
    profileX p q theta s * (-Real.sin (theta s)) +
      profileY p q theta s * Real.cos (theta s) = p s := by
  have h := Real.sin_sq_add_cos_sq (theta s)
  dsimp [profileX, profileY]
  linear_combination p s * h

theorem tangent_support (p q theta : ℝ → ℝ) (s : ℝ) :
    profileX p q theta s * Real.cos (theta s) +
      profileY p q theta s * Real.sin (theta s) = q s := by
  have h := Real.sin_sq_add_cos_sq (theta s)
  dsimp [profileX, profileY]
  linear_combination q s * h

theorem profileX_second_deriv (k p q theta : ℝ → ℝ)
    (hp : ∀ s, HasDerivAt p (-k s * q s) s)
    (hq : ∀ s, HasDerivAt q (1 + k s * p s) s)
    (ht : ∀ s, HasDerivAt theta (k s) s) (s : ℝ) :
    deriv (deriv (profileX p q theta)) s =
      -Real.sin (theta s) * k s := by
  have hd : deriv (profileX p q theta) = fun x => Real.cos (theta x) :=
    funext fun x => (profileX_hasDerivAt k p q theta x (hp x) (hq x) (ht x)).deriv
  rw [hd]
  exact (ht s).cos.deriv

theorem profileY_second_deriv (k p q theta : ℝ → ℝ)
    (hp : ∀ s, HasDerivAt p (-k s * q s) s)
    (hq : ∀ s, HasDerivAt q (1 + k s * p s) s)
    (ht : ∀ s, HasDerivAt theta (k s) s) (s : ℝ) :
    deriv (deriv (profileY p q theta)) s =
      Real.cos (theta s) * k s := by
  have hd : deriv (profileY p q theta) = fun x => Real.sin (theta x) :=
    funext fun x => (profileY_hasDerivAt k p q theta x (hp x) (hq x) (ht x)).deriv
  rw [hd]
  exact (ht s).sin.deriv

theorem profile_signed_curvature (k p q theta : ℝ → ℝ)
    (hp : ∀ s, HasDerivAt p (-k s * q s) s)
    (hq : ∀ s, HasDerivAt q (1 + k s * p s) s)
    (ht : ∀ s, HasDerivAt theta (k s) s) (s : ℝ) :
    deriv (profileX p q theta) s * deriv (deriv (profileY p q theta)) s -
      deriv (profileY p q theta) s * deriv (deriv (profileX p q theta)) s = k s := by
  rw [(profileX_hasDerivAt k p q theta s (hp s) (hq s) (ht s)).deriv,
    (profileY_hasDerivAt k p q theta s (hp s) (hq s) (ht s)).deriv,
    profileX_second_deriv k p q theta hp hq ht,
    profileY_second_deriv k p q theta hp hq ht]
  have h := Real.cos_sq_add_sin_sq (theta s)
  linear_combination k s * h

theorem profile_soliton_equation (omega : ℝ) (k v p q theta : ℝ → ℝ)
    (hk : ∀ s, HasDerivAt k (v s) s)
    (hv : ∀ s, HasDerivAt v (-(k s)^3 / 2 - p s - omega * q s) s)
    (s : ℝ) :
    deriv (deriv k) s + (k s)^3 / 2 =
      -(profileX p q theta s * (-Real.sin (theta s)) +
        profileY p q theta s * Real.cos (theta s)) -
        omega * (profileX p q theta s * Real.cos (theta s) +
          profileY p q theta s * Real.sin (theta s)) := by
  have hdk : deriv k = v := funext fun x => (hk x).deriv
  rw [hdk, (hv s).deriv, normal_support, tangent_support]
  ring

theorem profile_periodic (p q theta : ℝ → ℝ) (L : ℝ) (n : ℤ)
    (hp : Function.Periodic p L) (hq : Function.Periodic q L)
    (ht : ∀ s, theta (s + L) = theta s + n * (2 * Real.pi)) :
    Function.Periodic (profileX p q theta) L ∧
      Function.Periodic (profileY p q theta) L := by
  constructor
  · intro s
    dsimp [profileX]
    rw [hp s, hq s, ht s, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
  · intro s
    dsimp [profileY]
    rw [hp s, hq s, ht s, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

end
end ClosedSimilarity

#print axioms ClosedSimilarity.profile_unit_speed
#print axioms ClosedSimilarity.profile_signed_curvature
#print axioms ClosedSimilarity.profile_soliton_equation
#print axioms ClosedSimilarity.profile_periodic
