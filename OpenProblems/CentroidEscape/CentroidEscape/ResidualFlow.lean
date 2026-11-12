import CentroidEscape.ValidatedIntegration

/-!
# Error control from finite approximate trajectories

The approximate path may be a finite Taylor polynomial. Its derivative
residual is enough; no infinite series or local exact reference arc is used.
-/
namespace CentroidEscape
noncomputable section
open Set Real
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exp_sub_one_le_mul_exp (x : ℝ) : exp x - 1 ≤ x * exp x := by
  have h := mul_le_mul_of_nonneg_right (add_one_le_exp (-x)) (exp_pos x).le
  rw [← exp_add, neg_add_cancel, exp_zero] at h
  nlinarith

lemma gronwallBound_le_residual (δ K ε h : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε) :
    gronwallBound δ K ε h ≤ δ*exp (K*h) + ε*h*exp (K*h) := by
  by_cases hz : K = 0
  · simp [hz, gronwallBound_K0]
  · rw [gronwallBound_of_K_ne_0 hz]
    have hpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    have he := mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (K*h))
      (div_nonneg hε hK)
    have halg : ε/K*(K*h*exp (K*h)) = ε*h*exp (K*h) := by
      field_simp
    linarith

theorem approximate_step_error (f : E → E) (K : ℝ≥0) (a b ε : ℝ)
    (hab : a ≤ b) (hε : 0 ≤ ε) (z p pd : ℝ → E)
    (hLip : LipschitzWith K f)
    (hz : ContinuousOn z (Icc a b))
    (hz' : ∀ t ∈ Ico a b, HasDerivAt z (f (z t)) t)
    (hp : ContinuousOn p (Icc a b))
    (hp' : ∀ t ∈ Ico a b, HasDerivAt p (pd t) t)
    (hres : ∀ t ∈ Ico a b, dist (pd t) (f (p t)) ≤ ε) :
    dist (z b) (p b) ≤ dist (z a) (p a)*exp ((K:ℝ)*(b-a)) +
      ε*(b-a)*exp ((K:ℝ)*(b-a)) := by
  have hb := dist_le_of_approx_trajectories_ODE
    (v := fun _ => f) (K := K) (εf := 0) (εg := ε)
    (fun _ => hLip) hz (fun t ht => (hz' t ht).hasDerivWithinAt)
    (fun t ht => by simp) hp (fun t ht => (hp' t ht).hasDerivWithinAt)
    hres (δ := dist (z a) (p a)) le_rfl b ⟨hab, le_rfl⟩
  simp only [zero_add] at hb
  exact hb.trans (gronwallBound_le_residual _ _ _ _ K.coe_nonneg hε)

theorem approximate_grid_error (f : E → E) (K : ℝ≥0)
    (h ε : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (N : ℕ)
    (z : ℝ → E) (c : ℕ → E) (p pd : ℕ → ℝ → E)
    (hLip : LipschitzWith K f) (hinit : z 0 = c 0)
    (hz : ∀ j < N, ContinuousOn z (Icc (j*h) ((j+1)*h)))
    (hz' : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), HasDerivAt z (f (z t)) t)
    (hp : ∀ j < N, ContinuousOn (p j) (Icc (j*h) ((j+1)*h)))
    (hp' : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), HasDerivAt (p j) (pd j t) t)
    (hres : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), dist (pd j t) (f (p j t)) ≤ ε)
    (hp0 : ∀ j < N, p j (j*h) = c j)
    (hp1 : ∀ j < N, p j ((j+1)*h) = c (j+1)) :
    ∀ n ≤ N, dist (z (n*h)) (c n) ≤ n*ε*h*exp ((K:ℝ)*(n*h)) := by
  intro n hn
  induction n with
  | zero => simp [hinit]
  | succ n ih =>
    have hnN : n < N := Nat.lt_of_succ_le hn
    have hind := ih (Nat.le_of_lt hnN)
    have hs := approximate_step_error f K (n*h) ((n+1)*h) ε (by nlinarith) hε
      z (p n) (pd n) hLip (hz n hnN) (hz' n hnN) (hp n hnN) (hp' n hnN) (hres n hnN)
    rw [hp0 n hnN, hp1 n hnN, show (n+1:ℝ)*h-n*h=h by ring] at hs
    have he : exp ((K:ℝ)*(n*h))*exp ((K:ℝ)*h) = exp ((K:ℝ)*((n+1)*h)) := by
      rw [← exp_add]; congr 1; ring
    have he2 : exp ((K:ℝ)*h) ≤ exp ((K:ℝ)*((n+1)*h)) := by
      apply exp_le_exp.mpr
      nlinarith [mul_nonneg K.coe_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hh)]
    have hnn : 0 ≤ ε*h := mul_nonneg hε hh
    calc
      dist (z ((n.succ:ℝ)*h)) (c n.succ)
          ≤ dist (z (n*h)) (c n)*exp ((K:ℝ)*h)+ε*h*exp ((K:ℝ)*h) := by
            simpa only [Nat.cast_succ] using hs
      _ ≤ n*ε*h*exp ((K:ℝ)*(n*h))*exp ((K:ℝ)*h)+ε*h*exp ((K:ℝ)*((n+1)*h)) :=
        add_le_add (mul_le_mul_of_nonneg_right hind (exp_pos _).le)
          (mul_le_mul_of_nonneg_left he2 hnn)
      _ = (n.succ:ℝ)*ε*h*exp ((K:ℝ)*((n.succ:ℝ)*h)) := by
        rw [mul_assoc (n*ε*h), he, Nat.cast_succ]
        ring

/-- Existence and error control are obtained together from a bounded clipped
field and approximate arcs. A true trajectory remaining in a tube is not
assumed. Showing clipping is inactive remains a separate concrete check. -/
theorem exists_approximate_grid_solution [CompleteSpace E]
    (f : E → E) (K M : ℝ≥0) (h ε : ℝ) (hh : 0 ≤ h) (hε : 0 ≤ ε) (N : ℕ)
    (c : ℕ → E) (p pd : ℕ → ℝ → E)
    (hLip : LipschitzWith K f) (hbound : ∀ y, ‖f y‖ ≤ M)
    (hp : ∀ j < N, ContinuousOn (p j) (Icc (j*h) ((j+1)*h)))
    (hp' : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), HasDerivAt (p j) (pd j t) t)
    (hres : ∀ j < N, ∀ t ∈ Ico (j*h) ((j+1)*h), dist (pd j t) (f (p j t)) ≤ ε)
    (hp0 : ∀ j < N, p j (j*h) = c j)
    (hp1 : ∀ j < N, p j ((j+1)*h) = c (j+1)) :
    ∃ z : ℝ → E, z 0 = c 0 ∧
      (∀ t ∈ Icc 0 (N*h), HasDerivAt z (f (z t)) t) ∧
      (∀ n ≤ N, dist (z (n*h)) (c n) ≤ n*ε*h*exp ((K:ℝ)*(n*h))) := by
  obtain ⟨z, hz0, hz⟩ := exists_ode_on_finite_interval f K M (c 0) (N*h)
    (mul_nonneg (Nat.cast_nonneg N) hh) hLip hbound
  have hsub : ∀ j < N, Icc ((j:ℝ)*h) ((j+1)*h) ⊆ Icc 0 ((N:ℝ)*h) := by
    intro j hj t ht
    have hjN : (j:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
    constructor
    · exact (mul_nonneg (Nat.cast_nonneg j) hh).trans ht.1
    · exact ht.2.trans (mul_le_mul_of_nonneg_right hjN hh)
  refine ⟨z, hz0, hz, ?_⟩
  apply approximate_grid_error f K h ε hh hε N z c p pd hLip hz0
  · intro j hj t ht
    exact (hz t (hsub j hj ht)).continuousAt.continuousWithinAt
  · intro j hj t ht
    exact hz t (hsub j hj (Ico_subset_Icc_self ht))
  · exact hp
  · exact hp'
  · exact hres
  · exact hp0
  · exact hp1

end
end CentroidEscape

#print axioms CentroidEscape.approximate_grid_error
