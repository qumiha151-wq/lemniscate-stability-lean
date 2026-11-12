import OpenTranslators.BoundedCurvature

/-! Rigidity for the actual Frenet projections of an arbitrary nonzero constant
translation vector. Stress and derivative bounds are derived from the equations. -/

namespace OpenTranslator.ProjectedRigidity
noncomputable section
open Set Filter
open scoped Topology
open OpenTranslator.BoundedCurvature

theorem projected_rigidity {k v f q : ℝ → ℝ} {L K : ℝ}
    (hk : ∀ s, HasDerivAt k (v s) s)
    (hv : ∀ s, HasDerivAt v (-(k s)^3/2+f s) s)
    (hf : ∀ s, HasDerivAt f (k s*q s) s)
    (hq : ∀ s, HasDerivAt q (-k s*f s) s)
    (hL : 0 < L) (hframe : ∀ s, f s^2+q s^2=L)
    (hK : ∀ s, |k s| ≤ K) : (∀ s, k s=0) ∧ (∀ s, f s=0) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  let A := L+1
  let M := K^3/2+A
  let B := 2*K+M
  have hA : 0 < A := by dsimp [A]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbF (s : ℝ) : |f s| ≤ A := by
    have hn := hframe s
    dsimp [A]
    nlinarith [sq_abs (f s), sq_nonneg (|f s|-1), sq_nonneg (q s)]
  have hbQ (s : ℝ) : |q s| ≤ A := by
    have hn := hframe s
    dsimp [A]
    nlinarith [sq_abs (q s), sq_nonneg (|q s|-1), sq_nonneg (f s)]
  have hbK2 (s : ℝ) : k s^2 ≤ K^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hK s) 2
  have hbVprime (s : ℝ) : |-(k s)^3/2+f s| ≤ M := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) (hK s) 3
    calc
      _ ≤ |-(k s)^3/2|+|f s| := abs_add_le _ _
      _ = |k s|^3/2+|f s| := by simp [abs_div, abs_pow]
      _ ≤ M := by dsimp [M]; linarith [hbF s]
  have hbV (s : ℝ) : |v s| ≤ B := derivative_bound_of_bounded_and_second hk hv hK hbVprime s
  let P : ℝ → ℝ := fun s => -v s*f s+(k s)^2/2*q s
  have hP (s : ℝ) : HasDerivAt P (-(f s)^2) s := by
    convert ((hv s).neg.mul (hf s)).add ((((hk s).pow 2).div_const 2).mul (hq s)) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply, Pi.neg_apply]; ring)
  have hPanti : Antitone P := antitone_of_hasDerivAt_nonpos hP
    (fun _ => neg_nonpos.mpr (sq_nonneg _))
  have hPprime (s : ℝ) : HasDerivAt (fun u => -(f u)^2) (-2*f s*k s*q s) s := by
    convert ((hf s).pow 2).neg using 1 <;> first | rfl | ring
  have hbPprime (s : ℝ) : |-2*f s*k s*q s| ≤ 2*A*K*A := by
    calc
      _ = 2*|f s| *|k s| *|q s| := by
        rw [abs_mul, abs_mul, abs_mul, show |(-2:ℝ)|=2 by norm_num]
      _ ≤ (2*A*K)*A := mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left (hbF s) (by norm_num)) (hK s)
          (abs_nonneg _) (by positivity))
        (hbQ s) (abs_nonneg _) (by positivity)
      _ = _ := rfl
  have hPbound (s : ℝ) : |P s| ≤ B*A+K^2/2*A := by
    calc
      _ ≤ |-v s*f s|+|(k s)^2/2*q s| := abs_add_le _ _
      _ = |v s| *|f s|+(k s)^2/2*|q s| := by simp [abs_mul, abs_div, abs_pow, sq_abs]
      _ ≤ B*A+K^2/2*A := add_le_add
        (mul_le_mul (hbV s) (hbF s) (abs_nonneg _) hB)
        (mul_le_mul (by linarith [hbK2 s]) (hbQ s) (abs_nonneg _) (by positivity))
  have hPboundActual (s : ℝ) : |P s| ≤ |v s| *A+(k s)^2/2*A := by
    calc
      _ ≤ |-v s*f s|+|(k s)^2/2*q s| := abs_add_le _ _
      _ = |v s| *|f s|+(k s)^2/2*|q s| := by simp [abs_mul, abs_div, abs_pow, sq_abs]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hbF s) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hbQ s) (by positivity))
  have hfrate (s : ℝ) : HasDerivAt (fun u => k u*q u) (v s*q s-(k s)^2*f s) s := by
    convert (hk s).mul (hq s) using 1 <;> first | rfl | ring
  have hbfrate (s : ℝ) : |v s*q s-(k s)^2*f s| ≤ B*A+K^2*A := by
    calc
      _ ≤ |v s*q s|+|(k s)^2*f s| := abs_sub _ _
      _ = |v s| *|q s|+(k s)^2*|f s| := by simp [abs_mul, abs_pow, sq_abs]
      _ ≤ _ := add_le_add (mul_le_mul (hbV s) (hbQ s) (abs_nonneg _) hB)
        (mul_le_mul (hbK2 s) (hbF s) (abs_nonneg _) (sq_nonneg _))
  have hPend {l : Filter ℝ} {a : ℝ} (hl : l=atTop ∨ l=atBot)
      (hPlim : Tendsto P l (𝓝 a)) : Tendsto P l (𝓝 0) := by
    have hPprimeLim : Tendsto (fun s => -(f s)^2) l (𝓝 0) :=
      derivative_tendsto_zero_end (C := 2*A*K*A) hl hP (by positivity)
        (lipschitz_bound_of_derivative_bound hPprime hbPprime) hPlim
    have hfLim : Tendsto f l (𝓝 0) := by
      apply tendsto_zero_of_square
      simpa only [neg_neg, neg_zero] using hPprimeLim.neg
    have hkqLim : Tendsto (fun s => k s*q s) l (𝓝 0) :=
      derivative_tendsto_zero_end (C := B*A+K^2*A) hl hf (by positivity)
        (lipschitz_bound_of_derivative_bound hfrate hbfrate) hfLim
    have hkfLim : Tendsto (fun s => k s*f s) l (𝓝 0) := by
      have hlim : Tendsto (fun s => K*|f s|) l (𝓝 0) := by
        simpa only [abs_zero, mul_zero] using hfLim.abs.const_mul K
      refine squeeze_zero_norm (fun s => ?_) hlim
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hK s) (abs_nonneg _)
    have hkLim : Tendsto k l (𝓝 0) := by
      have hsum := ((hkfLim.pow 2).add (hkqLim.pow 2)).div_const L
      have he (s : ℝ) : ((k s*f s)^2+(k s*q s)^2)/L=(k s)^2 := by
        rw [show (k s*f s)^2+(k s*q s)^2=(k s)^2*(f s^2+q s^2) by ring,
          hframe s, mul_div_cancel_right₀ _ hL.ne']
      apply tendsto_zero_of_square
      simpa only [he, zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] using hsum
    have hvLim : Tendsto v l (𝓝 0) := derivative_tendsto_zero_end hl hk hM
      (lipschitz_bound_of_derivative_bound hv hbVprime) hkLim
    have hupper : Tendsto (fun s => |v s| *A+(k s)^2/2*A) l (𝓝 0) := by
      simpa only [abs_zero, zero_pow (by decide : 2 ≠ 0), zero_div, zero_mul, zero_add] using
        (hvLim.abs.mul_const A).add (((hkLim.pow 2).div_const 2).mul_const A)
    exact squeeze_zero_norm hPboundActual hupper
  have hbelow : BddBelow (range P) := by
    refine ⟨-(B*A+K^2/2*A), ?_⟩
    rintro u ⟨s, rfl⟩
    exact (abs_le.mp (hPbound s)).1
  have habove : BddAbove (range P) := by
    refine ⟨B*A+K^2/2*A, ?_⟩
    rintro u ⟨s, rfl⟩
    exact (abs_le.mp (hPbound s)).2
  have htop := hPend (Or.inl rfl) (tendsto_atTop_ciInf hPanti hbelow)
  have hbot := hPend (Or.inr rfl) (tendsto_atBot_ciSup hPanti habove)
  have hPzero : P=fun _ => 0 := funext fun s =>
    le_antisymm (hPanti.ge_of_tendsto hbot s) (hPanti.le_of_tendsto htop s)
  have hfzero (s : ℝ) : f s=0 := by
    have hd := hP s
    rw [hPzero] at hd
    exact sq_eq_zero_iff.mp (neg_eq_zero.mp (hd.unique (hasDerivAt_const s (0:ℝ))))
  refine ⟨?_, hfzero⟩
  intro s
  have hd := hf s
  rw [show f=fun _ => 0 from funext hfzero] at hd
  have hkq : k s*q s=0 := hd.unique (hasDerivAt_const s (0:ℝ))
  have hqne : q s ≠ 0 := by
    intro hzero
    have hh := hframe s
    rw [hfzero s, hzero] at hh
    norm_num at hh
    linarith
  exact (mul_eq_zero.mp hkq).resolve_right hqne

end
end OpenTranslator.ProjectedRigidity

#print axioms OpenTranslator.ProjectedRigidity.projected_rigidity

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`OpenTranslator).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"ProjectedRigidity: audited {checked} declarations; standard axioms only."
