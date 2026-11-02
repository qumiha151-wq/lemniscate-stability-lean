import Lemniscate.PeriodicFourierProducts

/-! The natural projection from a covering circle to the original circle,
and the Fourier coefficients of pullback along this projection. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T S : ℝ)

noncomputable def circleCoverProjection (M : ℕ) (hS : S = (M:ℝ)*T) :
    C(AddCircle S, AddCircle T) where
  toFun := QuotientAddGroup.map (AddSubgroup.zmultiples S) (AddSubgroup.zmultiples T)
    (AddMonoidHom.id ℝ) (by
      intro x hx
      obtain ⟨n,rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      change n • S ∈ AddSubgroup.zmultiples T
      rw [hS, ← nsmul_eq_mul]
      exact AddSubgroup.zsmul_mem _
        (AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples T) M) n)
  continuous_toFun := (AddCircle.continuous_mk' T).quotient_lift _

noncomputable def circlePeriodicExtension (M : ℕ) (hS : S = (M:ℝ)*T) :
    C(AddCircle T, ℂ) →ₐ[ℂ] C(AddCircle S, ℂ) :=
  ContinuousMap.compRightAlgHom ℂ ℂ (circleCoverProjection T S M hS)

theorem circle_periodic_extension_coe (M : ℕ) (hS : S = (M:ℝ)*T)
    (f : C(AddCircle T, ℂ)) (x : ℝ) :
    circlePeriodicExtension T S M hS f (x:AddCircle S) = f (x:AddCircle T) := rfl

theorem circle_periodic_extension_deriv (M : ℕ) (hS : S = (M:ℝ)*T)
    (f g : C(AddCircle T, ℂ)) (hd : HasCircleDeriv T f g) :
    HasCircleDeriv S (circlePeriodicExtension T S M hS f)
      (circlePeriodicExtension T S M hS g) := by
  intro x
  exact hd x

theorem circle_periodic_extension_real (M : ℕ) (hS : S = (M:ℝ)*T)
    (f : C(AddCircle T, ℂ)) (hf : ∀ x, conj (f x) = f x) :
    ∀ x, conj (circlePeriodicExtension T S M hS f x) =
      circlePeriodicExtension T S M hS f x := fun _ => hf _

variable [Fact (0 < T)] [Fact (0 < S)]

omit [Fact (0 < S)] in
theorem circle_periodic_extension_fourier_mode (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (n : ℤ) :
    circlePeriodicExtension T S M hS (fourier n) = fourier ((M:ℤ)*n) := by
  ext x
  induction x using QuotientAddGroup.induction_on
  rename_i x
  rw [circle_periodic_extension_coe, fourier_coe_apply, fourier_coe_apply]
  congr 1
  have hMC : (M:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hTC : (T:ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Fact.out : 0 < T))
  rw [hS]
  push_cast
  field_simp

theorem circle_periodic_extension_fourier (M : ℕ) (hM : 0 < M)
    (hS : S = (M:ℝ)*T) (f : C(AddCircle T, ℂ)) (m : ℤ) :
    fourierCoeff (circlePeriodicExtension T S M hS f) m =
      if (M:ℤ) ∣ m then fourierCoeff f (m/(M:ℤ)) else 0 := by
  let F := (circleFourierCLM S m).comp
    (ContinuousMap.compCLM ℂ ℂ (circleCoverProjection T S M hS))
  let G : C(AddCircle T, ℂ) →L[ℂ] ℂ :=
    if (M:ℤ) ∣ m then circleFourierCLM T (m/(M:ℤ)) else 0
  have hM0 : (M:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hFG : F = G := by
    apply ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top)
    rintro _ ⟨k,rfl⟩
    dsimp only [F,ContinuousLinearMap.comp_apply,ContinuousMap.compCLM_apply]
    rw [circle_fourier_clm_apply]
    change fourierCoeff (circlePeriodicExtension T S M hS (fourier k)) m = G (fourier k)
    rw [circle_periodic_extension_fourier_mode T S M hM hS,
      circle_continuous_fourier_mode]
    by_cases hm : (M:ℤ) ∣ m
    · simp only [G,if_pos hm,circle_fourier_clm_apply,circle_continuous_fourier_mode]
      have hi : m = (M:ℤ)*k ↔ m/(M:ℤ) = k := by
        obtain ⟨a,rfl⟩ := hm
        rw [Int.mul_ediv_cancel_left _ hM0]
        exact ⟨mul_left_cancel₀ hM0,congrArg (fun b : ℤ => (M:ℤ)*b)⟩
      simp only [hi]
    · simp only [G,if_neg hm,zero_apply]
      exact if_neg (fun h => hm ⟨k,h⟩)
  have heq := congrArg (fun L : C(AddCircle T, ℂ) →L[ℂ] ℂ => L f) hFG
  by_cases hm : (M:ℤ) ∣ m <;>
    simpa [F,G,hm,circlePeriodicExtension,circle_fourier_clm_apply] using heq

end Lemniscate
