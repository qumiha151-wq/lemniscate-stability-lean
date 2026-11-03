import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact L2 energy identity for finite diagonal parabolic systems.

For Fourier Galerkin equations the positive eigenvalues are
lambda_n = 1 + 4 * omega_n^4. The identity controls the time derivative,
the fourth spatial derivative and the H2 trace with constants independent of
the number of modes. All derivatives and integrals below are actual derivatives
and Lebesgue integrals, rather than an assumed energy identity.
-/
namespace Lemniscate
open MeasureTheory
open scoped RealInnerProductSpace

private theorem scalar_parabolic_energy (u v : ℝ → ℂ) (a t : ℝ)
    (hd : ∀ s, HasDerivAt u (v s) s) (hv : Continuous v) :
    (∫ s in (0:ℝ)..t, ‖v s‖^2+a^2*‖u s‖^2)+a*‖u t‖^2 =
      (∫ s in (0:ℝ)..t, ‖v s+a • u s‖^2)+a*‖u 0‖^2 := by
  have hu : Continuous u :=
    continuous_iff_continuousAt.mpr (fun s => (hd s).continuousAt)
  let D : ℝ → ℝ := fun s => ‖v s‖^2+a^2*‖u s‖^2
  let C : ℝ → ℝ := fun s => 2*inner ℝ (u s) (v s)
  have hD : Continuous D := (hv.norm.pow 2).add
    (continuous_const.mul (hu.norm.pow 2))
  have hC : Continuous C := continuous_const.mul (hu.inner hv)
  have hexpand (s : ℝ) : ‖v s+a • u s‖^2 = D s+a*C s := by
    rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,real_inner_comm (u s) (v s)]
    dsimp only [D,C]
    ring
  have hFTC : (∫ s in (0:ℝ)..t, C s) = ‖u t‖^2-‖u 0‖^2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (hd s).norm_sq) (hC.intervalIntegrable 0 t)
  have hsplit : (∫ s in (0:ℝ)..t, ‖v s+a • u s‖^2) =
      (∫ s in (0:ℝ)..t, D s)+a*(∫ s in (0:ℝ)..t, C s) := by
    have hAC : IntervalIntegrable (fun s : ℝ => a*C s) volume 0 t :=
      (hC.intervalIntegrable 0 t).const_mul a
    simp_rw [hexpand]
    rw [intervalIntegral.integral_add (hD.intervalIntegrable 0 t) hAC,
      intervalIntegral.integral_const_mul]
  rw [hFTC] at hsplit
  change (∫ s in (0:ℝ)..t, D s)+a*‖u t‖^2 = _
  linarith only [hsplit]

private theorem finite_parabolic_energy_identity {ι : Type*} [Fintype ι]
    (u v : ι → ℝ → ℂ) (a : ι → ℝ) (t : ℝ)
    (hd : ∀ i s, HasDerivAt (u i) (v i s) s) (hv : ∀ i, Continuous (v i)) :
    (∫ s in (0:ℝ)..t, ∑ i, (‖v i s‖^2+(a i)^2*‖u i s‖^2))+
        (∑ i, a i*‖u i t‖^2) =
      (∫ s in (0:ℝ)..t, ∑ i, ‖v i s+a i • u i s‖^2)+
        (∑ i, a i*‖u i 0‖^2) := by
  have hu (i : ι) : Continuous (u i) :=
    continuous_iff_continuousAt.mpr (fun s => (hd i s).continuousAt)
  have hsum :
      (∑ i, ((∫ s in (0:ℝ)..t, ‖v i s‖^2+(a i)^2*‖u i s‖^2)+
        a i*‖u i t‖^2)) =
      (∑ i, ((∫ s in (0:ℝ)..t, ‖v i s+a i • u i s‖^2)+
        a i*‖u i 0‖^2)) :=
    Finset.sum_congr rfl (fun i _ => scalar_parabolic_energy (u i) (v i)
      (a i) t (hd i) (hv i))
  have hDi (i : ι) :
      IntervalIntegrable (fun s : ℝ => ‖v i s‖^2+(a i)^2*‖u i s‖^2) volume 0 t :=
    (((hv i).norm.pow 2).add
      (continuous_const.mul ((hu i).norm.pow 2))).intervalIntegrable 0 t
  have hFi (i : ι) :
      IntervalIntegrable (fun s : ℝ => ‖v i s+a i • u i s‖^2) volume 0 t :=
    (((hv i).add ((hu i).const_smul (a i))).norm.pow 2).intervalIntegrable 0 t
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i s => ‖v i s‖^2+(a i)^2*‖u i s‖^2) (fun i _ => hDi i),
      intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun i s => ‖v i s+a i • u i s‖^2) (fun i _ => hFi i)]
  simpa only [Finset.sum_add_distrib] using hsum

/-- Exact parabolic energy and a bound uniform in time and in the number of
Fourier modes. Real scalar multiplication on complex modes is the usual
multiplication by `(lambda : Complex)`. -/
theorem finite_mode_parabolic_energy {ι : Type*} [Fintype ι]
    (u v : ι → ℝ → ℂ) (a : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (ha : ∀ i, 0 < a i)
    (hd : ∀ i s, HasDerivAt (u i) (v i s) s) (hv : ∀ i, Continuous (v i)) :
    let D : ℝ → ℝ := fun s => ∑ i, (‖v i s‖^2+(a i)^2*‖u i s‖^2)
    let F : ℝ → ℝ := fun s => ∑ i, ‖v i s+a i • u i s‖^2
    let E : ℝ → ℝ := fun s => ∑ i, a i*‖u i s‖^2
    (∫ s in (0:ℝ)..t, D s)+E t = (∫ s in (0:ℝ)..t, F s)+E 0 ∧
      ∀ s ∈ Set.Icc (0:ℝ) t,
        (∫ r in (0:ℝ)..t, D r)+E s ≤ 2*((∫ r in (0:ℝ)..t, F r)+E 0) := by
  let D : ℝ → ℝ := fun s => ∑ i, (‖v i s‖^2+(a i)^2*‖u i s‖^2)
  let F : ℝ → ℝ := fun s => ∑ i, ‖v i s+a i • u i s‖^2
  let E : ℝ → ℝ := fun s => ∑ i, a i*‖u i s‖^2
  have hid (s : ℝ) : (∫ r in (0:ℝ)..s, D r)+E s =
      (∫ r in (0:ℝ)..s, F r)+E 0 :=
    finite_parabolic_energy_identity u v a s hd hv
  have hE (s : ℝ) : 0 ≤ E s :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i).le (sq_nonneg _))
  have hD (s : ℝ) : 0 ≤ D s :=
    Finset.sum_nonneg (fun i _ => add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hF (s : ℝ) : 0 ≤ F s := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hu (i : ι) : Continuous (u i) :=
    continuous_iff_continuousAt.mpr (fun s => (hd i s).continuousAt)
  have hFc : Continuous F := continuous_finsetSum _ (fun i _ =>
    (((hv i).add ((hu i).const_smul (a i))).norm.pow 2))
  refine ⟨hid t,?_⟩
  intro s hs
  have hDint : 0 ≤ ∫ r in (0:ℝ)..s, D r :=
    intervalIntegral.integral_nonneg_of_forall hs.1 hD
  have hFmono : (∫ r in (0:ℝ)..s, F r) ≤ ∫ r in (0:ℝ)..t, F r :=
    intervalIntegral.integral_mono_interval (le_refl (0:ℝ)) hs.1 hs.2
      (ae_of_all _ hF) (hFc.intervalIntegrable 0 t)
  linarith only [hid t,hid s,hE t,hDint,hFmono]

end Lemniscate
