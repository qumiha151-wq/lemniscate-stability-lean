import Migration.LowDefectMaterialModes
import Migration.LowDefectModes

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.LowDefect.Tangent

theorem position_coefficient {G T : ℝ→ℂ} (ct : Continuous T)
    (dg : ∀ x, HasDerivAt G ((2*Real.pi:ℂ)*T x) x)
    (per : G 1=G 0) {n : ℤ} (hn : n≠0) :
    coeff G n=(-Complex.I/(n:ℂ))*coeff T n := by
  have hd := coeff_der dg (continuous_const.mul ct) per n
  have cs : coeff (fun x=>(2*Real.pi:ℂ)*T x) n=(2*Real.pi:ℂ)*coeff T n :=
    fourierCoeffOn.const_mul _ _ _ (by norm_num : (0:ℝ)<1)
  rw [cs] at hd
  have n0 : (n:ℂ)≠0 := by exact_mod_cast hn
  have pi0 : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  unfold omega at hd
  push_cast at hd
  apply (mul_left_cancel₀ (show (2:ℂ)*Real.pi*Complex.I*(n:ℂ)≠0 by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) pi0) Complex.I_ne_zero) n0))
  calc _ = (2*Real.pi:ℂ)*coeff T n := by linear_combination -hd
       _ = _ := by field_simp [n0]; ring_nf; simp [Complex.I_sq]

theorem normal_correction_moment {G T : ℝ→ℂ} {D : ℝ} (ct : Continuous T)
    (dg : ∀ x, HasDerivAt G ((2*Real.pi:ℂ)*T x) x) (per : G 1=G 0)
    (g0 : coeff G 0=0) (t0 : coeff T 0=0)
    (hm : HasSum (energy T) 1)
    (h1 : HasSum (fun n : ℤ=>(n:ℝ)*energy T n) 1)
    (h2 : HasSum (fun n : ℤ=>((n:ℝ)-1)^2*energy T n) D) :
    (∫x in (0:ℝ)..1,‖G x+Complex.I*T x‖^2) ≤
      5/9*D+7/12*energy T 2 := by
  let Z := fun x=>G x+Complex.I*T x
  have cg : Continuous G := continuous_iff_continuousAt.mpr fun x=>(dg x).continuousAt
  have cz : Continuous Z := cg.add (continuous_const.mul ct)
  have coeffZ (n : ℤ) : coeff Z n=coeff G n+Complex.I*coeff T n := by
    have e : Z=fun x=>G x-(-Complex.I*T x) := by funext x;dsimp [Z];ring
    have c := coeff_sub cg (continuous_const.mul ct : Continuous (fun x=> -Complex.I*T x)) n
    change coeff (fun x=>G x-(-Complex.I*T x)) n=coeff G n-coeff (fun x=> -Complex.I*T x) n at c
    rw [e,c]
    have s : coeff (fun x=> -Complex.I*T x) n= -Complex.I*coeff T n :=
      fourierCoeffOn.const_mul _ _ _ (by norm_num : (0:ℝ)<1)
    rw [s];ring
  have energyZ (n : ℤ) (hn : n≠0) : energy Z n=(1-1/(n:ℝ))^2*energy T n := by
    have h : coeff Z n=(((1-1/(n:ℝ)):ℝ):ℂ)*Complex.I*coeff T n := by
      rw [coeffZ,position_coefficient ct dg per hn]
      push_cast;ring
    unfold energy
    rw [h,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one,mul_pow,sq_abs]
  have s2 : HasSum (fun n : ℤ=>if n=2 then energy T 2 else 0) (energy T 2) := by
    simpa [eq_comm] using hasSum_ite_eq (2:ℤ) (energy T 2)
  have hs := ((h2.mul_left (5/9:ℝ)).sub ((h1.sub hm).mul_left (8/9:ℝ))).add (s2.mul_left (7/12:ℝ))
  have bound (n : ℤ) : energy Z n ≤ (5/9)*(((n:ℝ)-1)^2*energy T n)-
      (8/9)*((n:ℝ)*energy T n-energy T n)+(7/12)*(if n=2 then energy T 2 else 0) := by
    by_cases zero : n=0
    · subst n
      simp [energy,coeffZ,g0,t0]
    · rw [energyZ n zero]
      by_cases two : n=2
      · subst n; norm_num;ring_nf;linarith
      · rw [if_neg two,mul_zero,add_zero]
        have pos : 0≤energy T n := sq_nonneg _
        nlinarith only [mul_le_mul_of_nonneg_right (LowDefect.normal_weight zero two) pos]
  have endp := hasSum_le bound (parseval Z cz) hs
  simpa [Z] using endp

end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.normal_correction_moment
