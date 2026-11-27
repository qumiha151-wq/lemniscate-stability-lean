import Migration.LowDefectModes
import Migration.LowDefectTangentMoments

noncomputable section
namespace MigrationGeometry.Flow.LowDefect

theorem leakage_from_moments {p : ℤ→ℝ} {D : ℝ} (pos : ∀n,0≤p n)
    (p0 : p 0=0) (hp : HasSum p 1)
    (hn : HasSum (fun n : ℤ=>(n:ℝ)*p n) 1)
    (hd : HasSum (fun n : ℤ=>((n:ℝ)-1)^2*p n) D) :
    0 ≤ 1-p 1 ∧ 1-p 1 ≤ D/2 ∧ 1-p 1 ≤ D/4+3*p 2/4 := by
  have s1 : HasSum (fun n : ℤ=>if n=1 then p 1 else 0) (p 1) := by
    simpa [eq_comm] using hasSum_ite_eq (1:ℤ) (p 1)
  have s2 : HasSum (fun n : ℤ=>if n=2 then p 2 else 0) (p 2) := by
    simpa [eq_comm] using hasSum_ite_eq (2:ℤ) (p 2)
  have w := hp.sub s1
  have zle (n : ℤ) : (if n=1 then p 1 else 0) ≤ p n := by
    split_ifs with h
    · simp [h]
    · exact pos n
  have nn := hasSum_le zle s1 hp
  have sw : HasSum (fun n : ℤ=>(n:ℝ)*((n:ℝ)-1)*p n) D := by
    convert! hd.add (hn.sub hp) using 1
    · funext n;ring
    · ring
  have lb (n : ℤ) : 2*(p n-(if n=1 then p 1 else 0)) ≤ (n:ℝ)*((n:ℝ)-1)*p n := by
    by_cases e1 : n=1
    · simp [e1]
    rw [if_neg e1,sub_zero]
    by_cases e0 : n=0
    · simp [e0,p0]
    have f : (2:ℝ)≤(n:ℝ)*((n:ℝ)-1) := by
      by_cases n2 : 2≤n
      · have b : (2:ℝ)≤n := by exact_mod_cast n2
        nlinarith [mul_nonneg (show 0≤(n:ℝ)-2 by linarith) (show 0≤(n:ℝ)+1 by linarith)]
      · have b : (n:ℝ)≤-1 := by exact_mod_cast (show n≤ -1 by omega)
        nlinarith [mul_nonneg_of_nonpos_of_nonpos (show (n:ℝ)-2≤0 by linarith) (show (n:ℝ)+1≤0 by linarith)]
    exact mul_le_mul_of_nonneg_right f (pos n)
  have crude := hasSum_le lb (w.mul_left 2) sw
  have floor (n : ℤ) : 4*(p n-(if n=1 then p 1 else 0)) -
      3*(if n=2 then p 2 else 0) ≤ ((n:ℝ)-1)^2*p n := by
    by_cases e1 : n=1
    · simp [e1]
    by_cases e2 : n=2
    · subst n;norm_num;ring_nf;linarith
    rw [if_neg e1,if_neg e2,mul_zero,sub_zero,sub_zero]
    by_cases e0 : n=0
    · simp [e0,p0]
    have b : 4≤((n:ℝ)-1)^2 := by
      rcases lt_or_ge n 0 with h|h
      · have a : (n:ℝ)≤-1 := by exact_mod_cast (show n≤ -1 by omega)
        nlinarith [mul_nonneg_of_nonpos_of_nonpos (show (n:ℝ)+1≤0 by linarith)
          (show (n:ℝ)-3≤0 by linarith)]
      · have a : (3:ℝ)≤n := by exact_mod_cast (show 3≤n by omega)
        nlinarith [mul_nonneg (show 0≤(n:ℝ)+1 by linarith) (show 0≤(n:ℝ)-3 by linarith)]
    exact mul_le_mul_of_nonneg_right b (pos n)
  have gap := hasSum_le floor ((w.mul_left 4).sub (s2.mul_left 3)) hd
  exact ⟨by linarith,by linarith,by linarith⟩

end MigrationGeometry.Flow.LowDefect
#print axioms MigrationGeometry.Flow.LowDefect.leakage_from_moments
