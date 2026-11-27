import SolitonClassification.LemniscaticDuplicate
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

noncomputable section
open Function Filter Set Complex Metric
open scoped Topology
namespace ClosedSimilarity.LemniscaticExtension
set_option backward.isDefEq.respectTransparency false

private abbrev inside (r : ℝ) (z : ℂ) (n : ℕ) := ‖z‖<(2:ℝ)^n*r
theorem find_inside {r : ℝ} (rp : 0<r) (z : ℂ) : ∃n,inside r z n := by
  obtain ⟨n,h⟩ := pow_unbounded_of_one_lt (‖z‖/r) (show (1:ℝ)<2 by norm_num)
  exact ⟨n,(div_lt_iff₀ rp).mp h⟩

private theorem inside_mono {r : ℝ} (rp : 0<r) {z : ℂ} {n m : ℕ}
    (h : inside r z n) (le : n≤m) : inside r z m :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) le) rp.le)

theorem small_of_inside {r : ℝ} {z : ℂ} {n : ℕ} (h : inside r z n) :
    z/(2:ℂ)^n∈ball (0:ℂ) r := by
  rw [mem_ball_zero_iff,norm_div,norm_pow,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  exact (div_lt_iff₀ (by positivity)).mpr (by simpa only [inside,mul_comm] using h)

def approx (seed : ℂ→ℂ × ℂ) (n : ℕ) (z : ℂ) :=
  (double^[n]) (seed (z/(2:ℂ)^n))

private theorem approx_compat {seed : ℂ→ℂ × ℂ} {r : ℝ} (rp : 0<r)
    (localLaw : ∀z∈ball (0:ℂ) r,double (seed (z/2))=seed z)
    {z : ℂ} {n m : ℕ} (small : inside r z n) (le : n≤m) :
    approx seed m z=approx seed n z := by
  induction m, le using Nat.le_induction with
  | base => rfl
  | succ m le ih =>
    rw [approx,Function.iterate_succ_apply,pow_succ,
      show z/(2^m*2:ℂ)=z/2^m/2 by ring,
      localLaw _ (small_of_inside (inside_mono rp small le))]
    exact ih

def global (seed : ℂ→ℂ × ℂ) {r : ℝ} (rp : 0<r) (z : ℂ) :=
  approx seed (Nat.find (find_inside rp z)) z

theorem global_eq_approx {seed : ℂ→ℂ × ℂ} {r : ℝ} (rp : 0<r)
    (localLaw : ∀z∈ball (0:ℂ) r,double (seed (z/2))=seed z)
    {z : ℂ} {n : ℕ} (small : ‖z‖<(2:ℝ)^n*r) :
    global seed rp z=approx seed n z :=
  (approx_compat rp localLaw (Nat.find_spec (find_inside rp z)) (Nat.find_min' _ small)).symm

theorem global_locally_approx {seed : ℂ→ℂ × ℂ} {r : ℝ} (rp : 0<r)
    (localLaw : ∀z∈ball (0:ℂ) r,double (seed (z/2))=seed z)
    {z : ℂ} {n : ℕ} (small : ‖z‖<(2:ℝ)^n*r) :
    global seed rp=ᶠ[𝓝 z] approx seed n := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt_const small] with p hp
  exact global_eq_approx rp localLaw hp

private theorem iterate_merom {f g : ℂ→ℂ} {z : ℂ} (hf : MeromorphicAt f z)
    (hg : MeromorphicAt g z) (n : ℕ) :
    MeromorphicAt (fun t=>((double^[n]) (f t,g t)).1) z ∧
    MeromorphicAt (fun t=>((double^[n]) (f t,g t)).2) z := by
  induction n with
  | zero => exact ⟨hf,hg⟩
  | succ n ih =>
    simp_rw [Function.iterate_succ_apply']
    exact ⟨((((MeromorphicAt.const 2 z).mul ih.1).mul ih.2).div ((MeromorphicAt.const 1 z).add (ih.1.pow 4))),
      ((((MeromorphicAt.const 1 z).sub ((MeromorphicAt.const 6 z).mul (ih.1.pow 4))).add (ih.1.pow 8)).div
        (((MeromorphicAt.const 1 z).add (ih.1.pow 4)).pow 2))⟩

theorem global_meromorphic {seed : ℂ→ℂ × ℂ} {r : ℝ} (rp : 0<r)
    (hol : ∀z∈ball (0:ℂ) r,AnalyticAt ℂ (fun t=>(seed t).1) z ∧
      AnalyticAt ℂ (fun t=>(seed t).2) z)
    (localLaw : ∀z∈ball (0:ℂ) r,double (seed (z/2))=seed z) :
    Meromorphic (fun t=>(global seed rp t).1) ∧ Meromorphic (fun t=>(global seed rp t).2) := by
  have both (z : ℂ) : MeromorphicAt (fun t=>(global seed rp t).1) z ∧
      MeromorphicAt (fun t=>(global seed rp t).2) z := by
    obtain ⟨n,good⟩ := find_inside rp z
    have eq := global_locally_approx rp localLaw good
    have comp : AnalyticAt ℂ (fun p:ℂ=>p/2^n) z := by fun_prop
    obtain ⟨h1,h2⟩ := hol _ (small_of_inside good)
    obtain ⟨p,q⟩ := iterate_merom (h1.comp (f:=fun p:ℂ=>p/2^n) comp).meromorphicAt (h2.comp (f:=fun p:ℂ=>p/2^n) comp).meromorphicAt n
    exact ⟨p.congr ((eq.fun_comp Prod.fst).symm.filter_mono nhdsWithin_le_nhds),
      q.congr ((eq.fun_comp Prod.snd).symm.filter_mono nhdsWithin_le_nhds)⟩
  exact ⟨fun z=>(both z).1,fun z=>(both z).2⟩

end ClosedSimilarity.LemniscaticExtension
