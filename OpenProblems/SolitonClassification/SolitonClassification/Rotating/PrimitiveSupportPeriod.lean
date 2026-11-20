import SolitonClassification.Rotating.RotatingPeriodicFlow
import Mathlib.GroupTheory.Archimedean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Round

/-! A finite prime-divisor certificate for the primitive period of the
actual rotating support state. -/
noncomputable section
open Set Function
namespace SolitonClassification.Rotating.PrimitiveSupportPeriod

def periods {Y : Type*} (z : ℝ → Y) : AddSubgroup ℝ where
  carrier := {s | Periodic z s}
  zero_mem' := by intro x; simp
  add_mem' := fun h₁ h₂ => h₁.add_period h₂
  neg_mem' := fun h => h.neg

theorem primitive_of_prime_checks {Y : Type*} (z : ℝ → Y) {P : ℝ}
    (hp : 0 < P) (hcap : P < 64) (hz : Periodic z P)
    (hsmall : ∀ s : ℝ, 0 < s → s ≤ 1/40 → z s ≠ z 0)
    (htest : ∀ p : ℕ, p.Prime → p ≤ 2560 → z (P / p) ≠ z 0) :
    IsLeast {s : ℝ | Periodic z s ∧ 0 < s} P := by
  let S := periods z
  have hP : P ∈ S := hz
  have hdis : Disjoint (S : Set ℝ) (Ioo 0 (1/40)) := by
    apply Set.disjoint_left.mpr
    intro s hs ht
    exact hsmall s ht.1 ht.2.le (by simpa using (show Periodic z s from hs) 0)
  have hbot : S ≠ ⊥ := by
    intro hh
    rw [hh] at hP
    exact hp.ne' (by simpa using hP)
  have hε : (0:ℝ) < 1/40 := by norm_num
  have hleast := AddSubgroup.exists_isLeast_pos hbot hε hdis
  obtain ⟨d,hd⟩ := hleast
  have hmin : Periodic z d := hd.1.1
  have hdp : 0 < d := hd.1.2
  have hdlo : 1/40 < d := by
    by_contra! hn
    exact hsmall _ hdp hn (by simpa using hmin 0)
  have hgen := AddSubgroup.cyclic_of_min hd
  rw [hgen, AddSubgroup.mem_closure_singleton] at hP
  obtain ⟨n,hn⟩ := hP
  rw [zsmul_eq_mul] at hn
  have hns : 0 < (n:ℝ) := by
    by_contra! h
    linarith only [mul_nonpos_of_nonpos_of_nonneg h hdp.le,hn,hp]
  have hn0 : 0 ≤ n := by exact_mod_cast hns.le
  lift n to ℕ using hn0
  norm_cast at hn hns
  have hncap : n ≤ 2560 := by
    have : (n:ℝ) < 2560 := by
      nlinarith [mul_le_mul_of_nonneg_left hdlo.le (show (0:ℝ) ≤ n by positivity)]
    exact_mod_cast this.le
  have hone : n=1 := by
    by_contra hn1
    obtain ⟨p,hp',k,hk⟩ := Nat.exists_prime_and_dvd hn1
    have hpn : p ≤ n := Nat.le_of_dvd hns ⟨k,hk⟩
    have hsd : P / p = (k:ℝ)*d := by
      rw [← hn,hk,Nat.cast_mul]
      field_simp [(show (p:ℝ)≠0 by exact_mod_cast hp'.ne_zero)]
    have hper := hmin.nat_mul k
    exact htest p hp' (hpn.trans hncap) (by rw [hsd]; simpa using hper 0)
  have hpd : d=P := by simpa [hone] using hn
  exact ⟨⟨hz,hp⟩,fun _ hs => hpd ▸ hd.2 hs⟩

def supportPart (a : State) (s : ℝ) (i : Fin 4) : ℝ :=
  rotatingTrajectory a s (i.castLE (by decide))

theorem actual_primitive_of_endpoint_checks {a : State} {T θ : ℝ}
    (ht : 0<T) (hcap : T<32)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector θ)
    (hsmall : ∀ s : ℝ, 0<s → s≤1/40 → supportPart a s ≠ supportPart a 0)
    (htest : ∀ p : ℕ, p.Prime → p≤2560 → supportPart a (2*T/p) ≠ supportPart a 0) :
    IsLeast {s : ℝ | Periodic (supportPart a) s ∧ 0<s} (2*T) := by
  apply primitive_of_prime_checks (supportPart a) (by positivity) (by linarith)
    _ hsmall htest
  intro s
  ext i
  exact rotatingTrajectory_coordinate_periodic hmatch _ (by fin_cases i <;> decide) s

/-- A central reference-grid clock. The difference from the actual sampled
time includes the movement of the half-period parameter. -/
noncomputable def gridTime (T₀ : ℝ) (p : ℕ) : ℝ :=
  (round ((8000:ℝ)/p) : ℝ) * (T₀/4000)

theorem prime_test_time_error {T T₀ : ℝ} (hT₀ : 0<T₀) (h32 : T₀<32)
    (hclose : |T-T₀| ≤ (1:ℝ)/10^32) {p : ℕ} (hp : p.Prime) :
    |2*T/p-gridTime T₀ p| < 1/200 := by
  have hpos : 0<(p:ℝ) := by exact_mod_cast hp.pos
  have htwo : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hid : 2*T/p-gridTime T₀ p = (2/p)*(T-T₀)+
      (((8000:ℝ)/p)-(round ((8000:ℝ)/p):ℝ))*(T₀/4000) := by
    unfold gridTime
    ring
  rw [hid]
  apply (abs_add_le _ _).trans_lt
  rw [abs_mul,abs_mul,abs_of_pos (div_pos (by norm_num) hpos),
    abs_of_pos (div_pos hT₀ (by norm_num))]
  have hfactor : (2:ℝ)/p ≤ 1 := (div_le_one hpos).mpr htwo
  have h1 := mul_le_mul hfactor hclose (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  have h2 := mul_le_mul_of_nonneg_right (abs_sub_round ((8000:ℝ)/p))
    (show 0≤T₀/4000 by positivity)
  linarith

/-- The finite arithmetic obligations are now state-coordinate inequalities
at actual reference-grid times. The short Lipschitz bound permits a
componentwise enclosure without asserting exact equality of the two clocks. -/
theorem actual_primitive_of_grid_coordinate_gaps {a : State} {T T₀ θ : ℝ}
    (ht : 0<T) (htcap : T<32) (hT₀ : 0<T₀) (h32 : T₀<32)
    (hclose : |T-T₀| ≤ (1:ℝ)/10^32)
    (hmatch : rotatingTrajectory a T=rotatingTrajectory a (-T)+angleVector θ)
    (hsmall : ∀ s : ℝ, 0<s → s≤1/40 → supportPart a s ≠ supportPart a 0)
    (hspeed : ∀ p : ℕ, p.Prime → p≤2560 → ∀ i : Fin 4,
      |supportPart a (gridTime T₀ p) i-supportPart a (2*T/p) i| ≤
        75*|2*T/p-gridTime T₀ p|)
    (hgrid : ∀ p : ℕ, p.Prime → p≤2560 → ∃ i : Fin 4,
      2/5 < |supportPart a (gridTime T₀ p) i-supportPart a 0 i|) :
    IsLeast {s : ℝ | Periodic (supportPart a) s ∧ 0<s} (2*T) := by
  apply actual_primitive_of_endpoint_checks ht htcap hmatch hsmall
  intro p hp hpc he
  obtain ⟨i,hi⟩ := hgrid p hp hpc
  have h := hspeed p hp hpc i
  rw [he] at h
  linarith [prime_test_time_error hT₀ h32 hclose hp]

end SolitonClassification.Rotating.PrimitiveSupportPeriod
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (n, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating.PrimitiveSupportPeriod).isPrefixOf n then
      for a in (← collectAxioms n) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
          throwError "Unexpected axiom {a} in {n}"
      count := count+1
  logInfo m!"PRIMITIVE_SUPPORT_PERIOD_AUDIT {count} declarations with standard axioms"
