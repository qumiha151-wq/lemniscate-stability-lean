import SolitonClassification.Rotating.FlowBootstrapNeighborhood
import SolitonClassification.Rotating.ActualShooting
import SolitonClassification.Rotating.RotatingGridMargin

/-! Exact time coverage for a shooting-parameter neighborhood. Only the
last grid endpoint is extended. The old center endpoint remains inside
the final segment, while every local polynomial argument remains within
the certified step cap. A scalar budget such as 32 is not a time domain. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set Finset UniversalMajorant
set_option backward.isDefEq.respectTransparency false

def extendedGridTime (N : ℕ) (h r : ℝ) (j : ℕ) : ℝ :=
  if j<N then (j:ℝ)*h else (N:ℝ)*h+2*r

theorem extendedGridTime_zero {N : ℕ} (hN : 0<N) (h r : ℝ) : extendedGridTime N h r 0=0 := by
  simp [extendedGridTime,hN]

theorem extendedGridTime_last (N : ℕ) (h r : ℝ) : extendedGridTime N h r N=(N:ℝ)*h+2*r := by
  simp [extendedGridTime]

theorem extendedGridTime_before {N j : ℕ} (hj : j<N) (h r : ℝ) :
    extendedGridTime N h r j=(j:ℝ)*h := by simp [extendedGridTime,hj]

theorem extendedGridTime_step {N j : ℕ} {h r : ℝ} (hj : j<N) (hh : 0≤h) (hr : 0≤r) :
    extendedGridTime N h r j≤extendedGridTime N h r (j+1) := by
  rw [extendedGridTime_before hj]
  by_cases hn : j+1<N
  · rw [extendedGridTime_before hn]
    push_cast
    nlinarith
  · have he : j+1=N := by omega
    rw [he,extendedGridTime_last,←he]
    push_cast
    nlinarith

theorem extendedGridTime_mem {N j : ℕ} {h r : ℝ} (hj : j≤N) (hh : 0≤h) (hr : 0≤r) :
    extendedGridTime N h r j∈Icc 0 ((N:ℝ)*h+2*r) := by
  by_cases hn : j<N
  · rw [extendedGridTime_before hn]
    have hcast : (j:ℝ)≤(N:ℝ) := by exact_mod_cast hj
    exact ⟨by positivity,by nlinarith⟩
  · have he : j=N := by omega
    rw [he,extendedGridTime_last]
    exact ⟨by positivity,le_rfl⟩

theorem extendedGridTime_local_bounds {N j : ℕ} {h r t : ℝ} (hj : j<N) (hr : 0≤r)
    (ht : t∈Icc (extendedGridTime N h r j) (extendedGridTime N h r (j+1))) :
    0≤t-(j:ℝ)*h ∧ t-(j:ℝ)*h≤h+2*r := by
  have hl := ht.1
  rw [extendedGridTime_before hj] at hl
  refine ⟨by linarith,?_⟩
  have hu := ht.2
  by_cases hn : j+1<N
  · rw [extendedGridTime_before hn] at hu
    push_cast at hu
    linarith
  · have he : j+1=N := by omega
    rw [he,extendedGridTime_last,←he] at hu
    push_cast at hu
    linarith

theorem extendedGridTime_signed_local_cap (σ : ℝ) (hσ : |σ|≤1)
    {N j : ℕ} {h r t H : ℝ} (hj : j<N) (hr : 0≤r) (hcap : h+2*r≤H)
    (ht : t∈Icc (extendedGridTime N h r j) (extendedGridTime N h r (j+1))) :
    |σ*(t-(j:ℝ)*h)|≤H := by
  have hl := extendedGridTime_local_bounds hj hr ht
  rw [abs_mul,abs_of_nonneg hl.1]
  exact (mul_le_mul_of_nonneg_right hσ hl.1).trans
    (by simpa only [one_mul] using hl.2.trans hcap)

theorem center_endpoint_in_extended_last_segment {N : ℕ} {h r : ℝ}
    (hN : 0<N) (hh : 0≤h) (hr : 0≤r) :
    (N:ℝ)*h∈Icc (extendedGridTime N h r (N-1)) (extendedGridTime N h r N) := by
  rw [extendedGridTime_before (by omega : N-1<N),extendedGridTime_last]
  have hn : ((N-1:ℕ):ℝ)≤(N:ℝ) := by exact_mod_cast Nat.sub_le N 1
  exact ⟨mul_le_mul_of_nonneg_right hn hh,by linarith⟩

theorem extendedGridTime_polynomial_margin (σ : ℝ) (hσ : |σ|≤1)
    {N j : ℕ} {h r t : ℝ} {a : State} (ha : a∈innerTube)
    (hj : j<N) (hr : 0≤r) (hcap : h+2*r≤(universalStepCap:ℝ))
    (ht : t∈Icc (extendedGridTime N h r j) (extendedGridTime N h r (j+1))) :
    outerTubeMargin (polynomialPath (taylorPolynomial a 60) (σ*(t-(j:ℝ)*h))) (1/100) :=
  taylorPolynomial60_margin_uniform ha (extendedGridTime_signed_local_cap σ hσ hj hr hcap ht)

/-- Every half-length in the CLOSED parameter ball lies in the OPEN
time domain required by actual joint differentiability. Radius slack is
real: the horizon is center half-length plus 2*r, not plus r. -/
theorem shooting_length_in_extended_horizon {p c : Parameters} {r : ℝ}
    (hr : 0<r) (hp : r<p 2) (hc : c∈Metric.closedBall p r) : c 2∈Ioo 0 (p 2+2*r) := by
  have hn : ‖c-p‖≤r := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hc
  have hb : |c 2-p 2|≤r := by
    have h := (norm_le_pi_norm (c-p) (2:Fin 5)).trans hn
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using h
  have hab := abs_le.mp hb
  exact ⟨by linarith,by linarith⟩

/-- The actual covered horizon comes from a bootstrap grid CERTIFIED on
the extended interval. This theorem does not turn an old shorter-grid
certificate or a scalar upper budget into additional trajectory data. -/
theorem extended_grid_actual_tube {σ : ℝ} (hσ : |σ|≤1)
    {N : ℕ} {h r K I R ρ δ B SX SM : ℝ} {c : State} {rinit : ℝ}
    (g : FlowBootstrapGridData σ N ((N:ℝ)*h+2*r) K I R ρ δ)
    (hN : 0<N) (hB : 0≤B) (hK : 0≤K) (hI : 0≤I) (hR : 0≤R) (hρ : 0≤ρ) (hδ : 0≤δ)
    (hSX : (∑j∈range N,g.stateJump j)≤SX) (hSM : (∑j∈range N,g.matrixJump j)≤SM)
    (hstrict : (B+g.forcing*((N:ℝ)*h+2*r)+I*SX)*Real.exp (I*SM)<R)
    (hcenter : ‖c-g.reference 0 0‖+rinit≤B) :
    FlowTubeNeighborhood σ hσ ((N:ℝ)*h+2*r) c rinit :=
  g.tubeNeighborhood hσ hN hB hK hI hR hρ hδ hSX hSM hstrict hcenter

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating actual extended-grid horizon audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating actual extended-grid horizon audit passed for {count} declarations."
