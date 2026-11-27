import SolitonClassification.Rotating.IntegerCrossingPositions

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set DyadicReset
set_option maxHeartbeats 2000000

theorem covered_cell (N : ℕ) (hN : 0<N) (v : ℝ) (h0 : 0≤v) (h1 : v≤N) :
    ∃i : ℕ, i<N ∧ ∃t∈unitCell, v=(i:ℝ)+t := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases h : 0<N ∧ v≤N
    · obtain ⟨i,lo,t,ht,e⟩ := ih h.1 h.2
      exact ⟨i,by omega,t,ht,e⟩
    · have low : (N:ℝ)≤v := by
        by_cases hn : N=0
        · simpa only [hn,Nat.cast_zero] using h0
        · exact le_of_not_ge (fun q => h ⟨by omega,q⟩)
      refine ⟨N,by omega,v-N,⟨by linarith,by push_cast at h1; linarith⟩,by ring⟩


def h := step Middle.hn
def gridPosition (c : Parameters) (v : ℝ) := segmentPosition c (v*h)
def gridAngle (c : Parameters) (v : ℝ) := wideFlow (v*h,shootingInitial phase c) 5

theorem h_mem : 0<h ∧ h<1/125 := by norm_num [h,step,Middle.hn,Middle.hd]

theorem grid_rates {c : Parameters} (hc : c∈cube) (v : ℝ) (hv : v∈Icc 0 4000) :
    HasDerivAt (fun u => (gridPosition c u).1) (Real.cos (gridAngle c v)*h) v ∧
    HasDerivAt (fun u => (gridPosition c u).2) (Real.sin (gridAngle c v)*h) v ∧
    ∃k:ℝ, |k|≤10 ∧ HasDerivAt (gridAngle c) (k*h) v := by
  obtain ⟨i,hi,t,ht,vt⟩ := covered_cell 4000 (by decide) v hv.1 (by simpa using hv.2)
  have first : CompletePlus.tape.node 0=initialNode := (CompletePlus.range 0 (by decide)).1.trans rfl
  have data := prefix_physical CompletePlus.tape (by decide) (by decide) (signedHalfSteps true) first hc i hi t ht
  let z := fun s:ℝ=>wideFlow (s,shootingInitial phase c)
  have eq : ((i:ℝ)+t)*step Middle.hn=v*h := by rw [vt];rfl
  dsimp only at data
  rw [eq] at data
  have de (j : Fin 6) : HasDerivAt (fun u=>z u j) (field (z (v*h)) j) (v*h) :=
    (ContinuousLinearMap.proj j : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt _ data.1
  let k := fun u => z u 0
  let p := fun u => z u 2
  let q := fun u => z u 3
  let θ := fun u => z u 5
  have dp : HasDerivAt p (-k (v*h)*q (v*h)) (v*h) := de 2
  have dq : HasDerivAt q (1+k (v*h)*p (v*h)) (v*h) := de 3
  have dt : HasDerivAt θ (k (v*h)) (v*h) := de 5
  have sc : HasDerivAt (fun u:ℝ=>u*h) h v := by simpa using (hasDerivAt_id v).mul_const h
  have inner := (lift_inner (CompletePlus.tape.small i hi) ht).1 (0:Fin 6) (by decide)
  change |path (CompletePlus.tape.data i) d t 0|≤9 at inner
  have err := (coordinate_bound (z (v*h)-path (CompletePlus.tape.data i) d t) 0).trans data.2
  change |k (v*h)-path (CompletePlus.tape.data i) d t 0|≤_ at err
  have kb : |k (v*h)|≤10 := by
    have tri := abs_add_le (k (v*h)-path (CompletePlus.tape.data i) d t 0) (path (CompletePlus.tape.data i) d t 0)
    rw [sub_add_cancel] at tri; linarith
  have xx := (ClosedSimilarity.profileX_hasDerivAt k p q θ (v*h) dp dq dt).comp v sc
  have yy := (ClosedSimilarity.profileY_hasDerivAt k p q θ (v*h) dp dq dt).comp v sc
  have tt := dt.comp v sc
  exact ⟨xx,yy,k _,kb,tt⟩

theorem grid_lipschitz {c : Parameters} (hc : c∈cube) {s t : ℝ}
    (hs : s∈Icc 0 4000) (ht : t∈Icc 0 4000) :
    |(gridPosition c t).1-(gridPosition c s).1|≤h*|t-s| ∧
    |(gridPosition c t).2-(gridPosition c s).2|≤h*|t-s| ∧
    |gridAngle c t-gridAngle c s|≤(10*h)*|t-s| := by
  have lip (f : ℝ→ℝ) (K : ℝ) (rates : ∀u∈Icc (0:ℝ) 4000,∃a, HasDerivAt f a u ∧ |a|≤K) :
      |f t-f s|≤K*|t-s| := by
    have z := (convex_Icc (0:ℝ) 4000).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => ((rates x hx).choose_spec.1).differentiableAt)
      (fun x hx => by rw [((rates x hx).choose_spec.1).deriv,Real.norm_eq_abs]; exact (rates x hx).choose_spec.2) hs ht
    simpa only [Real.norm_eq_abs] using z
  constructor
  · exact lip _ _ fun u hu => ⟨_,(grid_rates hc u hu).1,by rw [abs_mul,abs_of_pos h_mem.1];simpa using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) h_mem.1.le⟩
  constructor
  · exact lip _ _ fun u hu => ⟨_,(grid_rates hc u hu).2.1,by rw [abs_mul,abs_of_pos h_mem.1];simpa using mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) h_mem.1.le⟩
  · apply lip
    intro u hu
    obtain ⟨k,hk,der⟩ := (grid_rates hc u hu).2.2
    exact ⟨_,der,by rw [abs_mul,abs_of_pos h_mem.1]; exact mul_le_mul_of_nonneg_right hk h_mem.1.le⟩

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.grid_lipschitz

