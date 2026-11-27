import SolitonClassification.FinitePassage
import SolitonClassification.TwelveLocalCycleTests

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Filter Set Topology

/-- Reversing at the same flight time changes the residual by a controlled
    factor. Combined with the strict odd derivative, this gives a pointwise
    lower bound on section displacement at nonzero pitch. -/
theorem pitch_cost_of_reversible_residual
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (Z : Section × ℝ → Section × (Fin 2 → ℝ)) (even : Section)
    (chart : Tendsto Z (𝓝 base) (𝓝 (even,0)))
    (pitch : ∀ y, (Z y).2 1=y.2)
    (G : Section × (Fin 2 → ℝ) → Y) (D : (Section × (Fin 2 → ℝ)) →L[ℝ] Y)
    (smooth : HasStrictFDerivAt G D (even,0)) {c : ℝ} (cp : 0<c)
    (rank : ∀ v : Fin 2 → ℝ, c*‖v‖≤‖D (0,v)‖)
    {K : ℝ} (kp : 0<K)
    (returns : ∀ᶠ y in 𝓝 base, ‖G (Z y)‖+‖G ((Z y).1,-(Z y).2)‖≤K*‖F y-y.1‖) :
    ∃ d>0, ∀ᶠ y in 𝓝 base, d* |y.2|≤‖F y-y.1‖ := by
  refine ⟨c/K,div_pos cp kp,?_⟩
  have sep := ClosedSimilarity.OddLocalRigidity.eventually_odd_separation smooth cp rank
  filter_upwards [chart.eventually sep,returns] with y h j
  have p : |y.2|≤‖(Z y).2‖ := by rw [←pitch y]; exact norm_le_pi_norm ((Z y).2) (1 : Fin 2)
  have t := (mul_le_mul_of_nonneg_left p cp.le).trans
    (h.trans ((norm_sub_le (G (Z y)) (G ((Z y).1,-(Z y).2))).trans j))
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ kp).mpr (by linarith)

/-- For a local strict spectral chart with a displacement lower bound
    proportional to pitch, the number of consecutive bounded returns times
    the absolute pitch has a uniform upper bound. All finite orbit segments
    are admissible, irrespective of periodicity. -/
theorem local_pitch_residence_bound
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (A : (Section × ℝ) →L[ℝ] Section) (strict : HasStrictFDerivAt F A base)
    (a u : ℝ) (ha : |a|<1) (hu : 1< |u|)
    (axes : ∀ v : Section, A (v,0) 0=a*v 0 ∧ A (v,0) 1=v 1 ∧ A (v,0) 2=u*v 2)
    (g : ℝ) (gp : 0<g) (cost : ∀ᶠ y in 𝓝 base, g* |y.2|≤‖F y-y.1‖) :
    ∃ W ∈ 𝓝 base, ∃ C>0, ∀ (N : ℕ) (x : ℕ → Section) (ω : ℝ),
      (∀ n≤N+1, (x n,ω)∈W) → (∀ n≤N, F (x n,ω)=x (n+1)) → N* |ω|≤C := by
  let e := min ((1-|a|)/4) ((|u|-1)/4)
  have ep : 0<e := lt_min (by linarith) (by linarith)
  have s : |a|+2*e<1 := by linarith [show e≤(1-|a|)/4 from min_le_left ..]
  have un : 1+2*e< |u| := by linarith [show e≤(|u|-1)/4 from min_le_right ..]
  let good := {p : (Section×ℝ)×(Section×ℝ) | ‖F p.1-F p.2-A (p.1-p.2)‖≤e*‖p.1-p.2‖}
  have h : good ∈ (𝓝 base) ×ˢ (𝓝 base) := by rw [←nhds_prod_eq]; exact strict.isLittleO.def ep
  obtain ⟨V,hV,Z,hZ,sub⟩ := Filter.mem_prod_iff.mp h
  let D := ‖base.1‖+1
  have dp : 0<D := by dsimp [D]; positivity
  have inside : ∀ᶠ y : Section×ℝ in 𝓝 base, ‖y.1‖<D :=
    (continuous_fst.norm.tendsto base).eventually_lt_const (by dsimp [D]; linarith)
  obtain ⟨c,cp,budget⟩ := finite_passage_variation a u e ep.le s un
  refine ⟨(V∩Z)∩({y | g* |y.2|≤‖F y-y.1‖}∩{y : Section×ℝ | ‖y.1‖<D}),
    inter_mem (inter_mem hV hZ) (inter_mem cost inside),10*D/(c*g),by positivity,?_⟩
  intro N x ω kept flight
  let v := fun n => x (n+1)-x n
  have paid := budget x N D (fun n nn => (kept n nn).2.2.le) (by
    intro w n nn
    have val := sub (show ((x (n+1),ω),(x n,ω))∈V×ˢZ from
      ⟨(kept (n+1) (by omega)).1.1,(kept n (by omega)).1.2⟩)
    have diff : (x (n+1),ω)-(x n,ω)=(v n,0) := Prod.ext rfl (sub_self _)
    change ‖F (x (n+1),ω)-F (x n,ω)-A ((x (n+1),ω)-(x n,ω))‖≤e*‖(x (n+1),ω)-(x n,ω)‖ at val
    have step : ‖v (n+1)-A (v n,0)‖≤e*‖v n‖ := by
      simpa only [diff,flight _ nn,flight _ nn.le,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using val
    have each (j : Fin 3) := (norm_le_pi_norm (v (n+1)-A (v n,0)) j).trans step
    have parts := axes (v n)
    exact ⟨by simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.1] using each 0,
      by simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.1] using each 1,
      by simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.2] using each 2⟩)
  have lo (n : ℕ) (nn : n∈Finset.range N) : g* |ω|≤‖x (n+1)-x n‖ := by
    have h := Finset.mem_range.mp nn
    have hcost : g* |ω|≤‖F (x n,ω)-x n‖ := (kept n (by omega)).2.1
    rwa [flight n h.le] at hcost
  have lower := Finset.sum_le_sum lo
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at lower
  apply (le_div_iff₀ (mul_pos cp gp)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left lower cp.le,paid]

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.pitch_cost_of_reversible_residual
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.local_pitch_residence_bound
