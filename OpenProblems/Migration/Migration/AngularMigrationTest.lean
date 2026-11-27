import Migration.AngularElasticFlow
import Migration.AngularMeshSeparation
import Migration.RecurringMigration

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.AngularGauge.Chart
variable {I : Set ℝ} {P : ℝ} (c : Chart I P)

theorem position_periodic {t : ℝ} (ht : t∈I) (a b : ℝ) (anchor : ℝ→ℝ)
    (closed : c.periodShift a b t=0) : Function.Periodic (c.position a b anchor t) P := by
  have cf : Continuous (c.slope a b t) := continuous_iff_continuousAt.mpr fun x =>
    (continuousAt_const.mul (((c.theta_x t ht x).cos.const_mul a).add
      ((c.theta_x t ht x).sin.const_mul b)).continuousAt)
  have per : Function.Periodic (c.slope a b t) P := fun x => by
    simp only [slope,(c.periodicTN ht a b).1 x]
  intro x
  have h := per.intervalIntegral_add_eq x 0
  simp only [zero_add] at h
  change (∫ s in (0:ℝ)..P,c.slope a b t s)=0 at closed
  rw [closed] at h
  unfold position
  rw [← intervalIntegral.integral_add_adjacent_intervals (cf.intervalIntegrable (μ:=volume) 0 x)
    (cf.intervalIntegrable (μ:=volume) x (x+P)),h,add_zero]

/-- One certified closure at the earlier time is enough for both full
parameter ranges. The true physical clock can be any increasing change
of time between the two certified sections. -/
theorem separated_ranges_of_mesh {s t s₀ t₀ : ℝ} {clock : ℝ→ℝ}
    (pp : 0<P) (st : s≤t) (inside : Icc s t ⊆ I)
    (hs : 0≤s₀) (later : s₀<t₀) (cs : clock s₀=s) (ct : clock t₀=t)
    (a b : ℝ→ℝ) (closedX : c.periodShift 1 0 s=0) (closedY : c.periodShift 0 1 s=0)
    {Z₀ Z₁ DZ₀ DZ₁ : ℝ→ℝ} {n : ℕ} (nn : 0<n)
    (p₀ : Function.Periodic Z₀ P) (p₁ : Function.Periodic Z₁ P)
    (dz₀ : ∀x,HasDerivAt Z₀ (DZ₀ x) x) (dz₁ : ∀x,HasDerivAt Z₁ (DZ₁ x) x)
    {e₀ e₁ m₀ m₁ lo hi : ℝ}
    (cap₀ : ∀x,|c.slope 0 1 s x-DZ₀ x|≤e₀)
    (cap₁ : ∀x,|c.slope 0 1 t x-DZ₁ x|≤e₁)
    (mean₀ : |(∫x in (0:ℝ)..P,(c.position 0 1 b s-Z₀) x)/P|≤m₀)
    (mean₁ : |(∫x in (0:ℝ)..P,(c.position 0 1 b t-Z₁) x)/P|≤m₁)
    (initial : ∀i : ℕ,i≤n → Z₀ (i*(P/n))≤lo)
    (terminal : ∀i : ℕ,i≤n → hi≤Z₁ (i*(P/n)))
    (gap : lo+(m₀+e₀*(P/4))+c.rho s*(P/n/2) <
      hi-(m₁+e₁*(P/4))-c.rho t*(P/n/2)) :
    Function.Periodic (c.planePosition a b s) P ∧
    Function.Periodic (c.planePosition a b t) P ∧
    SimilarityHull.HasSeparatedSlices (fun u=>range (c.planePosition a b (clock u))) := by
  have si := inside (left_mem_Icc.mpr st)
  have ti := inside (right_mem_Icc.mpr st)
  have per {u : ℝ} (hu : u∈I) (cx : c.periodShift 1 0 u=0) (cy : c.periodShift 0 1 u=0) :
      Function.Periodic (c.planePosition a b u) P := by
    intro x
    simp only [planePosition,c.position_periodic hu 1 0 a cx x,c.position_periodic hu 0 1 b cy x]
  have xt := (c.periodShift_constant st inside 1 0).trans closedX
  have yt := (c.periodShift_constant st inside 0 1).trans closedY
  have ps := c.position_periodic si 0 1 b closedY
  have pt := c.position_periodic ti 0 1 b yt
  have bound {u : ℝ} (hu : u∈I) (x : ℝ) : |c.slope 0 1 u x|≤c.rho u := by
    simp only [slope,T,zero_mul,one_mul,zero_add,abs_mul,abs_of_pos (c.rho_pos u hu)]
    exact mul_le_of_le_one_right (c.rho_pos u hu).le (Real.abs_sin_le_one _)
  obtain ⟨l,bl,bh⟩ := mesh_separates pp nn (ps.sub p₀) (pt.sub p₁)
    (fun x=>c.position_space si 0 1 x b) (fun x=>c.position_space ti 0 1 x b)
    dz₀ dz₁ cap₀ cap₁ mean₀ mean₁ (bound si) (bound ti) initial terminal le_rfl le_rfl gap
  refine ⟨per si closedX closedY,per ti xt yt,s₀,t₀,hs,later,Complex.imCLM,l,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    obtain ⟨v,hv,hv'⟩ := ps.exists_mem_Ico₀ pp x
    simpa [cs,planePosition,hv'] using bl v ⟨hv.1,hv.2.le⟩
  · rintro _ ⟨x,rfl⟩
    obtain ⟨v,hv,hv'⟩ := pt.exists_mem_Ico₀ pp x
    simpa [ct,planePosition,hv'] using bh v ⟨hv.1,hv.2.le⟩

end MigrationGeometry.AngularGauge.Chart
#print axioms MigrationGeometry.AngularGauge.Chart.separated_ranges_of_mesh
