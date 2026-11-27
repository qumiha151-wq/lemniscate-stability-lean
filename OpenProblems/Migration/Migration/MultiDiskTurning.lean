import Migration.SublevelInitialDisk
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Connected.TotallyDisconnected

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.MultiDisk

/-- A continuously varying integral multiple of a fixed period is constant. -/
theorem quantized_constant {S : Set ℝ} (conn : IsPreconnected S) {f : ℝ→ℝ}
    (cf : ContinuousOn f S) {P : ℝ} (nz : P≠0)
    (quantized : ∀ t∈S, ∃ n : ℤ, f t = (n:ℝ)*P)
    {s t : ℝ} (hs : s∈S) (ht : t∈S) : f t=f s := by
  let n := fun u => ⌊f u/P⌋
  have val (u) (hu : u∈S) : (n u:ℝ)=f u/P := by
    obtain ⟨m,hm⟩ := quantized u hu
    simp [n,hm,nz]
  have cn : ContinuousOn n S := by
    apply Real.isClosedEmbedding_intCast.isEmbedding.isInducing.continuousOn_iff.mpr
    exact (cf.div_const P).congr (fun u hu=>val u hu)
  have sub := (conn.image n cn).subsingleton
  have eq : n t=n s := sub ⟨t,ht,rfl⟩ ⟨s,hs,rfl⟩
  have cast := congrArg (fun m:ℤ=>(m:ℝ)) eq
  rw [val t ht,val s hs] at cast
  exact (div_left_inj' nz).mp cast

end MigrationGeometry.MultiDisk
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem multi_turn_quantized {v : ℝ} (hv : v∈I) :
    ∃n : ℤ, c.signedCurvatureIntegral v=(n:ℝ)*(2*Real.pi) := by
  let p := c.materialSlice hv
  obtain ⟨n,hn⟩ := p.bendingCurve.curvature_turns_integer
  exact ⟨n,p.bendingCurve_turn.symm.trans hn⟩

/-- The integral of signed curvature is constant along any regular material homotopy. -/
theorem multi_turn_on_slab {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I) :
    c.signedCurvatureIntegral t=c.signedCurvatureIntegral s :=
  MultiDisk.quantized_constant isPreconnected_Icc (c.scalar_turn_continuous_slab slab)
    (by positivity : 2*Real.pi≠0) (fun u hu=>c.multi_turn_quantized (slab hu))
    ⟨le_rfl,st⟩ ⟨st,le_rfl⟩

end MigrationGeometry.Flow.SmoothPeriodicImmersion
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- For one-sided classical data the conserved integer is its initial value. -/
theorem multi_turn_from_zero
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    {n : ℤ} (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    {t : ℝ} (ht : 0≤t) :
    c.signedCurvatureIntegral t=(n:ℝ)*(2*Real.pi) := by
  have cc : ContinuousOn c.signedCurvatureIntegral (Icc 0 t) := by
    apply continuousOn_intervalIntegral_of_isCompact isCompact_Icc
    exact (curv.mul spd).mono (fun q h=>⟨h.1.1,mem_univ _⟩)
  have q (u) (hu : u∈Icc 0 t) : ∃m : ℤ, c.signedCurvatureIntegral u=(m:ℝ)*(2*Real.pi) := by
    rcases eq_or_lt_of_le hu.1 with h|h
    · exact ⟨n,h ▸ turn⟩
    · exact c.multi_turn_quantized h
  exact (MultiDisk.quantized_constant isPreconnected_Icc cc (by positivity : 2*Real.pi≠0) q
    ⟨le_rfl,ht⟩ ⟨ht,le_rfl⟩).trans turn

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_turn_from_zero

