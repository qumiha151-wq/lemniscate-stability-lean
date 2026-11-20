import Migration.EscapingHulls

noncomputable section
open Set
namespace MigrationGeometry.SimilarityHull

/-- Time after n returns with fixed time T and spatial dilation r. -/
def returnTime (T r u : ℝ) (n : ℕ) : ℝ := T + (r ^ 4) ^ n * (u-T)

/-- The angle at the next phase may depend on the current time. -/
def HasDiscreteSimilarity (K : ℝ → Set ℂ) (O : ℂ) (T r : ℝ) : Prop :=
  ∀ u, 0 ≤ u → ∃ a : ℂ, ‖a‖ = r ∧
    K (T+r^4*(u-T)) = directSimilarity O a '' K u

def ArbitrarilyLateSeparation (K : ℝ → Set ℂ) : Prop :=
  ∀ u, 0 ≤ u → ∀ B : ℝ, ∃ t, max u B < t ∧ separated (K u) (K t)

def HasSeparatedSlices (K : ℝ → Set ℂ) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ separated (K s) (K t)

private theorem return_time_nonneg {T r u : ℝ} (hT : T < 0) (hr : 1 < r)
    (hu : 0 ≤ u) (n : ℕ) : 0 ≤ returnTime T r u n := by
  have ha : 1 ≤ r ^ 4 := one_le_pow₀ hr.le
  have hv : 0 ≤ u-T := by linarith
  have h := le_mul_of_one_le_left hv (one_le_pow₀ ha (n := n))
  dsimp [returnTime]
  linarith

/-- Iteration of the single-step law gives the exact image, the physical
time and the norm of the accumulated complex multiplier. -/
theorem iterated_discrete_similarity {K : ℝ → Set ℂ} {O : ℂ} {T r u : ℝ}
    (hT : T < 0) (hr : 1 < r) (hs : HasDiscreteSimilarity K O T r)
    (hu : 0 ≤ u) (n : ℕ) : ∃ a : ℂ, ‖a‖ = r^n ∧
      K (returnTime T r u n) = directSimilarity O a '' K u := by
  induction n with
  | zero =>
    refine ⟨1,by simp,?_⟩
    have hid : directSimilarity O 1 = id := by
      funext z
      dsimp [directSimilarity]
      ring
    simp [returnTime,hid]
  | succ n ih =>
    obtain ⟨a,ha,he⟩ := ih
    obtain ⟨b,hb,hbK⟩ := hs _ (return_time_nonneg hT hr hu n)
    refine ⟨b*a,by rw [norm_mul,hb,ha,pow_succ'],?_⟩
    have clock : returnTime T r u (n+1) = T+r^4*(returnTime T r u n-T) := by
      simp only [returnTime,pow_succ']
      ring
    rw [clock,hbK,he,image_image]
    congr 1
    funext z
    dsimp [directSimilarity]
    ring

/-- All nonnegative times are iterates of phases in the first closed period. -/
theorem exists_return_phase {T r u : ℝ} (hT : T < 0) (hr : 1 < r) (hu : 0 ≤ u) :
    ∃ v ∈ Icc 0 (T+r^4*(0-T)), ∃ n : ℕ, returnTime T r v n = u := by
  let A := r ^ 4
  have hA : 1 < A := one_lt_pow₀ hr (by decide : 4 ≠ 0)
  have hT' : 0 < -T := neg_pos.mpr hT
  have hx : 1 ≤ (u-T)/(-T) := (one_le_div hT').2 (by linarith)
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near hx hA
  have hAn : 0 < A^n := pow_pos (zero_lt_one.trans hA) n
  have hlo := (le_div_iff₀ hT').1 hn
  have hhi := (div_lt_iff₀ hT').1 hn'
  have hleft : -T ≤ (u-T)/A^n := (le_div_iff₀ hAn).2 (by simpa [mul_comm] using hlo)
  have hright : (u-T)/A^n ≤ A*(-T) := (div_le_iff₀ hAn).2 (by
    simpa [pow_succ,mul_comm,mul_left_comm,mul_assoc] using hhi.le)
  refine ⟨T+(u-T)/A^n,⟨by linarith,by change T+_ ≤ T+A*(0-T); linarith⟩,n,?_⟩
  change T+A^n*((T+(u-T)/A^n)-T) = u
  field_simp
  ring

/-- An exterior phase eventually separates its expanded copies from any
prescribed compact slice, even with arbitrarily varying angular factors. -/
theorem late_separation_of_exterior_phase {K : ℝ → Set ℂ} {O : ℂ} {T r v : ℝ}
    (hT : T < 0) (hr : 1 < r) (hk : ∀ u, 0 ≤ u → IsCompact (K u))
    (hn : ∀ u, 0 ≤ u → (K u).Nonempty) (hs : HasDiscreteSimilarity K O T r)
    (hv : 0 ≤ v) (hout : O ∉ convexHull ℝ (K v)) : ArbitrarilyLateSeparation K := by
  let d := Metric.infDist O (convexHull ℝ (K v))
  have hd : 0 < d := ((compact_convexHull (hk _ hv)).isClosed.notMem_iff_infDist_pos
    ((hn _ hv).mono (subset_convexHull ℝ (K v)))).mp hout
  intro u hu B
  obtain ⟨m,_,hm⟩ := (hk u hu).exists_isMaxOn (hn u hu)
    (show ContinuousOn (fun x => dist x O) (K u) from
      (continuous_id.dist continuous_const).continuousOn)
  have hvT : 0 < v-T := by linarith
  obtain ⟨n,hn'⟩ := pow_unbounded_of_one_lt (max (dist m O/d) ((max u B-T)/(v-T))) hr
  have hspace := (div_lt_iff₀ hd).1 ((le_max_left _ _).trans_lt hn')
  have htime := (div_lt_iff₀ hvT).1 ((le_max_right _ _).trans_lt hn')
  have hp : r^n ≤ (r^4)^n :=
    pow_le_pow_left₀ (zero_lt_one.trans hr).le (le_self_pow₀ hr.le (by decide : 4 ≠ 0)) n
  obtain ⟨a,ha,hK⟩ := iterated_discrete_similarity hT hr hs hv n
  refine ⟨returnTime T r v n,?_,?_⟩
  · dsimp [returnTime]
    linarith only [htime, mul_le_mul_of_nonneg_right hp hvT.le]
  · rw [hK]
    apply separated_of_similarity_error (K := K v) (hk v hv) O a
      (R := dist m O) (ε := 0) (fun _ h => hm h)
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨x,hx,(dist_self _).le⟩
    · simpa [ha,d] using hspace

/-- The exact discreteness criterion on the physical half-line, including
reduction to the first period and arbitrary late times for each early slice. -/
theorem discrete_migration_equivalences {K : ℝ → Set ℂ} {O : ℂ} {T r : ℝ}
    (hT : T < 0) (hr : 1 < r) (hk : ∀ u, 0 ≤ u → IsCompact (K u))
    (hn : ∀ u, 0 ≤ u → (K u).Nonempty) (hs : HasDiscreteSimilarity K O T r) :
    ((∃ v ∈ Icc 0 (T+r^4*(0-T)), O ∉ convexHull ℝ (K v)) ↔ ArbitrarilyLateSeparation K) ∧
    (ArbitrarilyLateSeparation K ↔ HasSeparatedSlices K) := by
  have first : (∃ v ∈ Icc 0 (T+r^4*(0-T)), O ∉ convexHull ℝ (K v)) →
      ArbitrarilyLateSeparation K := by
    rintro ⟨v,hv,hout⟩
    exact late_separation_of_exterior_phase hT hr hk hn hs hv.1 hout
  have second : ArbitrarilyLateSeparation K → HasSeparatedSlices K := by
    intro h
    obtain ⟨t,ht,hst⟩ := h 0 le_rfl 0
    exact ⟨0,t,le_rfl,by simpa using ht,hst⟩
  have third : HasSeparatedSlices K →
      ∃ v ∈ Icc 0 (T+r^4*(0-T)), O ∉ convexHull ℝ (K v) := by
    rintro ⟨s,t,h₀,hst,hsep⟩
    by_contra! h
    have common (u : ℝ) (hu : 0 ≤ u) : O ∈ convexHull ℝ (K u) := by
      obtain ⟨v,hv,n,hvn⟩ := exists_return_phase hT hr hu
      obtain ⟨a,_,he⟩ := iterated_discrete_similarity hT hr hs hv.1 n
      rw [← hvn,he]
      exact center_mem_direct_hull (h v hv) a
    exact not_separated_of_common_hull (common s h₀) (common t (h₀.trans hst.le)) hsep
  exact ⟨⟨first,third ∘ second⟩,⟨second,first ∘ third⟩⟩

#print axioms iterated_discrete_similarity
#print axioms exists_return_phase
#print axioms late_separation_of_exterior_phase
#print axioms discrete_migration_equivalences
end MigrationGeometry.SimilarityHull
