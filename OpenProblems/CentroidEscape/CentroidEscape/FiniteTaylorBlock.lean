import CentroidEscape.FiniteShootingPath

/-!
# Proof aggregation for separately checked Taylor blocks

No coefficient arithmetic is recomputed here. A block certificate combines
already proved stage, endpoint, and margin facts. Adjacent blocks need only
agree on the initial coefficient vector at their common boundary.
-/
namespace CentroidEscape.MetricStability
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def Order60SegmentValid (S : ℕ) (h : ℚ) (n : ℕ)
    (st : ℕ → FixedTaylorState) : Prop :=
  ∀ j<n, checkOrderTaylorData S 60 (st j)=true ∧
    (∀ i : Fin 7, (st (j+1)).coefficient 0 i=
      (evaluateFixedTaylorOrder S 60 h (st j))[i.val]) ∧
    checkBallCanonicalMargin (fun i=>((st j).coefficient 0 i).toRational S)=true

def appendTaylorStages (n : ℕ) (a b : ℕ → FixedTaylorState)
    (j : ℕ) : FixedTaylorState := if j<n then a j else b (j-n)

lemma appendTaylorStages_left {n j : ℕ} (a b : ℕ → FixedTaylorState)
    (hj : j<n) : appendTaylorStages n a b j=a j := by
  simp [appendTaylorStages,hj]

lemma appendTaylorStages_right {n j : ℕ} (a b : ℕ → FixedTaylorState)
    (hj : n≤j) : appendTaylorStages n a b j=b (j-n) := by
  simp [appendTaylorStages,Nat.not_lt.mpr hj]

/-- The proof uses each previously checked block once; the boundary check
compares only coefficient0, so a terminal one-vector table is sufficient. -/
theorem Order60SegmentValid.append {S n m : ℕ} {h : ℚ}
    {a b : ℕ → FixedTaylorState}
    (ha : Order60SegmentValid S h n a) (hb : Order60SegmentValid S h m b)
    (hboundary : ∀ i : Fin 7, (a n).coefficient 0 i=(b 0).coefficient 0 i) :
    Order60SegmentValid S h (n+m) (appendTaylorStages n a b) := by
  intro j hj
  by_cases hleft : j<n
  · obtain ⟨hc,hg,hm⟩ := ha j hleft
    rw [appendTaylorStages_left a b hleft]
    refine ⟨hc,?_,hm⟩
    intro i
    by_cases hnext : j+1<n
    · rw [appendTaylorStages_left a b hnext]
      exact hg i
    · have he : j+1=n := by omega
      rw [he,appendTaylorStages_right a b (by omega),Nat.sub_self,← hboundary i]
      simpa only [he] using hg i
  · have hn : n≤j := by omega
    have hjb : j-n<m := by omega
    obtain ⟨hc,hg,hm⟩ := hb (j-n) hjb
    rw [appendTaylorStages_right a b hn]
    refine ⟨hc,?_,hm⟩
    intro i
    rw [appendTaylorStages_right a b (by omega)]
    have he : j+1-n=(j-n)+1 := by omega
    simpa only [he] using hg i

lemma appendTaylorStages_initial {n : ℕ} (hn : 0<n)
    (a b : ℕ → FixedTaylorState) : appendTaylorStages n a b 0=a 0 := by
  exact appendTaylorStages_left a b hn

lemma appendTaylorStages_terminal (n m : ℕ) (a b : ℕ → FixedTaylorState) :
    appendTaylorStages n a b (n+m)=b m := by
  rw [appendTaylorStages_right a b (by omega)]
  congr 1
  omega

/-- Freeze a complete finite segment into the existing 751-entry path API. -/
def finiteShootingPathOfStages (st : ℕ → FixedTaylorState) : FiniteShootingPath :=
  ⟨fun i=>st i.val⟩

lemma finiteShootingPathOfStages_stage {st : ℕ → FixedTaylorState} {j : ℕ}
    (hj : j≤750) : (finiteShootingPathOfStages st).stage j=st j := by
  simp [FiniteShootingPath.stage,finiteShootingPathOfStages,Nat.min_eq_left hj]

theorem finiteShootingPathOfStages_checked {S : ℕ} {h : ℚ}
    {p : RationalVector3} {st : ℕ → FixedTaylorState}
    (hv : Order60SegmentValid S h 750 st)
    (hi : ∀ i : Fin 7,
      |rationalShootingInitial p i-(((st 0).coefficient 0 i).toRational S).center|≤
        (((st 0).coefficient 0 i).toRational S).radius)
    (hr : checkProjectedRadius (order60EndpointBalls S 750 st) (1/10^40)=true) :
    (finiteShootingPathOfStages st).check S h p=true := by
  apply decide_eq_true
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    rw [finiteShootingPathOfStages_stage (by omega)]
    exact (hv j.val j.isLt).1
  · intro j i
    rw [finiteShootingPathOfStages_stage (by omega),
      finiteShootingPathOfStages_stage (by omega)]
    exact (hv j.val j.isLt).2.1 i
  · intro j
    simpa only [finiteShootingPathOfStages_stage (by omega : j.val≤750)]
      using (hv j.val j.isLt).2.2
  · simpa only [finiteShootingPathOfStages_stage (by omega : 0≤750)] using hi
  · have he : (finiteShootingPathOfStages st).endpoint S=order60EndpointBalls S 750 st := by
      funext i
      change ((((finiteShootingPathOfStages st).stage 750).coefficient 0 i).toRational S).inflate
        (1/10^43)=(((st 750).coefficient 0 i).toRational S).inflate (1/10^43)
      rw [finiteShootingPathOfStages_stage (by omega)]
    simpa only [he] using hr

end CentroidEscape.MetricStability

#print axioms CentroidEscape.MetricStability.finiteShootingPathOfStages_checked
