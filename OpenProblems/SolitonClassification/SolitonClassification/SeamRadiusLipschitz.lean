import SolitonClassification.PhysicalSeamScale

noncomputable section
namespace ClosedSimilarity.GlobalSupport
open Set Metric

def seamData (c d : ℝ) : Data := (d,![c,0,1,0])
def seamState (c d t : ℝ) := solution d (seamData c d).2 t
def seamRadius (c d t : ℝ) := Real.sqrt (radiusSq (seamState c d t))
def radiusFactor (c d t : ℝ) := (radiusSq (seamState c d t))^(-2/3:ℝ)

lemma continuous_seamData : Continuous (fun z : ℝ × ℝ => seamData z.1 z.2) := by
  apply continuous_snd.prodMk
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

lemma compact_seam_coordinate_bound {C : Set ℝ} (hC : IsCompact C) {D T : ℝ} (hT : 0 ≤ T) :
    ∃ K > (0:ℝ), ∀ c ∈ C, ∀ a ∈ Icc (0:ℝ) D, ∀ b ∈ Icc (0:ℝ) D, ∀ t, |t| ≤ T →
      ∀ i, |seamState c a t i-seamState c b t i| ≤ K*|a-b| := by
  let f := fun z : ℝ × ℝ => seamData z.1 z.2
  let S := f '' (C ×ˢ Icc (0:ℝ) D)
  obtain ⟨K,hK,h⟩ := compact_initial_estimate (S := S)
    ((hC.prod isCompact_Icc).image continuous_seamData) hT
  refine ⟨K,hK,?_⟩
  intro c hc a ha b hb t ht i
  have z := h (f (c,a)) ⟨(c,a),⟨hc,ha⟩,rfl⟩ (f (c,b)) ⟨(c,b),⟨hc,hb⟩,rfl⟩ t ht
  have base : dist (f (c,a)) (f (c,b)) = |a-b| := by simp [f,seamData,Prod.dist_eq,Real.dist_eq]
  rw [base] at z
  have state := (le_max_right _ _).trans (show max _ _ ≤ _ by exact z)
  have h' := norm_le_pi_norm (seamState c a t-seamState c b t) i
  exact h'.trans (show ‖seamState c a t-seamState c b t‖ ≤ _ by
    simpa only [dist_eq_norm,extended,f,seamData,seamState] using state)

lemma seamRadius_bounds {D T c d t : ℝ} (hd : d ∈ Icc (0:ℝ) D) (ht : |t| ≤ T)
    (small : D*T ≤ 1/2) : 1/2 ≤ seamRadius c d t ∧ seamRadius c d t ≤ 2 := by
  have h := radius_speed d (seamData c d).2 0 t
  have z : radiusSq (solution d (seamData c d).2 0) = 1 := by simp [solution_zero,seamData,radiusSq]
  rw [z,Real.sqrt_one,sub_zero,abs_of_nonneg hd.1] at h
  obtain ⟨a,b⟩ := abs_le.mp (h.trans ((mul_le_mul hd.2 ht (abs_nonneg _) (hd.1.trans hd.2)).trans small))
  unfold seamRadius seamState
  constructor <;> linarith

lemma seamRadius_sq (c d t : ℝ) : seamRadius c d t ^2 = radiusSq (seamState c d t) :=
  Real.sq_sqrt (by unfold radiusSq; positivity)

/-- In a compact family the physical radius factor at a selected crossing is
    uniformly Lipschitz in the seam scale if the crossing times are. -/
theorem compact_radiusFactor_lipschitz {C : Set ℝ} (hC : IsCompact C) {D T B : ℝ}
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hB : 0 ≤ B) (small : D*T ≤ 1/2) (τ : ℝ → ℝ → ℝ)
    (bounded : ∀ c ∈ C, ∀ d ∈ Icc (0:ℝ) D, |τ c d| ≤ T)
    (times : ∀ c ∈ C, ∀ a ∈ Icc (0:ℝ) D, ∀ b ∈ Icc (0:ℝ) D, |τ c a-τ c b| ≤ B*|a-b|) :
    ∃ L ≥ (0:ℝ), ∀ c ∈ C, ∀ a ∈ Icc (0:ℝ) D, ∀ b ∈ Icc (0:ℝ) D,
      |radiusFactor c a (τ c a)-radiusFactor c b (τ c b)| ≤ L*|a-b| := by
  obtain ⟨K,hK,h⟩ := compact_seam_coordinate_bound (D := D) hC hT
  let S := Icc (1/4:ℝ) 4
  have sm : ContDiffOn ℝ 1 (fun x : ℝ => x^(-2/3:ℝ)) S :=
    contDiffOn_id.rpow_const_of_ne (fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1))
  obtain ⟨J,hJ⟩ := sm.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨J*(8*K+4*D*B),by positivity,?_⟩
  intro c hc a ha b hb
  let R := seamRadius c
  let A := fun d t => radiusSq (seamState c d t)
  have rad {d t : ℝ} (hd : d ∈ Icc (0:ℝ) D) (ht : |t| ≤ T) : 1/2 ≤ R d t ∧ R d t ≤ 2 :=
    seamRadius_bounds hd ht small
  have mem {d t : ℝ} (hd : d ∈ Icc (0:ℝ) D) (ht : |t| ≤ T) : A d t ∈ S := by
    have e : (R d t)^2 = A d t := seamRadius_sq _ _ _
    obtain ⟨lo,hi⟩ := rad hd ht
    constructor <;> nlinarith
  let s := τ c a
  let t := τ c b
  have hs : |s| ≤ T := bounded c hc a ha
  have ht : |t| ≤ T := bounded c hc b hb
  have varyTime : |A b s-A b t| ≤ 4*D*B*|a-b| := by
    have ds : |R b s-R b t| ≤ b*|s-t| := by
      simpa only [R,seamRadius,seamState,abs_of_nonneg hb.1] using radius_speed b (seamData c b).2 t s
    have dt : |R b s-R b t| ≤ D*(B*|a-b|) :=
      ds.trans (mul_le_mul hb.2 (times c hc a ha b hb) (abs_nonneg _) hD)
    have plus : |R b s+R b t| ≤ 4 := by
      obtain ⟨l,u⟩ := rad hb hs
      obtain ⟨v,w⟩ := rad hb ht
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    rw [show A b s-A b t = (R b s-R b t)*(R b s+R b t) by
      calc
        _ = (R b s)^2-(R b t)^2 := by simp only [A,R,seamRadius_sq]
        _ = _ := by ring]
    rw [abs_mul]
    nlinarith only [mul_le_mul dt plus (abs_nonneg _) (by positivity)]
  have varyDrive : |A a s-A b s| ≤ 8*K*|a-b| := by
    let p := fun d => seamState c d s 2
    let q := fun d => seamState c d s 3
    have cap {d : ℝ} (hd : d ∈ Icc (0:ℝ) D) : |p d| ≤ 2 ∧ |q d| ≤ 2 := by
      have m := (mem hd hs).2
      change (p d)^2+(q d)^2 ≤ 4 at m
      constructor <;> rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (p d),sq_nonneg (q d)]
    have term (f : ℝ → ℝ) (l : |f a| ≤ 2) (r : |f b| ≤ 2) (z : |f a-f b| ≤ K*|a-b|) :
        |f a^2-f b^2| ≤ 4*(K*|a-b|) := by
      rw [sq_sub_sq,abs_mul]
      nlinarith only [mul_le_mul z ((abs_add_le _ _).trans (add_le_add l r)) (abs_nonneg _) (by positivity)]
    have hp := term p (cap ha).1 (cap hb).1 (h c hc a ha b hb s hs 2)
    have hq := term q (cap ha).2 (cap hb).2 (h c hc a ha b hb s hs 3)
    change |(p a)^2+(q a)^2-((p b)^2+(q b)^2)| ≤ _
    rw [show (p a)^2+(q a)^2-((p b)^2+(q b)^2)=((p a)^2-(p b)^2)+((q a)^2-(q b)^2) by ring]
    linarith only [abs_add_le ((p a)^2-(p b)^2) ((q a)^2-(q b)^2),hp,hq]
  have tot : |A a s-A b t| ≤ (8*K+4*D*B)*|a-b| := by
    linarith only [abs_sub_le (A a s) (A b s) (A b t),varyTime,varyDrive]
  have lip := hJ.dist_le_mul _ (mem ha hs) _ (mem hb ht)
  simp only [Real.dist_eq] at lip
  exact lip.trans (by nlinarith only [mul_le_mul_of_nonneg_left tot J.coe_nonneg])

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.compact_radiusFactor_lipschitz
