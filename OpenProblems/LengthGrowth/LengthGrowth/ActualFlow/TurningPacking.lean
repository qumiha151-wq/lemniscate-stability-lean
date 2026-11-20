import LengthGrowth.ActualFlow.StrongArcCover
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.MacroscopicTurning

private def inside (u v : ℝ) (J : ℝ × ℝ) : Prop := u≤J.1 ∧ J.1<J.2 ∧ J.2≤v
private def separate (S : Finset (ℝ × ℝ)) : Prop :=
  ∀I∈S,∀J∈S, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)

private theorem select_pieces {f : ℝ→ℝ} (hf : Continuous f) (n : ℕ) {u v : ℝ}
    (uv : u≤v) (mass : (n:ℝ)/4≤∫ x in u..v,f x) :
    ∃ S : Finset (ℝ × ℝ), S.card=n ∧ separate S ∧
      ∀J∈S,inside u v J ∧ (∫x in J.1..J.2,f x)=1/4 := by
  classical
  induction n generalizing u with
  | zero => exact ⟨∅,rfl,by simp [separate],by simp⟩
  | succ n ih =>
    let g:=fun y => ∫x in u..y, f x
    have cg : Continuous g := intervalIntegral.continuous_primitive hf.intervalIntegrable u
    have q : (1/4:ℝ)∈Icc (g u) (g v) := by
      constructor
      · simp [g]
      · change 1/4≤∫x in u..v,f x
        push_cast at mass
        linarith [show 0≤(n:ℝ) by positivity]
    obtain ⟨z,hz,eq⟩ := intermediate_value_Icc uv cg.continuousOn q
    change (∫ x in u..z,f x)=1/4 at eq
    have uz : u<z := lt_of_le_of_ne hz.1 (by rintro rfl; simp at eq)
    have rest := intervalIntegral.integral_add_adjacent_intervals (μ:=volume) (hf.intervalIntegrable u z) (hf.intervalIntegrable z v)
    obtain ⟨S,card,sep,good⟩:=ih hz.2 (by push_cast at mass; linarith only [eq,rest,mass])
    have fresh : (u,z)∉S := fun h => (not_le_of_gt uz) (good _ h).1.1
    refine ⟨insert (u,z) S, by simp [fresh,card],?_,?_⟩
    · intro I hi J hj ne
      rcases Finset.mem_insert.mp hi with rfl|hi <;> rcases Finset.mem_insert.mp hj with rfl|hj
      · exact False.elim (ne rfl)
      · exact disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge ((good _ hj).1.1.trans h2.1.le) h1.2)
      · exact disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge ((good _ hi).1.1.trans h1.1.le) h2.2)
      · exact sep _ hi _ hj ne
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl|hj
      · exact ⟨⟨le_rfl,uz,hz.2⟩,eq⟩
      · obtain ⟨⟨lo,lt,up⟩,val⟩:=good _ hj
        exact ⟨⟨uz.le.trans lo,lt,up⟩,val⟩

private theorem lobe_sign {k : ℝ→ℝ} (hk : Continuous k) {a b : ℝ} {I : ℝ × ℝ}
    (hl : Lobe k a b I) : (∀x∈Ioo I.1 I.2,0≤k x) ∨ (∀x∈Ioo I.1 I.2,k x≤0) := by
  by_contra! h
  obtain ⟨⟨x,hx,hn⟩,y,hy,hp⟩ := h
  obtain ⟨z,hz,ke⟩ := isPreconnected_Ioo.intermediate_value hx hy hk.continuousOn
    (show (0:ℝ)∈Icc (k x) (k y) from ⟨hn.le,hp.le⟩)
  exact hl.nonzero z hz ke

private theorem sign_pieces {k : ℝ→ℝ} (hk : Continuous k) {a b : ℝ}
    (hab : a≤b) (sgn : (∀x∈Ioo a b,0≤k x) ∨ (∀x∈Ioo a b,k x≤0)) :
    ∃ S : Finset (ℝ × ℝ), S.card=⌊4*(∫x in a..b, |k x|)⌋₊ ∧ separate S ∧
      ∀J∈S,inside a b J ∧ |∫x in J.1..J.2,k x|=1/4 := by
  have zero_le_int:=intervalIntegral.integral_nonneg_of_forall (μ:=volume) hab (fun x => abs_nonneg (k x))
  obtain ⟨S,card,sep,good⟩:=select_pieces hk.abs ⌊4*(∫x in a..b, |k x|)⌋₊ hab
    (by linarith [Nat.floor_le (show (0:ℝ)≤4*(∫x in a..b, |k x|) by positivity)])
  refine ⟨S,card,sep,?_⟩
  intro J hj
  obtain ⟨inner,mass⟩:=good J hj
  refine ⟨inner,?_⟩
  have sub : Ioo J.1 J.2 ⊆ Ioo a b := fun _ hx => ⟨inner.1.trans_lt hx.1,hx.2.trans_le inner.2.2⟩
  rcases sgn with pos|neg
  · have eq:=intervalIntegral.integral_congr_Ioo_of_le (μ:=volume) inner.2.1.le
      (fun x hx => abs_of_nonneg (pos x (sub hx)))
    rw [eq] at mass
    rw [mass,abs_of_pos (by norm_num)]
  · have eq:=intervalIntegral.integral_congr_Ioo_of_le (μ:=volume) inner.2.1.le
      (fun x hx => abs_of_nonpos (neg x (sub hx)))
    rw [eq,intervalIntegral.integral_neg] at mass
    rw [←abs_neg, mass,abs_of_pos (by norm_num)]

private theorem one_lobe {k : ℝ→ℝ} (hk : Continuous k) {a b : ℝ} {I : ℝ × ℝ}
    (hl : Lobe k a b I) :
    ∃ S : Finset (ℝ × ℝ), S.card=⌊4*(∫x in I.1..I.2, |k x|)⌋₊ ∧ separate S ∧
      ∀J∈S,inside I.1 I.2 J ∧ |∫x in J.1..J.2,k x|=1/4 :=
  sign_pieces hk hl.ordered.le (lobe_sign hk hl)

private theorem floor_bound {θ : ℝ} (h : 1/4≤θ) : θ≤(⌊4*θ⌋₊:ℝ)/2 := by
  have lb : 1≤⌊4*θ⌋₊ := (Nat.le_floor_iff (by linarith : 0≤4*θ)).mpr (by norm_num; linarith)
  have one : (1:ℝ)≤(⌊4*θ⌋₊:ℝ) := by exact_mod_cast lb
  linarith [Nat.lt_floor_add_one (4*θ)]

theorem pack_quarter_turn_sign {k : ℝ→ℝ} (hk : Continuous k) {a b : ℝ} (hab : a≤b)
    (sgn : (∀x∈Ioo a b,0≤k x) ∨ (∀x∈Ioo a b,k x≤0)) (large : 1/4≤∫x in a..b, |k x|) :
    ∃ U : Finset (ℝ × ℝ), U.card=⌊4*(∫x in a..b, |k x|)⌋₊ ∧
      (∫x in a..b, |k x|)≤(U.card:ℝ)/2 ∧
      (∀J∈U,a≤J.1 ∧ J.1<J.2 ∧ J.2≤b ∧ |∫x in J.1..J.2,k x|=1/4) ∧
      (∀I∈U,∀J∈U,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) := by
  obtain ⟨U,card,sep,good⟩:=sign_pieces hk hab sgn
  refine ⟨U,card,card ▸ floor_bound large,?_,sep⟩
  intro J hj
  obtain ⟨⟨lo,ord,up⟩,val⟩:=good J hj
  exact ⟨lo,ord,up,val⟩

/-- Every finite collection of disjoint complete lobes of turning larger
than 1/4 contains floor(4 times turning) disjoint quarter-turn subarcs
per lobe. Their total count controls the total angular mass. -/
theorem pack_quarter_turn_lobes {k : ℝ→ℝ} (hk : Continuous k) {a b : ℝ} {S : Finset (ℝ × ℝ)}
    (hs : ∀I∈S,Lobe k a b I)
    (ds : ∀I∈S,∀J∈S,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2))
    (large : ∀I∈S,(1/4:ℝ)<∫x in I.1..I.2, |k x|) :
    ∃ U : Finset (ℝ × ℝ), U.card=∑I∈S, ⌊4*(∫x in I.1..I.2, |k x|)⌋₊ ∧
      (∑I∈S, ∫x in I.1..I.2, |k x|)≤(U.card:ℝ)/2 ∧
      (∀J∈U,a≤J.1 ∧ J.1<J.2 ∧ J.2≤b ∧ |∫x in J.1..J.2,k x|=1/4) ∧
      (∀I∈U,∀J∈U,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) := by
  classical
  let θ (I : ℝ × ℝ) := ∫x in I.1..I.2, |k x|
  let m (I : ℝ × ℝ) := ⌊4*θ I⌋₊
  let parts (I : ℝ × ℝ) := if h : Lobe k a b I then (one_lobe hk h).choose else ∅
  have spec (I) (hi : I∈S) : (parts I).card=m I ∧ separate (parts I) ∧
      ∀J∈parts I,inside I.1 I.2 J ∧ |∫x in J.1..J.2,k x|=1/4 := by
    simp only [parts,dif_pos (hs I hi)]
    exact (one_lobe hk (hs I hi)).choose_spec
  have into (I) (hi : I∈S) (J) (hj : J∈parts I) : Ioo J.1 J.2 ⊆ Ioo I.1 I.2 := by
    obtain ⟨⟨lo,_,up⟩,_⟩:=(spec I hi).2.2 J hj
    exact fun _ h => ⟨lo.trans_lt h.1,h.2.trans_le up⟩
  have dis : (S:Set (ℝ × ℝ)).PairwiseDisjoint parts := by
    intro I hi K hK neq
    apply Finset.disjoint_left.mpr
    intro J hJ hJ2
    have ord:=((spec _ hi).2.2 _ hJ).1.2.1
    obtain ⟨x,hx⟩:=nonempty_Ioo.mpr ord
    exact Set.disjoint_left.mp (ds I hi K hK neq) (into I hi J hJ hx) (into K hK J hJ2 hx)
  let U:=S.biUnion parts
  have card : U.card=∑I∈S,m I := (Finset.card_biUnion dis).trans (Finset.sum_congr rfl (fun I hi => (spec I hi).1))
  refine ⟨U,card,?_,?_,?_⟩
  · have per I (hi : I∈S) : θ I≤(m I:ℝ)/2 := by
      exact floor_bound (large I hi).le
    rw [card,Nat.cast_sum]
    exact (Finset.sum_le_sum per).trans_eq (by rw [Finset.sum_div])
  · intro J hJ
    obtain ⟨I,hi,hp⟩:=Finset.mem_biUnion.mp hJ
    obtain ⟨⟨lo,ord,up⟩,ve⟩:=(spec I hi).2.2 J hp
    exact ⟨(hs I hi).left.trans lo,ord,up.trans (hs I hi).right,ve⟩
  · intro I hi J hj ne
    obtain ⟨V,hv,hI⟩:=Finset.mem_biUnion.mp hi
    obtain ⟨W,hw,hJ⟩:=Finset.mem_biUnion.mp hj
    by_cases eq : V=W
    · subst W
      exact (spec V hv).2.1 I hI J hJ ne
    · exact (ds V hv W hw eq).mono (into V hv I hI) (into W hw J hJ)

end LengthGrowth.ActualFlow.MacroscopicTurning
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.pack_quarter_turn_sign
#print axioms LengthGrowth.ActualFlow.MacroscopicTurning.pack_quarter_turn_lobes
