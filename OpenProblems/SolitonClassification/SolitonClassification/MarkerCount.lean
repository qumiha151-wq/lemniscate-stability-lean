import SolitonClassification.RectangleCrossing

open Set

namespace SolitonClassification.Reflected.Rectangle

/-- Finite counting form of the matching argument. Each separated phase level
    forces a distinct marker in the same prescribed interval, even if the
    incoming phase oscillates and the seam datum is nonunique. -/
theorem separated_matching_markers
    (a B c d M : ℝ) (hab : a ≤ B) (hcd : c ≤ d)
    (phase impact : ℝ → ℝ) (seamPhase seamImpact : ℝ × ℝ → ℝ)
    (regular : ContinuousOn (fun p : ℝ × ℝ =>
      (phase p.1 - seamPhase p, seamImpact p - impact p.1)) (box a B c d))
    (bounded : ∀ x ∈ Icc a B, ∀ y ∈ Icc c d, |seamPhase (x,y)| ≤ M)
    (low : ∀ x ∈ Icc a B, seamImpact (x,c) < impact x)
    (high : ∀ x ∈ Icc a B, impact x < seamImpact (x,d))
    (N : ℕ) (level : Fin N → ℝ)
    (left : ∀ i, phase a + M < level i)
    (right : ∀ i, level i + M < phase B)
    (gap : ∀ i j, i < j → 2*M < level j - level i) :
    ∃ marker seam : Fin N → ℝ, Function.Injective marker ∧
      ∀ i, marker i ∈ Icc a B ∧ seam i ∈ Icc c d ∧
        phase (marker i) = seamPhase (marker i,seam i) + level i ∧
        impact (marker i) = seamImpact (marker i,seam i) := by
  classical
  have one (i : Fin N) : ∃ x ∈ Icc a B, ∃ y ∈ Icc c d,
      phase x = seamPhase (x,y) + level i ∧ impact x = seamImpact (x,y) := by
    let F (p : ℝ × ℝ) := (phase p.1 - seamPhase p - level i, seamImpact p - impact p.1)
    obtain ⟨p,hp,hz⟩ := zero_in_box a B c d hab hcd F
      ((regular.fst.sub continuousOn_const).prodMk regular.snd)
      (fun y hy => by
        have := (abs_le.mp (bounded a ⟨le_rfl,hab⟩ y hy)).1
        dsimp [F]; linarith [left i])
      (fun y hy => by
        have := (abs_le.mp (bounded B ⟨hab,le_rfl⟩ y hy)).2
        dsimp [F]; linarith [right i])
      (fun x hx => sub_neg.mpr (low x hx)) (fun x hx => sub_pos.mpr (high x hx))
    have e₁ := congrArg Prod.fst hz
    have e₂ := congrArg Prod.snd hz
    change phase p.1 - seamPhase p - level i = 0 at e₁
    change seamImpact p - impact p.1 = 0 at e₂
    exact ⟨p.1,⟨hp.1.1,hp.2.1⟩,p.2,⟨hp.1.2,hp.2.2⟩,by linarith,by linarith⟩
  choose x hx y hy hphase himpact using one
  have distinct {i j : Fin N} (hij : i < j) : x i ≠ x j := by
    intro same
    have ei := hphase i
    rw [same] at ei
    have hi := (abs_le.mp (bounded (x j) (hx j) (y i) (hy i))).2
    have hj := (abs_le.mp (bounded (x j) (hx j) (y j) (hy j))).1
    linarith [hphase j,gap i j hij]
  refine ⟨x,y,?_,fun i => ⟨hx i,hy i,hphase i,himpact i⟩⟩
  intro i j eq
  rcases lt_trichotomy i j with h | h | h
  · exact (distinct h eq).elim
  · exact h
  · exact (distinct h eq.symm).elim

end SolitonClassification.Reflected.Rectangle
#print axioms SolitonClassification.Reflected.Rectangle.separated_matching_markers
