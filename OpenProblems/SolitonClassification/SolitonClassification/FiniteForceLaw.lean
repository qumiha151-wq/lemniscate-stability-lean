import SolitonClassification.InflectionForceBranches
import SolitonClassification.SeparatedEarlyInflections

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

/-- Even a fixed finite number of separately chosen functions of curvature
cannot approximate the elastic force to a fixed error on all closed profiles
of dilation coefficient one. On the witness, one simple inflection defeats
all the functions simultaneously in every traversal from its centre mark. -/
theorem unbounded_error_for_finite_force_laws (n : ℕ) (M : ℝ) :
    ∃ b>0, ∃ L>0, ∃ P : ZeroTurnExpander L b,
      ∀ d>0, Function.Periodic P.X d → Function.Periodic P.Y d →
      ∀ G : Fin n → ℝ → ℝ, ∃ s∈Ioo 0 d, P.k s=0 ∧ deriv P.k s≠0 ∧
        ∀ i, M < |deriv (deriv P.k) s+(P.k s)^3/2-G i (P.k s)| := by
  classical
  let A := max 0 M+1
  have ap : 0<A := by dsimp [A]; linarith [le_max_left 0 M]
  have ma : M<A := by dsimp [A]; linarith [le_max_right 0 M]
  obtain ⟨B,select⟩ := ZeroTurnExpander.separated_early_simple_inflections (n+1) (144*A) (by positivity)
  obtain ⟨b,high,L,lp,⟨P⟩⟩ := unbounded_closed_zero_turn_expanders (max 32 B)
  have large : 32≤b := (le_max_left ..).trans high.le
  have bp : 0<b := by linarith
  obtain ⟨v,info,spaced⟩ := select ((le_max_right ..).trans high.le) P
  refine ⟨b,bp,L,lp,P,?_⟩
  intro d dp px py G
  have bound := P.lower_bound_for_each_period large dp px py
  let F := fun j => deriv (deriv P.k) (v j)
  have within (i) : v i≤Real.sqrt b/2 := by linarith [(info i).2.1,Real.sqrt_nonneg b]
  by_contra! bad
  have near (j : Fin (n+1)) : ∃ i, |F j-G i 0|≤M := by
    obtain ⟨i,h⟩ := bad (v j) ⟨(info j).1,(info j).2.1.trans_lt bound⟩ (info j).2.2.1 (info j).2.2.2
    exact ⟨i,by simpa [F,(info j).2.2.1] using h⟩
  choose branch fits using near
  have impossible (i j : Fin (n+1)) (diff : i ≠ j) (order : v i≤v j) (same : branch i=branch j) : False := by
    have far := spaced j i diff.symm
    rw [abs_of_nonneg (sub_nonneg.mpr order)] at far
    have low := P.force_gap_on_initial_zeros large (info i).1.le order (within j)
      (info i).2.2.1 (info j).2.2.1
    have one := fits i
    rw [same] at one
    have distance : |F j-F i|≤2*M := by
      calc
        |F j-F i| ≤ |F j-G (branch j) 0|+|G (branch j) 0-F i| := abs_sub_le _ _ _
        _ ≤ 2*M := by rw [abs_sub_comm (G (branch j) 0)]; linarith [fits j]
    have close := (abs_sub_abs_le_abs_sub (F j) (F i)).trans distance
    change (v j-v i)/72≤|F j|-|F i| at low
    linarith
  have single : Function.Injective branch := by
    intro i j same
    by_contra diff
    rcases le_total (v i) (v j) with ij|ji
    · exact impossible i j diff ij same
    · exact impossible j i (fun h => diff h.symm) ji same.symm
  have card := Fintype.card_le_of_injective branch single
  simp only [Fintype.card_fin] at card
  omega

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.unbounded_error_for_finite_force_laws
