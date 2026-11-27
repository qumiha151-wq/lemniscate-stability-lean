import SolitonClassification.Rotating.ResetDependence
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false

def remBound : ℕ→ℝ
  | 0=>0
  | n+1=>2*(remBound n+((2:ℝ)^n)^2)

def Joined (N : ℕ) (a : State) (f : ℕ→ℝ→State) := ∀i,i<N →
  f i 0=(if i=0 then a else f (i-1) 1)
def JoinedMatrix (N : ℕ) (J : ℕ→ℝ→FlowEnd) := ∀i,i<N →
  J i 0=(if i=0 then 1 else J (i-1) 1)

theorem family_remainder {N : ℕ} {s : ℝ} (hs : |s|≤1/100) {a b : State}
    {x y : ℕ→ℝ→State} (jx : Joined N a x) (jy : Joined N b y)
    (dx : ∀i,i<N→FollowsState s (x i)) (dy : ∀i,i<N→FollowsState s (y i))
    (bx : ∀i,i<N→∀t∈unitCell,StateBox (x i t))
    (by0 : ∀i,i<N→∀t∈unitCell,StateBox (y i t))
    (diam : ∀i,i<N→∀t∈unitCell,‖y i t-x i t‖≤1)
    (J : ℕ→ℝ→FlowEnd) (jJ : JoinedMatrix N J)
    (dJ : ∀i,i<N→∀t∈unitCell,HasDerivWithinAt (J i) (actualCoefficient s (x i) t*J i t) unitCell t) :
    ∀i,i<N→∀t∈unitCell,‖y i t-x i t‖≤(2:ℝ)^(i+1)*‖b-a‖ ∧
      ‖y i t-x i t-J i t (b-a)‖≤remBound (i+1)*‖b-a‖^2 := by
  intro i
  induction i with
  | zero =>
    intro hi t ht
    have z := cell_initial_remainder hs (dx 0 hi) (dy 0 hi) (bx 0 hi) (by0 0 hi) (diam 0 hi)
      (J 0) (dJ 0 hi) (b-a)
    have l:=z.1 t ht
    have r:=z.2 t ht
    simp only [jx 0 hi,jy 0 hi,jJ 0 hi,if_true] at l r
    simpa [remBound] using And.intro l r
  | succ i ih =>
    intro hi t ht
    have z := cell_initial_remainder hs (dx _ hi) (dy _ hi) (bx _ hi) (by0 _ hi) (diam _ hi)
      (J _) (dJ _ hi) (b-a)
    have l:=z.1 t ht
    have r:=z.2 t ht
    simp only [jx _ hi,jy _ hi,jJ _ hi,Nat.succ_ne_zero,if_false,Nat.add_one_sub_one] at l r
    obtain ⟨prev,rem⟩:=ih (by omega) 1 (by norm_num [unitCell])
    have sq:= (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr prev
    constructor
    · exact l.trans ((mul_le_mul_of_nonneg_left prev (by norm_num)).trans_eq (by ring))
    · exact r.trans ((mul_le_mul_of_nonneg_left (add_le_add rem sq) (by norm_num)).trans_eq (by simp only [remBound];ring))

/-- For any selection of actual flows on a neighborhood, the previously
constructed variational matrix is the Fréchet derivative of the endpoint
map with respect to the original six-dimensional initial condition. -/
theorem actual_endpoint_fderiv {N : ℕ} {s : ℝ} (hs : |s|≤1/100) {a : State}
    {S : Set State} (nb : S∈𝓝 a) (X : State→ℕ→ℝ→State)
    (joins : ∀b∈S,Joined N b (X b)) (ode : ∀b∈S,∀i,i<N→FollowsState s (X b i))
    (box : ∀b∈S,∀i,i<N→∀t∈unitCell,StateBox (X b i t))
    (close : ∀b∈S,∀i,i<N→∀t∈unitCell,‖X b i t-X a i t‖≤1)
    (J : ℕ→ℝ→FlowEnd) (jJ : JoinedMatrix N J)
    (dJ : ∀i,i<N→∀t∈unitCell,HasDerivWithinAt (J i) (actualCoefficient s (X a i) t*J i t) unitCell t) :
    ∀i,i<N→∀t∈unitCell,HasFDerivAt (fun b=>X b i t) (J i t) a := by
  have aIn := mem_of_mem_nhds nb
  have nearby : ∀ᶠ h : State in 𝓝 0, a+h∈S := by
    have cont : ContinuousAt (fun h : State=>a+h) 0 := continuous_const.continuousAt.add continuous_id.continuousAt
    exact cont (by simpa using nb)
  intro i hi t ht
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsBigO.trans_isLittleO (g:=fun h : State=>‖h‖^2) _ (isLittleO_norm_pow_id one_lt_two)
  apply Asymptotics.isBigO_iff.mpr ⟨remBound (i+1),?_⟩
  filter_upwards [nearby] with h hIn
  have b:=family_remainder hs (joins a aIn) (joins (a+h) hIn) (ode a aIn) (ode (a+h) hIn)
    (box a aIn) (box (a+h) hIn) (close (a+h) hIn) J jJ dJ i hi t ht
  simpa only [add_sub_cancel_left,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖h‖)] using b.2
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.actual_endpoint_fderiv
