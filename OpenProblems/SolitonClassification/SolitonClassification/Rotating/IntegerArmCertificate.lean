import SolitonClassification.Rotating.IntegerMovingEndpoint
import SolitonClassification.Rotating.ShootingVariation
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Metric Filter DyadicReset
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Numerical interfaces for the initial and final rows of a signed tape.
They involve only rational/dyadic data and their specified real casts. -/
structure TapeNumbers {n : ℤ} (T : PolynomialTape n 4000) (q : Fin 6 → ℚ)
    (cols : ParameterMatrix) : Prop where
  stepSmall : |step n|≤1/125
  origin : matrixPath (T.data 0) 0=1
  initialError : ‖shootingInitial phase center-path (T.data 0) d 0‖≤1/10^71
  stateEnd : path (T.data 3999) d 1=realState q
  stateSize : ∀j : Fin 6, |q j|≤8
  matrixSize : ‖matrixPath (T.data 3999) 1‖≤5000
  columnsEnd : ∀j i, (cols j i:ℝ)=(matrixPath (T.data 3999) 1)
    (basisVector (n:=6) j.castSucc) (physicalIndex i)

theorem in_arm_ball {n : ℤ} {T : PolynomialTape n 4000} {q : Fin 6 → ℚ}
    {cols : ParameterMatrix} (h : TapeNumbers T q cols) {c : Parameters} (hc : c∈cube) :
    shootingInitial phase c∈ball (path (T.data 0) d 0) (2/10^30) := by
  rw [mem_ball,dist_eq_norm]
  have e0 : |phase 0|≤1 := by norm_num [phase,phaseQ]
  have e1 : |phase 1|≤1 := by norm_num [phase,phaseQ]
  have change := shootingInitial_norm_bound phase e0 e1 (c-center)
  rw [map_sub] at change
  have r : ‖c-center‖≤1/(10:ℝ)^30 := hc
  exact (norm_sub_le_norm_sub_add_norm_sub _ (shootingInitial phase center) _).trans_lt
    (by linarith [h.initialError])

def selectedDerivative (p : ℝ×State) := fderiv ℝ wideFlow p

private theorem input_norm (j : Fin 5) : ‖basisVector (n:=6) j.castSucc‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  by_cases h : j.castSucc=i <;> simp [basisVector,h]

/-- The moving-time arm obligations of the contraction follow from the
signed cell tape and finite endpoint numbers. -/
theorem arm_from_tape {n : ℤ} (T : PolynomialTape n 4000) {q : Fin 6 → ℚ}
    {cols : ParameterMatrix} (num : TapeNumbers T q cols)
    (input : Parameters →L[ℝ] (ℝ×State)) (hinit : ∀c,(input c).2=shootingInitial phase c)
    (hcenter : (input center).1=4000*step n)
    (htime : ∀c∈cube, |(input c).1-(input center).1|≤1/10^30) :
    ArmBounds wideFlow selectedDerivative input q cols := by
  let s := (4000:ℝ)*step n
  let P := matrixPath (T.data 3999) 1
  have last (c : Parameters) (hc : c∈cube) := fixed_time_shooting_bounds T num.stepSmall num.origin
    _ (in_arm_ball num hc) 3999 (by decide) 1 (by norm_num [unitCell])
  have get (c : Parameters) (hc : c∈cube) :
      let a := shootingInitial phase c
      let y := wideFlow (s,a)
      let J := fderiv ℝ (fun b => wideFlow (s,b)) a
      ‖y-realState q‖≤5/10^26 ∧
      (‖a-path (T.data 0) d 0‖≤1/10^71 → ‖y-realState q‖≤5/10^52) ∧
      HasFDerivAt (fun b => wideFlow (s,b)) J a ∧ ‖J-P‖≤3/10^12 := by
    have h := (last c hc).2.2
    simpa only [s,P,Nat.cast_ofNat,show (3999:ℝ)+1=4000 by norm_num,num.stateEnd] using h
  have fixedcenter : center∈cube := mem_closedBall_self (by positivity)
  have moving (c : Parameters) (hc : c∈cube) :
      let a := shootingInitial phase c
      let z := input c
      ∃ M : FlowEnd, HasFDerivAt wideFlow (fullDifferential z.1 a M) z ∧
        ‖M-P‖≤1/10^11 ∧ ‖wideFlow z-realState q‖≤1/10^12 ∧
        StateBox (wideFlow z) := by
    let a := shootingInitial phase c
    let u := (input c).1
    let τ := u-s
    let J := fderiv ℝ (fun b => wideFlow (s,b)) a
    have hu : input c=(u,a) := Prod.ext rfl (hinit c)
    have ht : |τ|≤1/10^30 := by simpa only [τ,u,←hcenter,s] using htime c hc
    have st := get c hc
    have margin (i : Fin 6) (hi : i.val<5) : |wideFlow (s,a) i|≤9 := by
      have eq := (coordinate_bound (wideFlow (s,a)-realState q) i).trans st.1
      change |wideFlow (s,a) i-realState q i|≤_ at eq
      have hq : |realState q i|≤8 := by
        simpa only [realState,Rat.cast_abs,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr (num.stateSize i)
      have tri := abs_add_le (wideFlow (s,a) i-realState q i) (realState q i)
      rw [sub_add_cancel] at tri
      linarith
    have nj : ‖J‖≤5001 := by
      have size : ‖P‖≤5000 := num.matrixSize
      have prox : ‖J-P‖≤3/(10:ℝ)^12 := st.2.2.2
      calc
        _ = ‖(J-P)+P‖ := by rw [sub_add_cancel]
        _ ≤ ‖J-P‖+‖P‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    obtain ⟨M,dm,mm,yy⟩ := move_endpoint ht st.2.2.1 margin nj
    have su : s+τ=u := by dsimp [τ];ring
    rw [su] at dm yy
    have hp : ‖M-P‖≤1/(10:ℝ)^11 := (norm_sub_le_norm_sub_add_norm_sub M J P).trans (by
      linarith [st.2.2.2])
    have hy : ‖wideFlow (u,a)-realState q‖≤1/(10:ℝ)^12 :=
      (norm_sub_le_norm_sub_add_norm_sub _ (wideFlow (s,a)) _).trans (by linarith [st.1])
    refine ⟨M,by simpa only [hu] using dm,hp,hu ▸ hy,?_⟩
    rw [hu]
    intro i hi
    have de := (coordinate_bound (wideFlow (u,a)-wideFlow (s,a)) i).trans yy
    change |wideFlow (u,a) i-wideFlow (s,a) i|≤_ at de
    have tri := abs_add_le (wideFlow (u,a) i-wideFlow (s,a) i) (wideFlow (s,a) i)
    rw [sub_add_cancel] at tri
    linarith [margin i hi]
  constructor
  · have e := (get center fixedcenter).2.1 num.initialError
    have iz : input center=(s,shootingInitial phase center) := Prod.ext hcenter (hinit center)
    rw [iz]
    exact e.trans (by norm_num)
  · intro c hc
    exact (moving c hc).choose_spec.2.2.1
  · intro c hc
    exact (moving c hc).choose_spec.1.differentiableAt.hasFDerivAt
  · intro c hc
    obtain ⟨M,der,_,_,box⟩ := moving c hc
    rw [selectedDerivative,der.fderiv]
    change (1:ℝ) • wideField (wideFlow ((input c).1,shootingInitial phase c))+M 0=_
    rw [one_smul,map_zero,add_zero,←hinit c,Prod.mk.eta,wideField,wideClip_id box]
  · intro c hc j i
    obtain ⟨M,der,m,_,_⟩ := moving c hc
    rw [selectedDerivative,der.fderiv,num.columnsEnd]
    let v := basisVector (n:=6) j.castSucc
    change |P v (physicalIndex i)-((0:ℝ) • _+M v) (physicalIndex i)|≤_
    rw [zero_smul,zero_add]
    have vnorm := input_norm j
    have eq := coordinate_bound ((P-M) v) (physicalIndex i)
    have op := ((P-M).le_opNorm v).trans (mul_le_mul (by simpa only [norm_sub_rev] using m)
      vnorm (norm_nonneg _) (by positivity))
    exact eq.trans (op.trans_eq (by ring))

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.arm_from_tape
