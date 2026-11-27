import SolitonClassification.Rotating.IntegerWindingTrueStep
import SolitonClassification.Rotating.IntegerWindingFirstReplay
import SolitonClassification.Rotating.IntegerWindingStepUniqueness

namespace SolitonClassification.Rotating.IntegerWinding
noncomputable section
open Set Metric Polynomial UniversalMajorant
set_option maxRecDepth 500000
set_option maxHeartbeats 3000000

/-- The five decimals and the phase line are the exact published shooting inputs. -/
def center (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => 7.75911663705979640164486279788885102854646819372172115107133125419672015
  | 1 => 0.157842952057178233280344086508722201568222800593116128244379696887796363
  | 2 => 30.2106169881485265812773368836096284212451340576862482346806333626589531
  | 3 => 0.105822679845287219660933106605646552091643631528686773299157687368964270
  | _ => 0.106444255274622251153299378466623537798940318186715100653544012696897789
def phaseE : ℚ := -0.05995393111634394
def phaseG : ℚ := -0.9982011451324311

def initial (c : Fin 5 → ℝ) (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => c 0
  | 1 => c 3*(phaseE:ℝ)/8
  | 2 => c 1
  | 3 => c 3*(phaseG:ℝ)
  | 4 => c 4
  | _ => 0

def shootingCube (c : Fin 5 → ℝ) : Prop :=
  ∀ i, |c i-(center i:ℝ)| ≤ 1/10^30

private theorem state_perturbation {c : Fin 5 → ℝ} (hc : shootingCube c)
    (i : Fin 6) : |initial c i-initial (fun j => (center j:ℝ)) i| ≤ 1/10^30 := by
  fin_cases i
  · exact hc 0
  · change |c 3*(phaseE:ℝ)/8-(center 3:ℝ)*(phaseE:ℝ)/8| ≤ _
    rw [show c 3*(phaseE:ℝ)/8-(center 3:ℝ)*(phaseE:ℝ)/8 =
      (c 3-(center 3:ℝ))*((phaseE:ℝ)/8) by ring,abs_mul]
    calc
      _ ≤ (1/10^30)*|((phaseE:ℝ)/8)| := mul_le_mul_of_nonneg_right (hc 3) (abs_nonneg _)
      _ ≤ _ := by norm_num [phaseE]
  · exact hc 1
  · change |c 3*(phaseG:ℝ)-(center 3:ℝ)*(phaseG:ℝ)| ≤ _
    rw [←sub_mul,abs_mul]
    calc
      _ ≤ (1/10^30)*|(phaseG:ℝ)| := mul_le_mul_of_nonneg_right (hc 3) (abs_nonneg _)
      _ ≤ _ := by norm_num [phaseG]
  · exact hc 4
  · norm_num [initial]

private theorem first_input_contains {c : Fin 5 → ℝ} (hc : shootingCube c)
    (i : Fin 6) : firstInputs[i.val].Contains scale (initial c i) := by
  have h := state_perturbation hc i
  by_cases hi : i=5
  · subst i
    change |(0:ℝ)-((0:ℚ)/10^64:ℚ)| ≤ ((0:ℚ)/10^64:ℚ)
    norm_num
  · let m := initial (fun j => (center j:ℝ)) i
    let v := firstInputs[i.val]
    change |initial c i-(((v.center:ℚ)/scale:ℚ):ℝ)| ≤ (((v.radius:ℚ)/scale:ℚ):ℝ)
    calc
      _ ≤ |initial c i-m|+|m-(((v.center:ℚ)/scale:ℚ):ℝ)| := abs_sub_le _ _ _
      _ ≤ 1/10^30+|m-(((v.center:ℚ)/scale:ℚ):ℝ)| := add_le_add h le_rfl
      _ ≤ _ := by
        fin_cases i <;> first | contradiction | norm_num [v,m,firstInputs,scale,initial,center,phaseE,phaseG, Matrix.cons_val]

private theorem cube_in_nodeBox {c : Fin 5 → ℝ} (hc : shootingCube c) :
    initial c ∈ nodeBox := by
  have b (i : Fin 6) : |initial c i| ≤ 1/10^30+|initial (fun j => (center j:ℝ)) i| := by
    calc
      _ = |(initial c i-initial (fun j => (center j:ℝ)) i)+initial (fun j => (center j:ℝ)) i| :=
        by rw [sub_add_cancel]
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (state_perturbation hc i) le_rfl)
  exact ⟨(b 0).trans (by norm_num [initial,center,phaseE,phaseG,Matrix.cons_val]),
    (b 1).trans (by norm_num [initial,center,phaseE,phaseG,Matrix.cons_val]),
    (b 2).trans (by norm_num [initial,center,phaseE,phaseG,Matrix.cons_val]),
    (b 3).trans (by norm_num [initial,center,phaseE,phaseG,Matrix.cons_val]),
    (b 4).trans (by norm_num [initial,center,phaseE,phaseG,Matrix.cons_val])⟩

private theorem time_in_cap {c : Fin 5 → ℝ} (hc : shootingCube c) :
    c 2/4000 ∈ Icc 0 (universalStepCap:ℝ) := by
  have h := abs_le.mp (hc 2)
  norm_num [center,Matrix.cons_val,universalStepCap] at h ⊢
  constructor <;> linarith [h.1,h.2]

private theorem time_enclosure {c : Fin 5 → ℝ} (hc : shootingCube c) (pos : Bool) :
    (if pos then timePlus else timeMinus).Contains scale
      ((if pos then (1:ℝ) else -1)*(c 2/4000)) := by
  have h := abs_le.mp (hc 2)
  norm_num [center,Matrix.cons_val] at h
  cases pos <;> change |_-_| ≤ _
  all_goals
    norm_num [timeMinus,timePlus,scale,FixedBall.Contains,FixedBall.toRational,RationalBall.Contains]
    rw [abs_le]
    constructor <;> linarith [h.1,h.2]

private theorem polynomialBox_sound {a : State} {tb : FixedBall} {t : ℝ}
    (ha : ∀i : Fin 6, firstInputs[i.val].Contains scale (a i)) (ht : tb.Contains scale t)
    (i : Fin 6) :
    (polynomialBox tb)[i.val].Contains scale ((taylorPolynomial a 60 i).eval t) := by
  have h := checked_recurrence.sound (by norm_num [scale]) (fun i => by rw [checked_input]; exact ha i)
  have he : (taylorPolynomial a 60 i).eval t=
      ∑ j ∈ Finset.range (60+1),taylorCoeff a j i*t^j := by
    simp [taylorPolynomial,Polynomial.eval_finsetSum]
  rw [he]
  simpa only [polynomialBox,Vector.getElem_ofFn,Nat.zero_add] using
    fixedHorner_contains (S:=scale) (by norm_num [scale]) tb t ht
      (fun j => coefficientTable.coefficient j i)
      (fun j => taylorCoeff a j i) 0 61
      (fun j hj => by simpa only [Nat.zero_add] using h.coefficients j (by omega) i)

/-- Both signed first endpoints of the entire five-parameter shooting cube, 
evaluated at its own varying step length. Each reported fixed-mesh radius
is enlarged by exactly the proven analytic Taylor tail. -/
theorem cube_first_endpoint {c : Fin 5 → ℝ} (hc : shootingCube c) (pos : Bool) :
    let σ : ℝ := if pos then 1 else -1
    let data := if pos then positivePolynomial else negativePolynomial
    ∃ x : ℝ → State, x 0=initial c ∧
      (∀s ∈ Ioo (-(1/125:ℝ)) (1/125), HasDerivAt x (σ • field (x s)) s) ∧
      ∀ i : Fin 6, |x (c 2/4000) i-(((data[i.val].center:ℚ)/scale:ℚ):ℝ)|
        ≤ (((data[i.val].radius:ℚ)/scale:ℚ):ℝ)+2/10^59 := by
  dsimp only
  let σ : ℝ := if pos then 1 else -1
  let tb := if pos then timePlus else timeMinus
  have hs : |σ|≤1 := by cases pos <;> norm_num [σ]
  obtain ⟨x,h0,hx,he⟩ := exists_true_taylor_step (cube_in_nodeBox hc) σ hs
  refine ⟨x,h0,hx,fun i => ?_⟩
  have hpoly := polynomialBox_sound (first_input_contains hc) (time_enclosure hc pos) i
  have hid : polynomialBox tb = (if pos then positivePolynomial else negativePolynomial) := by
    cases pos
    · exact negative_replay
    · exact positive_replay
  change (polynomialBox tb)[i.val].Contains scale ((taylorPolynomial (initial c) 60 i).eval (σ*(c 2/4000))) at hpoly
  rw [hid] at hpoly
  have tail := (coordinate_bound _ i).trans (he _ (time_in_cap hc))
  change |x (c 2/4000) i-(taylorPolynomial (initial c) 60 i).eval (σ*(c 2/4000))|≤2/10^59 at tail
  exact (abs_sub_le _ _ _).trans ((add_le_add tail hpoly).trans_eq (add_comm _ _))

theorem first_endpoint_radius : ∀ (pos : Bool) (i : Fin 6),
    let data := if pos then positivePolynomial else negativePolynomial
    (data[i.val].radius:ℚ)/scale + 2/10^59 < 1097/10^33 := by decide +kernel

/-- A previously supplied trajectory of the original equation satisfies the
same coordinate enclosures without a bound on its image. -/
theorem every_cube_first_endpoint {c : Fin 5 → ℝ} (hc : shootingCube c) (pos : Bool)
    {x : ℝ → State} (h0 : x 0=initial c)
    (hx : ∀s ∈ Icc 0 (universalStepCap:ℝ),
      HasDerivAt x ((if pos then (1:ℝ) else -1) • field (x s)) s) (i : Fin 6) :
    let data := if pos then positivePolynomial else negativePolynomial
    |x (c 2/4000) i-(((data[i.val].center:ℚ)/scale:ℚ):ℝ)| < 1097/10^33 := by
  obtain ⟨y,hy0,hy,he⟩ := cube_first_endpoint hc pos
  have hd s (hs : s∈Icc 0 (universalStepCap:ℝ)) :
      HasDerivAt y ((if pos then (1:ℝ) else -1) • field (y s)) s :=
    hy s ⟨by linarith [hs.1],hs.2.trans_lt (by norm_num [universalStepCap])⟩
  rw [signed_solution_agreement hx hd (h0.trans hy0.symm) (time_in_cap hc)]
  apply (he i).trans_lt
  have h := (Rat.cast_lt (K:=ℝ)).mpr (first_endpoint_radius pos i)
  simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using h

end
end SolitonClassification.Rotating.IntegerWinding

#print axioms SolitonClassification.Rotating.IntegerWinding.cube_first_endpoint
#print axioms SolitonClassification.Rotating.IntegerWinding.every_cube_first_endpoint
