import SolitonClassification.Rotating.ResetLinearPropagation
namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false

private theorem solution_cont {s : ℝ} {x : ℝ→State} (hx : FollowsState s x) :
    ContinuousOn x unitCell := fun t ht=>(hx t ht).continuousWithinAt

def actualCoefficient (s : ℝ) (x : ℝ→State) (t : ℝ) : FlowEnd :=
  s • fderiv ℝ field (x t)
def relativeCoefficient {s : ℝ} (c : MetricCell s) (x : ℝ→State) (t : ℝ) : FlowEnd :=
  flowMetricCoefficient (actualCoefficient s x t) (c.M t) (c.dM t)
def coefficientBound (D : ℝ) := 5000*((1/100)*(5*D)*5000+6*eps)

theorem relative_cont {s : ℝ} (c : MetricCell s) (x : ℝ→State) (hx : FollowsState s x)
    (cd : ContinuousOn c.dM unitCell) : ContinuousOn (relativeCoefficient c x) unitCell := by
  have cm : ContinuousOn c.M unitCell := fun t _=>(c.variation_deriv t).continuousAt.continuousWithinAt
  have ca : ContinuousOn (actualCoefficient s x) unitCell :=
    (field_fderiv_differentiable.continuous.comp_continuousOn (solution_cont hx)).const_smul s
  exact (referenceInverse_continuousOn cm c.unit).mul ((ca.mul cm).sub cd)

theorem relative_bound {s D : ℝ} (hs : |s|≤1/100) (h1 : D≤1) (c : MetricCell s)
    (x : ℝ→State) (close : ∀t∈unitCell,‖x t-c.Q t‖≤D) (t : ℝ) (ht : t∈unitCell) :
    ‖relativeCoefficient c x t‖≤coefficientBound D := by
  let A := actualCoefficient s x t
  let B := s • fderiv ℝ field (c.Q t)
  let Z := c.dM t-B*c.M t
  have hZ : ‖Z‖≤6*eps := c.var_res t ht
  have a : ‖A-B‖≤(1/100)*(5*D) := by
    change ‖s • fderiv ℝ field (x t)-s • fderiv ℝ field (c.Q t)‖≤_
    have ee : s • fderiv ℝ field (x t)-s • fderiv ℝ field (c.Q t)=s • (fderiv ℝ field (x t)-fderiv ℝ field (c.Q t)) := by ext u i;simp [smul_sub]
    rw [ee,norm_smul,Real.norm_eq_abs]
    apply mul_le_mul hs _ (norm_nonneg _) (by norm_num)
    exact (derivative_wide (c.inner t ht 0 (by decide)) ((close t ht).trans h1)).trans
      (mul_le_mul_of_nonneg_left (close t ht) (by norm_num))
  have Dpos := (norm_nonneg _).trans (close t ht)
  have b := flowMetricCoefficient_norm_bound (A:=A) (B:=B) (M:=c.M t) (Z:=Z)
    (by norm_num : (0:ℝ)≤5000) (by positivity : 0≤(1/100:ℝ)*(5*D)) (c.inverse_norm t ht) (c.matrix_norm t ht) a hZ
  change ‖flowMetricCoefficient A (c.M t) (c.dM t)‖≤_
  simpa only [Z,add_sub_cancel,coefficientBound] using b

theorem variation_chain {s : ℝ} (c : ℕ→MetricCell s) (N : ℕ) (x : ℕ→ℝ→State)
    {D : ℝ} (hs : |s|≤1/100) (hD : D≤1)
    (der : ∀i,i<N→FollowsState s (x i))
    (close : ∀i,i<N→∀t∈unitCell,‖x i t-(c i).Q t‖≤D)
    (continuous : ∀i,i<N→ContinuousOn (c i).dM unitCell)
    (join : ∀i,i+1<N→(c i).M 1=(c (i+1)).M 0)
    (h8 : coefficientBound D≤1/8) (h4 : (N:ℝ)*(2*coefficientBound D)≤1/4) :
    ∃J : ℕ→ℝ→FlowEnd, ∀i,i<N →
      J i 0=(if i=0 then (c 0).M 0 else J (i-1) 1) ∧
      (∀t∈unitCell,HasDerivWithinAt (J i) (actualCoefficient s (x i) t*J i t) unitCell t) ∧
      ∀t∈unitCell,‖J i t-(c i).M t‖≤5000*((i:ℝ)+1)*(2*coefficientBound D) := by
  classical
  let H := fun i=>relativeCoefficient (c i) (x i)
  let δ := coefficientBound D
  let good (i : ℕ) (v : FlowEnd) := ‖v-1‖≤(i:ℝ)*(2*δ)
  have dr (i : ℕ) (hi : i<N) (t : ℝ) (ht : t∈unitCell) : ‖H i t‖≤δ :=
    relative_bound hs hD (c i) (x i) (close i hi) t ht
  have cap (i : ℕ) (hi : i<N) : (i:ℝ)*(2*δ)≤1/4 := by
    have p := (norm_nonneg _).trans (dr i hi 0 (by norm_num [unitCell]))
    exact (mul_le_mul_of_nonneg_right (show (i:ℝ)≤N by exact_mod_cast hi.le) (by positivity)).trans h4
  let oneStep (i : ℕ) (v : FlowEnd) (hv : i<N ∧ good i v) :=
    linear_step (relative_cont (c i) (x i) (der i hv.1) (continuous i hv.1)) h8 (dr i hv.1) v (hv.2.trans (cap i hv.1))
  let U (i : ℕ) (v : FlowEnd) := if hv : i<N ∧ good i v then (oneStep i v hv).choose else fun _=>v
  have follow (i : ℕ) (v : FlowEnd) (hi : i<N) (hv : good i v) :
      U i v 0=v ∧ (∀t∈unitCell,HasDerivWithinAt (U i v) (H i t*U i v t) unitCell t) ∧
      ∀t∈unitCell,‖U i v t-1‖≤((i:ℝ)+1)*(2*δ) := by
    dsimp only [U];rw [dif_pos (show i<N ∧ good i v from ⟨hi,hv⟩)]
    obtain ⟨ini,ode,err⟩ := (oneStep i v ⟨hi,hv⟩).choose_spec
    refine ⟨ini,ode,fun t ht=>(norm_sub_le_norm_sub_add_norm_sub _ v 1).trans ((add_le_add (err t ht) hv).trans_eq ?_)⟩
    ring
  let node : ℕ→FlowEnd := Nat.rec 1 (fun i v=>U i v 1)
  have ng (i : ℕ) (hi : i<N) : good i (node i) := by
    induction i with
    | zero => simp [good,node]
    | succ i ih =>
      have prev := follow i (node i) (by omega) (ih (by omega))
      simpa only [good,node,Nat.cast_succ] using prev.2.2 1 (by norm_num [unitCell])
  let J := fun i t=>(c i).M t*U i (node i) t
  refine ⟨J,fun i hi=>?_⟩
  obtain ⟨ini,ode,err⟩ := follow i (node i) hi (ng i hi)
  refine ⟨?_,?_,?_⟩
  · dsimp only [J];rw [ini]
    cases i with
    | zero => simp [node]
    | succ i => simp [node,join i hi]
  · intro t ht
    have u := (c i).unit t ht
    have eq : (c i).M t*Ring.inverse ((c i).M t)=1 := Ring.mul_inverse_cancel _ u
    have d := ((c i).variation_deriv t).hasDerivWithinAt.mul (ode t ht)
    apply d.congr_deriv
    change _=actualCoefficient s (x i) t*((c i).M t*U i (node i) t)
    simp only [H,relativeCoefficient,flowMetricCoefficient]
    rw [←mul_assoc ((c i).M t),←mul_assoc ((c i).M t),eq,one_mul,sub_mul,mul_assoc]
    abel
  · intro t ht
    change ‖(c i).M t*U i (node i) t-(c i).M t‖≤_
    rw [show (c i).M t*U i (node i) t-(c i).M t=(c i).M t*(U i (node i) t-1) by rw [mul_sub,mul_one]]
    exact (norm_mul_le ..).trans ((mul_le_mul ((c i).matrix_norm t ht) (err t ht) (norm_nonneg _) (by norm_num)).trans_eq (by dsimp [δ];ring))
end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.variation_chain
