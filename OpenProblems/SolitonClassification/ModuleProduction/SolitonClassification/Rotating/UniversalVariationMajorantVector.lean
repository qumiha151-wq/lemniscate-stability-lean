module

public import SolitonClassification.Rotating.AnalyticMajorantVectorActual
public import SolitonClassification.Rotating.UniversalVariationMajorantScalar

@[expose] public section

/-! Finite majorization of the derivative-field convolution. The actual
state field's parameter direction and angle row remain present. This file
is generic finite algebra; the companion Actual file identifies the
pre-existing variationCoeff with this recurrence. -/
namespace SolitonClassification.Rotating.UniversalMajorant
noncomputable section
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def mixedBilinearCoeff (a : State) (p w : ℕ → State) (n : ℕ) : State :=
  ∑ ij ∈ Finset.antidiagonal n,bilinear a (p ij.1) (w ij.2)

def mixedTrilinearCoeff (p q w : ℕ → State) (n : ℕ) : State :=
  ∑ ij ∈ Finset.antidiagonal n,∑ jk ∈ Finset.antidiagonal ij.2,
    trilinear (p ij.1) (q jk.1) (w jk.2)

def variationTaylorRHS (a : State) (p w : ℕ → State) (n : ℕ) : State :=
  linear a (w n)+mixedBilinearCoeff a p w n+mixedBilinearCoeff a w p n+
    (3:ℝ) • mixedTrilinearCoeff p p w n

lemma mixedBilinearCoeff_bound {a : State} (ha : a∈innerTube)
    (p w : ℕ → State) (P Q : ℝ[X])
    (hP : ∀ j,0≤P.coeff j) (hQ : ∀ j,0≤Q.coeff j) (n : ℕ)
    (hp : ∀ j≤n,‖p j‖≤P.coeff j) (hw : ∀ j≤n,‖w j‖≤Q.coeff j) :
    ‖mixedBilinearCoeff a p w n‖≤2*(P*Q).coeff n := by
  rw [mixedBilinearCoeff,coeff_mul,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  have hpi := hP ij.1
  have hqj := hQ ij.2
  calc
    _ ≤ 2*‖p ij.1‖*‖w ij.2‖ := bilinear_bound (innerTube_subset_outerTube ha) _ _
    _ ≤ 2*P.coeff ij.1*Q.coeff ij.2 := by
      gcongr
      · exact hp _ (by omega)
      · exact hw _ (by omega)
    _ = _ := by ring

lemma mixedTrilinearCoeff_bound (p q w : ℕ → State) (P Q R : ℝ[X])
    (hP : ∀ j,0≤P.coeff j) (hQ : ∀ j,0≤Q.coeff j) (hR : ∀ j,0≤R.coeff j)
    (n : ℕ) (hp : ∀ j≤n,‖p j‖≤P.coeff j)
    (hq : ∀ j≤n,‖q j‖≤Q.coeff j) (hw : ∀ j≤n,‖w j‖≤R.coeff j) :
    ‖mixedTrilinearCoeff p q w n‖≤(1/16)*(P*(Q*R)).coeff n := by
  rw [mixedTrilinearCoeff,coeff_mul,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ij hij
  have he := Finset.mem_antidiagonal.mp hij
  rw [coeff_mul,Finset.mul_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro jk hjk
  have hj := Finset.mem_antidiagonal.mp hjk
  have hpi := hP ij.1
  have hqj := hQ jk.1
  have hrk := hR jk.2
  calc
    _ ≤ (1/16)*‖p ij.1‖*‖q jk.1‖*‖w jk.2‖ := trilinear_bound _ _ _
    _ ≤ (1/16)*P.coeff ij.1*Q.coeff jk.1*R.coeff jk.2 := by
      gcongr
      · exact hp _ (by omega)
      · exact hq _ (by omega)
      · exact hw _ (by omega)
    _ = _ := by ring

lemma variationTaylorRHS_bound {a : State} (ha : a∈innerTube)
    (M : ℕ) (p w : ℕ → State) (q : ℝ[X]) (hq : ∀ j,0≤q.coeff j) (n : ℕ)
    (hp : ∀ j≤n,‖p j‖≤(displacementPolynomial M).coeff j)
    (hw : ∀ j≤n,‖w j‖≤q.coeff j) :
    ‖variationTaylorRHS a p w n‖≤(jacLipschitzPolynomial M*q).coeff n := by
  let W := displacementPolynomial M
  have hW := displacementPolynomial_nonneg M
  have hlin : ‖linear a (w n)‖≤17*q.coeff n :=
    (linear_bound (innerTube_subset_outerTube ha) _).trans
      (mul_le_mul_of_nonneg_left (hw n le_rfl) (by norm_num))
  have hb1 := mixedBilinearCoeff_bound ha p w W q hW hq n hp hw
  have hb2 := mixedBilinearCoeff_bound ha w p q W hq hW n hw hp
  rw [mul_comm q W] at hb2
  have ht := mixedTrilinearCoeff_bound p p w W W q hW hW hq n hp hp hw
  have he : W*(W*q)=W^2*q := by ring
  rw [he] at ht
  have h3 : ‖(3:ℝ) • mixedTrilinearCoeff p p w n‖≤(3/16)*(W^2*q).coeff n := by
    rw [norm_smul,Real.norm_eq_abs]
    norm_num
    linarith
  have h0 := hq n
  have h1 := coeff_mul_nonneg_all hW hq n
  have h2 : 0≤(W^2*q).coeff n := by
    rw [pow_two]
    exact coeff_mul_nonneg_all (coeff_mul_nonneg_all hW hW) hq n
  have hs1 := norm_add_le (linear a (w n)) (mixedBilinearCoeff a p w n)
  have hs2 := norm_add_le (linear a (w n)+mixedBilinearCoeff a p w n)
    (mixedBilinearCoeff a w p n)
  have hs3 := norm_add_le (linear a (w n)+mixedBilinearCoeff a p w n+
    mixedBilinearCoeff a w p n) ((3:ℝ) • mixedTrilinearCoeff p p w n)
  rw [jacLipschitzPolynomial_displacement]
  simp only [add_mul,mul_assoc,coeff_add,coeff_C_mul]
  change ‖variationTaylorRHS a p w n‖≤
    (366/19)*q.coeff n+(1464/361)*(W*q).coeff n+(1464/6859)*(W^2*q).coeff n
  unfold variationTaylorRHS
  linarith

lemma variationTaylorRHS_congr (a : State) (p q w z : ℕ → State) (n : ℕ)
    (hp : ∀ j≤n,p j=q j) (hw : ∀ j≤n,w j=z j) :
    variationTaylorRHS a p w n=variationTaylorRHS a q z n := by
  have hB : mixedBilinearCoeff a p w n=mixedBilinearCoeff a q z n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    rw [hp ij.1 (by omega),hw ij.2 (by omega)]
  have hB' : mixedBilinearCoeff a w p n=mixedBilinearCoeff a z q n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    rw [hw ij.1 (by omega),hp ij.2 (by omega)]
  have hT : mixedTrilinearCoeff p p w n=mixedTrilinearCoeff q q z n := by
    apply Finset.sum_congr rfl
    intro ij hij
    have h := Finset.mem_antidiagonal.mp hij
    apply Finset.sum_congr rfl
    intro jk hjk
    have h' := Finset.mem_antidiagonal.mp hjk
    rw [hp ij.1 (by omega),hp jk.1 (by omega),hw jk.2 (by omega)]
  simp only [variationTaylorRHS,hw n le_rfl,hB,hB',hT]

/-- Arbitrary initial direction, with its actual norm retained. -/
theorem variationTaylor_majorized {a : State} (ha : a∈innerTube)
    (M N : ℕ) (hNM : N≤M) (v : State) (p w : ℕ → State)
    (hp : ∀ j≤N,‖p j‖≤(displacementPolynomial M).coeff j)
    (hw0 : w 0=v)
    (hrec : ∀ n<N,(n+1:ℝ) • w (n+1)=variationTaylorRHS a p w n) :
    ∀ n≤N,‖w n‖≤‖v‖*(jacPolynomial N).coeff n := by
  let q : ℝ[X] := C ‖v‖*jacPolynomial N
  have hq (j : ℕ) : 0≤q.coeff j := by
    change 0≤(C ‖v‖*jacPolynomial N).coeff j
    rw [coeff_C_mul]
    exact mul_nonneg (norm_nonneg v) (jacPolynomial_nonneg N j)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    cases n with
    | zero => simp [hw0,jacPolynomial_zero]
    | succ n =>
      have hw : ∀ j≤n,‖w j‖≤q.coeff j := by
        intro j hj
        change ‖w j‖≤(C ‖v‖*jacPolynomial N).coeff j
        rw [coeff_C_mul]
        exact ih j (by omega) (by omega)
      have hbound := variationTaylorRHS_bound ha M p w q hq n
        (fun j hj => hp j (by omega)) hw
      have he : jacLipschitzPolynomial M*q=C ‖v‖*(jacLipschitzPolynomial M*jacPolynomial N) := by
        dsimp [q]
        ring
      rw [he,coeff_C_mul,jacForcing_recurrence M N n hNM (by omega)] at hbound
      rw [←hrec n (by omega),norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hbound
      by_contra hnot
      have hpos := mul_pos (by positivity : (0:ℝ)<n+1)
        (sub_pos.mpr (lt_of_not_ge hnot))
      nlinarith

end
end SolitonClassification.Rotating.UniversalMajorant

#print axioms SolitonClassification.Rotating.UniversalMajorant.variationTaylor_majorized
open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (←collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
  logInfo "Universal variation vector audit passed; standard axioms only."

end
