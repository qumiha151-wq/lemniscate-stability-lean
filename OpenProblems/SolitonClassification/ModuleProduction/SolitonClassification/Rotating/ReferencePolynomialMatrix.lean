module

public import SolitonClassification.Rotating.UniversalVariationOperatorTail
public import SolitonClassification.Rotating.ReferenceInversePerturbation

@[expose] public section

/-! Real polynomial reference matrices have certified whole-segment
invertibility. The proof uses closeness of the local polynomial operator
to identity, not an assumed inverse bound for the true variational flow. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set UniversalMajorant
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

theorem variationPolynomialMap_zero (a : State) (N : ℕ) :
    variationPolynomialMap a N 0=1 := by
  ext v
  rw [variationPolynomialMap_apply,polynomialPath_variation_zero]
  rfl

theorem variationPolynomialMap_signed_hasDerivAt (σ : ℝ) (a : State) (N : ℕ) (t : ℝ) :
    HasDerivAt (fun s=>variationPolynomialMap a N (σ*s))
      (σ • variationVelocityMap a N (σ*t)) t := by
  convert! (variationPolynomialMap_hasDerivAt a N (σ*t)).scomp t
    ((hasDerivAt_id t).const_mul σ) using 1
  simp

theorem variationVelocityMap_norm_of_bounds {a : State} {M N : ℕ} {t : ℝ}
    (hp : polynomialPath (taylorPolynomial a M) t∈outerTube)
    (hU : ‖variationPolynomialMap a N t‖≤6/5)
    (hr : ‖mixedVariationResidualMap a M N t‖≤1) :
    ‖variationVelocityMap a N t‖≤107/5 := by
  have he : variationVelocityMap a N t=
      (fderiv ℝ field (polynomialPath (taylorPolynomial a M) t)).comp (variationPolynomialMap a N t)+
        mixedVariationResidualMap a M N t := by
    unfold mixedVariationResidualMap
    abel
  have hcomp : ‖(fderiv ℝ field (polynomialPath (taylorPolynomial a M) t)).comp
      (variationPolynomialMap a N t)‖≤17*(6/5) :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (field_fderiv_bound hp) hU (norm_nonneg _) (by norm_num))
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hcomp hr).trans (by norm_num))

theorem variationVelocityMap30_norm {a : State} (ha : a∈innerTube) {t : ℝ}
    (ht : |t|≤(universalStepCap:ℝ)) : ‖variationVelocityMap a 30 t‖≤107/5 :=
  variationVelocityMap_norm_of_bounds (taylorPolynomial60_tube_uniform ha ht)
    (variationPolynomialMap30_norm ha ht) ((mixedVariationResidualMap60_30_norm ha ht).trans (by norm_num))

theorem variationPolynomialMap_signed_sub_one_le (σ : ℝ) (hσ : |σ|≤1) (a : State) (N : ℕ)
    {T t : ℝ} (ht : t∈Icc 0 T)
    (hv : ∀s∈Icc 0 T,‖variationVelocityMap a N (σ*s)‖≤107/5) :
    ‖variationPolynomialMap a N (σ*t)-1‖≤(107/5)*t := by
  have hT : 0≤T := ht.1.trans ht.2
  have hb (s : ℝ) (hs : s∈Icc 0 T) : ‖σ • variationVelocityMap a N (σ*s)‖≤107/5 := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
      (by simpa using hv s hs)
  have h := (convex_Icc (0:ℝ) T).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _=>(variationPolynomialMap_signed_hasDerivAt σ a N s).hasDerivWithinAt) hb
    (x:=0) (y:=t) ⟨le_rfl,hT⟩ ht
  simpa only [mul_zero,variationPolynomialMap_zero,sub_zero,Real.norm_eq_abs,abs_of_nonneg ht.1] using h

theorem variationPolynomialMap_unit_of_velocity_bound (σ : ℝ) (hσ : |σ|≤1) (a : State) (N : ℕ)
    {T t : ℝ} (hT : T≤(universalStepCap:ℝ)) (ht : t∈Icc 0 T)
    (hv : ∀s∈Icc 0 T,‖variationVelocityMap a N (σ*s)‖≤107/5) :
    IsUnit (variationPolynomialMap a N (σ*t)) ∧
      ‖Ring.inverse (variationPolynomialMap a N (σ*t))‖≤5/4 := by
  apply flowEnd_inverse_bound_one_fifth
  apply (variationPolynomialMap_signed_sub_one_le σ hσ a N ht hv).trans
  calc
    _ ≤ (107/5)*(universalStepCap:ℝ) := mul_le_mul_of_nonneg_left (ht.2.trans hT) (by norm_num)
    _ ≤ 1/5 := by norm_num [universalStepCap]

theorem variationPolynomialMap30_unit (σ : ℝ) (hσ : |σ|≤1) {a : State} (ha : a∈innerTube)
    {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    IsUnit (variationPolynomialMap a 30 (σ*t)) ∧
      ‖Ring.inverse (variationPolynomialMap a 30 (σ*t))‖≤5/4 := by
  apply variationPolynomialMap_unit_of_velocity_bound σ hσ a 30 le_rfl ht
  intro s hs
  apply variationVelocityMap30_norm ha
  rw [abs_mul,abs_of_nonneg hs.1]
  exact (mul_le_mul_of_nonneg_right hσ hs.1).trans (by simpa using hs.2)

def referencePolynomialMatrix (σ : ℝ) (a : State) (N : ℕ) (B : State →L[ℝ] State) (t : ℝ) :
    State →L[ℝ] State := (variationPolynomialMap a N (σ*t)).comp B

theorem referencePolynomialMatrix_hasDerivAt (σ : ℝ) (a : State) (N : ℕ)
    (B : State →L[ℝ] State) (t : ℝ) :
    HasDerivAt (referencePolynomialMatrix σ a N B)
      ((σ • variationVelocityMap a N (σ*t)).comp B) t := by
  have h := (variationPolynomialMap_signed_hasDerivAt σ a N t).clm_comp (hasDerivAt_const t B)
  convert! h using 1
  simp

theorem referencePolynomialMatrix_residual_derivative (σ : ℝ) (a : State) (M N : ℕ)
    (B : State →L[ℝ] State) (t : ℝ) :
    HasDerivAt (referencePolynomialMatrix σ a N B)
      ((σ • fderiv ℝ field (polynomialPath (taylorPolynomial a M) (σ*t))).comp
        (referencePolynomialMatrix σ a N B t)+
          σ • ((mixedVariationResidualMap a M N (σ*t)).comp B)) t := by
  convert! referencePolynomialMatrix_hasDerivAt σ a N B t using 1
  ext v i
  simp [referencePolynomialMatrix,mixedVariationResidualMap,ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  ring

theorem referencePolynomialMatrix30_residual_norm (σ : ℝ) (hσ : |σ|≤1)
    {a : State} (ha : a∈innerTube) (B : State →L[ℝ] State) {t : ℝ}
    (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    ‖σ • ((mixedVariationResidualMap a 60 30 (σ*t)).comp B)‖≤(4/10^27)*‖B‖ := by
  have hs : |σ*t|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hσ ht.1).trans (by simpa using ht.2)
  rw [norm_smul,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_right hσ (norm_nonneg _)).trans
  simpa only [one_mul] using mixedVariationResidualMap60_30_comp_norm ha hs B

theorem referencePolynomialMatrix30_bounds (σ : ℝ) (hσ : |σ|≤1) {a : State} (ha : a∈innerTube)
    (B : State →L[ℝ] State) (hB : IsUnit B) {t : ℝ} (ht : t∈Icc 0 (universalStepCap:ℝ)) :
    IsUnit (referencePolynomialMatrix σ a 30 B t) ∧
      ‖referencePolynomialMatrix σ a 30 B t‖≤(6/5)*‖B‖ ∧
      ‖Ring.inverse (referencePolynomialMatrix σ a 30 B t)‖≤(5/4)*‖Ring.inverse B‖ := by
  have hu:=variationPolynomialMap30_unit σ hσ ha ht
  have hs : |σ*t|≤(universalStepCap:ℝ) := by
    rw [abs_mul,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hσ ht.1).trans (by simpa using ht.2)
  change IsUnit (variationPolynomialMap a 30 (σ*t)*B) ∧ _
  refine ⟨hu.1.mul hB,?_,?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (variationPolynomialMap30_norm ha hs) (norm_nonneg B))
  · change ‖Ring.inverse (variationPolynomialMap a 30 (σ*t)*B)‖≤_
    rw [Ring.inverse_mul (Or.inl hu.1)]
    exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hu.2 (norm_nonneg _)).trans_eq (mul_comm _ _))

end
end SolitonClassification.Rotating

#print axioms SolitonClassification.Rotating.referencePolynomialMatrix30_bounds
open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for a in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains a do
          throwError "Axiom audit failed: {name} depends on {a}"
      count := count+1
  logInfo m!"Polynomial reference-matrix whole-segment inverse audit passed for {count} declarations."

end
