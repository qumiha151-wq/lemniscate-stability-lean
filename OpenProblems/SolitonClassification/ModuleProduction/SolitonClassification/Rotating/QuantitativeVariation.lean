module

public import SolitonClassification.Rotating.FlowVariationalODE
public import SolitonClassification.Rotating.FieldHessian
public import SolitonClassification.Rotating.VariationConstantsWithin

@[expose] public section

/-! Sharp variation of the genuine initial-state derivative. The proof uses
the derived actual first variational ODE, the actual fundamental matrix and
its actual inverse, and variation of constants. No flow Hessian or derivative
variation estimate is assumed. The actual matrix bounds are still explicit
certificate obligations. -/
namespace SolitonClassification.Rotating
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem flowLinearCoefficient_bound (σ : ℝ) (hσ : |σ|≤1)
    {a : State} {t : ℝ} (htube : supportFlow σ hσ t a∈outerTube) :
    ‖flowLinearCoefficient σ hσ a t‖≤17 := by
  rw [flowLinearCoefficient,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul hσ (field_fderiv_bound htube) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 17)

/-- A true uniform initial derivative bound bounds actual trajectory
separation on any convex set of initial data. -/
theorem supportFlow_distance_of_true_derivative_bound (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R K : ℝ} {S : Set State}
    (hreg : FlowTubeNeighborhood σ hσ T c R)
    (hS : Convex ℝ S) (hsub : S⊆Metric.ball c R)
    (hPbound : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow σ hσ t) a‖≤K)
    {a b : State} (ha : a∈S) (hb : b∈S) {t : ℝ} (ht : t∈Icc 0 T) :
    ‖supportFlow σ hσ t b-supportFlow σ hσ t a‖≤K*‖b-a‖ := by
  exact hS.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun x hx => (supportFlow_hasFDerivAt_initial σ hσ hreg (hsub hx) ht).hasFDerivWithinAt)
    (fun x hx => hPbound x hx t ht) ha hb

theorem flowLinearCoefficient_difference_of_true_bound (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} {c : State} {R K : ℝ} {S : Set State}
    (hreg : FlowTubeNeighborhood σ hσ T c R)
    (hS : Convex ℝ S) (hsub : S⊆Metric.ball c R)
    (hPbound : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow σ hσ t) a‖≤K)
    {a b : State} (ha : a∈S) (hb : b∈S) {t : ℝ} (ht : t∈Icc 0 T) :
    ‖flowLinearCoefficient σ hσ b t-flowLinearCoefficient σ hσ a t‖≤4*K*‖b-a‖ := by
  have hd := field_fderiv_difference (hreg b (hsub hb) t ht) (hreg a (hsub ha) t ht)
  have hs := supportFlow_distance_of_true_derivative_bound σ hσ hreg hS hsub hPbound ha hb ht
  have he : flowLinearCoefficient σ hσ b t-flowLinearCoefficient σ hσ a t=
      σ • (fderiv ℝ field (supportFlow σ hσ t b)-fderiv ℝ field (supportFlow σ hσ t a)) := by
    ext u
    simp [flowLinearCoefficient,smul_sub]
  rw [he,norm_smul,Real.norm_eq_abs]
  have hm := mul_le_mul_of_nonneg_right hσ
    (norm_nonneg (fderiv ℝ field (supportFlow σ hσ t b)-fderiv ℝ field (supportFlow σ hσ t a)))
  nlinarith

/-- The actual derivative variation is controlled by 4*K^3*I*t. In the
certificate K and I will be true flow/inverse-flow bounds (4 times the
stored metric budgets), never the numerical matrices themselves. -/
theorem supportFlow_fderiv_sharp_variation (σ : ℝ) (hσ : |σ|≤1)
    {T : ℝ} (hT : 0≤T) {c : State} {R K I : ℝ} {S : Set State}
    (hK : 0≤K) (hI : 0≤I) (hreg : FlowTubeNeighborhood σ hσ T c R)
    (hS : Convex ℝ S) (hsub : S⊆Metric.ball c R)
    (hPbound : ∀a∈S,∀t∈Icc 0 T,‖fderiv ℝ (supportFlow σ hσ t) a‖≤K)
    {a b : State} (ha : a∈S) (hb : b∈S)
    (Q : ℝ → State →L[ℝ] State) (hQc : ContinuousOn Q (Icc 0 T))
    (hPQ : ∀t∈Icc 0 T,(fderiv ℝ (supportFlow σ hσ t) a).comp (Q t)=ContinuousLinearMap.id ℝ State)
    (hQbound : ∀t∈Icc 0 T,‖Q t‖≤I) :
    ∀t∈Icc 0 T,
      ‖fderiv ℝ (supportFlow σ hσ t) b-fderiv ℝ (supportFlow σ hσ t) a‖≤
        4*K^3*I*t*‖b-a‖ := by
  intro t ht
  have ht0 := ht.1
  let P : ℝ → State →L[ℝ] State := fun s => fderiv ℝ (supportFlow σ hσ s) a
  let Pb : ℝ → State →L[ℝ] State := fun s => fderiv ℝ (supportFlow σ hσ s) b
  let A := flowLinearCoefficient σ hσ a
  let Ab := flowLinearCoefficient σ hσ b
  have hPc : ContinuousOn P (Icc 0 T) := supportFlow_fderiv_time_continuousOn σ hσ hreg (hsub ha)
  have hPbc : ContinuousOn Pb (Icc 0 T) := supportFlow_fderiv_time_continuousOn σ hσ hreg (hsub hb)
  have hP : ∀s∈Ico 0 T,HasDerivWithinAt P ((A s).comp (P s)) (Ici s) s :=
    fun s hs => supportFlow_fderiv_hasDerivWithinAt σ hσ hreg (hsub ha) hs
  have hPb : ∀s∈Ico 0 T,HasDerivWithinAt Pb ((Ab s).comp (Pb s)) (Ici s) s :=
    fun s hs => supportFlow_fderiv_hasDerivWithinAt σ hσ hreg (hsub hb) hs
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  let w : ℝ → State := fun s => Pb s u-P s u
  let g : ℝ → State := fun s => (Ab s-A s) (Pb s u)
  have hwc : ContinuousOn w (Icc 0 T) :=
    (hPbc.clm_apply continuousOn_const).sub (hPc.clm_apply continuousOn_const)
  have hgc : ContinuousOn g (Icc 0 T) :=
    ((flowLinearCoefficient_continuous σ hσ b).continuousOn.sub
      (flowLinearCoefficient_continuous σ hσ a).continuousOn).clm_apply
      (hPbc.clm_apply continuousOn_const)
  have hw : ∀s∈Ico 0 T,HasDerivWithinAt w (A s (w s)+g s) (Ici s) s := by
    intro s hs
    have hd := ((hPb s hs).clm_apply (hasDerivWithinAt_const s (Ici s) u)).sub
      ((hP s hs).clm_apply (hasDerivWithinAt_const s (Ici s) u))
    convert! hd using 1
    simp only [w,g,ContinuousLinearMap.comp_apply,sub_apply,map_sub,map_zero,add_zero]
    abel
  have hgBound : ∀s∈Icc 0 T,‖g s‖≤4*K^2*‖b-a‖*‖u‖ := by
    intro s hs
    have hAb := flowLinearCoefficient_difference_of_true_bound σ hσ hreg hS hsub hPbound ha hb hs
    have hPub : ‖Pb s u‖≤K*‖u‖ := ((Pb s).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hPbound b hb s hs) (norm_nonneg u))
    have hm := mul_le_mul hAb hPub (norm_nonneg _) (by positivity : 0≤4*K*‖b-a‖)
    exact ((Ab s-A s).le_opNorm (Pb s u)).trans (by nlinarith)
  have hw0 : w 0=0 := by simp only [w,P,Pb,supportFlow_fderiv_initial,sub_self]
  have hh := variation_of_constants_within_norm_bound (A:=A) (P:=P) (Q:=Q) (g:=g) (v:=w)
    (L:=17) hT hK hI hQc hgc
    (fun s hs => flowLinearCoefficient_bound σ hσ (hreg a (hsub ha) s hs))
    hPc hP hPQ (supportFlow_fderiv_initial σ hσ a) hwc hw
    (hPbound a ha) hQbound hgBound t ht
  rw [hw0,norm_zero,zero_add] at hh
  change ‖w t‖≤(4*K^3*I*t*‖b-a‖)*‖u‖
  convert! hh using 1
  ring

end
end SolitonClassification.Rotating

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`SolitonClassification.Rotating).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Rotating sharp actual variation audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Rotating sharp actual variation audit passed for {count} declarations."

end
