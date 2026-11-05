import Lemniscate.PeriodicImmersionArclength
import Lemniscate.PeriodicCurveDilation
import Lemniscate.PeriodicCurvaturePhaseMinimum
import Lemniscate.PeriodicCurvatureProfileEntry
import Lemniscate.PeriodicParameterChange
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! The intrinsic normalized signed-curvature error of a periodic
immersion gives a phase-fixed normal graph in the prescribed circle.
Arclength, positive dilation, the minimizing phase and the genuine smooth
parameter change are all constructed from the immersion.

-/
noncomputable section
namespace Lemniscate
open Complex Set MeasureTheory
open scoped Topology ContDiff ComplexConjugate

/-- Signed curvature after arclength parametrization and positive dilation
to length S. On immersions, the inverse is the genuine arclength inverse. -/
def normalizedImmersionCurvature (S P : ℝ) (γ : ℝ → ℂ) (x : ℝ) : ℝ :=
  let L := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
  let arc : ℝ → ℝ := fun u => ∫ v in (0:ℝ)..u, ‖deriv γ v‖
  planarSignedCurvature γ (Function.invFun arc ((L/S)*x))*(L/S)

/-- The scale-invariant squared signed-curvature profile error, minimized
over the phase of the fixed reference curvature. -/
def normalizedCurvatureProfileError (S P : ℝ) (γ : ℝ → ℂ) (k : ℝ → ℝ) : ℝ :=
  S*sInf (Set.range (fun σ : ℝ =>
    ∫ x in (0:ℝ)..S, (normalizedImmersionCurvature S P γ x-k (x+σ))^2))

private theorem periodic_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (S : ℝ) (hf : Function.Periodic f S) :
    Function.Periodic (deriv f) S := by
  intro x
  have heq : (fun u => f (u+S)) = f := funext hf
  simpa only [deriv_comp_add_const] using congrArg (fun F => deriv F x) heq

private theorem reference_curvature_periodic
    (β t : ℝ → ℂ) (k : ℝ → ℝ) (S : ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t (I*(k s:ℂ)*t s) s)
    (hu : ∀ s, ‖t s‖ = 1) (hβper : Function.Periodic β S) :
    Function.Periodic k S := by
  have hdt : deriv β = t := funext (fun s => (hβ s).deriv)
  have htp : Function.Periodic t S := by
    rw [← hdt]
    exact periodic_derivative β S hβper
  have htdp := periodic_derivative t S htp
  intro s
  have heq : I*(k (s+S):ℂ)*t s = I*(k s:ℂ)*t s := by
    simpa only [(ht (s+S)).deriv,(ht s).deriv,htp s] using htdp s
  have htne : t s ≠ 0 := by
    intro hz
    have hn := hu s
    rw [hz,norm_zero] at hn
    norm_num at hn
  exact Complex.ofReal_injective
    (mul_left_cancel₀ Complex.I_ne_zero (mul_right_cancel₀ htne heq))

private theorem positive_pair_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, P a b)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

set_option maxHeartbeats 1200000 in
/-- A smooth periodic immersion with small intrinsic normalized curvature
error has a real phase-fixed normal height on the prescribed circle. The
original curve is represented using a genuine smooth orientation-preserving
parameter change with the original parameter period. -/
theorem normalized_curvature_profile_entry
    (S : ℝ) [Fact (0<S)] (β t : ℝ → ℂ) (k ks : ℝ → ℝ)
    (hβsmooth : ContDiff ℝ ∞ β) (hβper : Function.Periodic β S)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t (I*(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s) (hu : ∀ s, ‖t s‖=1)
    (K K₁ : ℝ) (hK : 0≤K) (hK₁ : 0≤K₁)
    (hcurvature : ∀ s, |k s|≤K) (hcurvatureDerivative : ∀ s, |ks s|≤K₁)
    (b : C(AddCircle S,ℂ))
    (hb : ∀ s : ℝ, b (s:AddCircle S)=((conj (t s)*β s).re:ℂ))
    (ψ : CircleL2 S) (hψ : circleConjugate S ψ=ψ)
    (hpair : inner ℂ ψ (circleContinuousL2 S b)≠0) :
    ∃ ε > 0, ∃ C > 0, ∀ P : ℝ, 0 < P → ∀ γ : ℝ → ℂ,
      ContDiff ℝ ∞ γ → Function.Periodic γ P → (∀ u, deriv γ u ≠ 0) →
      normalizedCurvatureProfileError S P γ k < ε →
      let L := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
      0 < L ∧ ∃ p₀ r : ℂ, ‖r‖ = 1 ∧ ∃ e₀ : ℝ ≃o ℝ,
        ContDiff ℝ ∞ (e₀ : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ) ∧
        (∀ x, e₀ (x+S) = e₀ x+P) ∧ (∀ u, e₀.symm (u+P) = e₀.symm u+S) ∧
        ∃ h : ℝ → ℝ, ∃ hh : ContDiff ℝ ∞ h, ∃ hp : Function.Periodic h S,
          (∀ x, γ (e₀ x) = p₀+(L/S) • (r*(β x+I*(h x:ℂ)*t x))) ∧
          ∃ H : CircleSobolevSpace S 2,
            circleSobolevConjugation S 2 H = H ∧
            circleSobolevCoordinate S 2 0 H = circleContinuousL2 S
              (periodicCircleFunction S (fun x => (h x:ℂ))
                (fun x => congrArg Complex.ofReal (hp x))
                (Complex.continuous_ofReal.comp hh.continuous)) ∧
            inner ℂ ψ (circleSobolevCoordinate S 2 0 H) = 0 ∧
            ‖H‖ ≤ C*Real.sqrt (normalizedCurvatureProfileError S P γ k) := by
  have hS : 0 < S := Fact.out
  refine positive_pair_transport (periodic_curvature_profile_entry S β t k ks
    hβsmooth hβper hβ ht hk hu K K₁ hK hK₁ hcurvature hcurvatureDerivative
    b hb ψ hψ hpair) ?_
  intro ε hε C hC hEntry
  refine ⟨ε,hε,C,hC,?_⟩
  intro P hP γ hγsmooth hγper hγreg hsmall
  obtain ⟨eArc,hArc,hArcSmooth,hArcInvSmooth,hArcDer,hArcInvDer,hArcData⟩ :=
    periodic_immersion_arclength P hP γ hγsmooth hγper hγreg
  let L : ℝ := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
  let Γ : ℝ → ℂ := γ ∘ eArc.symm
  let Tγ : ℝ → ℂ := fun s => deriv γ (eArc.symm s)/(‖deriv γ (eArc.symm s)‖:ℂ)
  let κ : ℝ → ℝ := fun s => planarSignedCurvature γ (eArc.symm s)
  change 0<L ∧ (∀ u, eArc (u+P)=eArc u+L) ∧
    ContDiff ℝ ∞ Γ ∧ Function.Periodic Γ L ∧
    ContDiff ℝ ∞ Tγ ∧ Function.Periodic Tγ L ∧
    ContDiff ℝ ∞ κ ∧ Function.Periodic κ L ∧ _ at hArcData
  obtain ⟨hL,hArcDeck,hΓsmooth,hΓper,hTγsmooth,hTγper,hκsmooth,hκper,hframe⟩ := hArcData
  let a : ℝ := S/L
  have ha : 0<a := div_pos hS hL
  have haL : a*L=S := by dsimp only [a]; field_simp [hL.ne']
  have hinva : a⁻¹=L/S := by dsimp only [a]; field_simp [hL.ne',hS.ne']
  let Γn : ℝ → ℂ := fun x => (a:ℂ)*Γ (x/a)
  let Tn : ℝ → ℂ := fun x => Tγ (x/a)
  let κn : ℝ → ℝ := fun x => κ (x/a)/a
  have hDilation := periodic_curve_dilation a L ha hL
    (fun _ : Fin 2 => Γ) (fun _ : Fin 2 => Tγ) (fun _ : Fin 2 => κ)
    (fun _ => hΓsmooth) (fun _ => hTγsmooth) (fun _ => hκsmooth)
    (fun _ => hΓper) (fun _ => hTγper) (fun _ => hκper)
    (fun _ s => (hframe s).1) (fun _ s => (hframe s).2.2.1)
    (fun _ s => (hframe s).2.1)
  have hNData : ContDiff ℝ ∞ Γn ∧ Function.Periodic Γn S ∧
      ContDiff ℝ ∞ Tn ∧ Function.Periodic Tn S ∧
      ContDiff ℝ ∞ κn ∧ Function.Periodic κn S ∧
      ∀ x, HasDerivAt Γn (Tn x) x ∧ ‖Tn x‖=1 ∧
        HasDerivAt Tn (I*(κn x:ℂ)*Tn x) x ∧ planarSignedCurvature Γn x=κn x := by
    simpa only [haL] using (hDilation.2.1 (0 : Fin 2))
  obtain ⟨hΓnSmooth,hΓnPer,hTnSmooth,hTnPer,hκnSmooth,hκnPer,hNframe⟩ := hNData
  let arc : ℝ → ℝ := fun u => ∫ v in (0:ℝ)..u, ‖deriv γ v‖
  have hArcFun : arc = (eArc : ℝ → ℝ) := funext (fun u => (hArc u).symm)
  have hInv : Function.invFun arc = (eArc.symm : ℝ → ℝ) := by
    rw [hArcFun]
    exact Function.invFun_eq_of_injective_of_rightInverse eArc.injective eArc.apply_symm_apply
  have hNormalized : normalizedImmersionCurvature S P γ = κn := by
    funext x
    change planarSignedCurvature γ (Function.invFun arc ((L/S)*x))*(L/S) = κ (x/a)/a
    rw [hInv]
    have harg : (L/S)*x=x/a := by
      dsimp only [a]
      field_simp [hL.ne',hS.ne'] <;> ring
    rw [harg]
    change κ (x/a)*(L/S)=κ (x/a)/a
    calc
      _ = κ (x/a)*a⁻¹ := congrArg (fun z : ℝ => κ (x/a)*z) hinva.symm
      _ = _ := (div_eq_mul_inv _ _).symm
  have hkcont : Continuous k := continuous_iff_continuousAt.mpr (fun s => (hk s).continuousAt)
  have hkper := reference_curvature_periodic β t k S hβ ht hu hβper
  obtain ⟨σ,hσ,hmin,hphaseShift⟩ :=
    periodic_curvature_phase_minimum S hS κn k hκnSmooth.continuous hkcont hκnPer hkper
  let J : ℝ → ℝ := fun θ => ∫ x in (0:ℝ)..S, (κn x-k (x+θ))^2
  have hleast : IsLeast (Set.range J) (J σ) := by
    refine ⟨⟨σ,rfl⟩,?_⟩
    rintro y ⟨θ,rfl⟩
    exact hmin θ
  have hError : normalizedCurvatureProfileError S P γ k = S*J σ := by
    unfold normalizedCurvatureProfileError
    rw [hNormalized]
    exact congrArg (fun z : ℝ => S*z) hleast.csInf_eq
  let Γs : ℝ → ℂ := fun x => Γn (x-σ)
  let Ts : ℝ → ℂ := fun x => Tn (x-σ)
  let κs : ℝ → ℝ := fun x => κn (x-σ)
  have hΓsSmooth : ContDiff ℝ ∞ Γs := hΓnSmooth.comp (contDiff_id.sub contDiff_const)
  have hΓsPer : Function.Periodic Γs S := by
    intro x
    change Γn ((x+S)-σ)=Γn (x-σ)
    rw [add_sub_right_comm,hΓnPer]
  have hκsPer : Function.Periodic κs S := by
    intro x
    change κn ((x+S)-σ)=κn (x-σ)
    rw [add_sub_right_comm,hκnPer]
  have hΓs (x : ℝ) : HasDerivAt Γs (Ts x) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using!
      ((hNframe (x-σ)).1).scomp x ((hasDerivAt_id x).sub_const σ)
  have hTs (x : ℝ) : HasDerivAt Ts (I*(κs x:ℂ)*Ts x) x := by
    simpa only [Function.comp_def,id_eq,one_smul] using!
      ((hNframe (x-σ)).2.2.1).scomp x ((hasDerivAt_id x).sub_const σ)
  have hκsCont : Continuous κs := hκnSmooth.continuous.comp (continuous_id.sub continuous_const)
  have hErrorShift : (S*(∫ x in (0:ℝ)..S, (κs x-k x)^2)) =
      normalizedCurvatureProfileError S P γ k :=
    (congrArg (fun z : ℝ => S*z) hphaseShift).symm.trans hError.symm
  obtain ⟨pAux,r,hr,χ,h,hh,hp,hχ,hχper,hgraph,H,hHreal,hHvalue,hHphase,hHbound⟩ :=
    hEntry Γs Ts κs hΓsSmooth hΓsPer hΓs hTs
      (fun x => (hNframe (x-σ)).2.1) hκsCont hκsPer (hErrorShift.trans_lt hsmall)
  have hχDeck (x : ℝ) : χ (x+S)=χ x+S := by
    have hh := hχper x
    change χ (x+S)-(x+S)=χ x-x at hh
    linarith only [hh]
  have hχpositive (x : ℝ) : 0<deriv χ x :=
    (by norm_num : (0:ℝ)<1/4).trans_le (hgraph x).2.2.1
  have hχshift (x : ℝ) : |χ x-x| ≤ C*Real.sqrt (normalizedCurvatureProfileError S P γ k) :=
    ((hgraph x).2.1).trans_eq (congrArg (fun z : ℝ => C*Real.sqrt z) hErrorShift)
  obtain ⟨eχ,heχ,hEχSmooth,hEχInvSmooth,hEχDeck,hEχInvDeck⟩ :=
    periodic_parameter_change S hS χ (C*Real.sqrt (normalizedCurvatureProfileError S P γ k))
      hχ hχDeck hχpositive hχshift
  let e₀ : ℝ ≃o ℝ := eχ.trans
    ((OrderIso.addRight (-σ)).trans ((OrderIso.divRight₀ a ha).trans eArc.symm))
  have he₀ (x : ℝ) : e₀ x = eArc.symm ((χ x-σ)/a) := by
    change eArc.symm ((eχ x+(-σ))/a)=eArc.symm ((χ x-σ)/a)
    rw [heχ,sub_eq_add_neg]
  have he₀Inv (u : ℝ) : e₀.symm u=eχ.symm (eArc u*a+σ) := by
    change eχ.symm ((eArc u*a)-(-σ))=eχ.symm (eArc u*a+σ)
    rw [sub_neg_eq_add]
  have he₀Smooth : ContDiff ℝ ∞ (e₀ : ℝ → ℝ) := by
    rw [show (e₀ : ℝ → ℝ)=(fun x => eArc.symm ((χ x-σ)/a)) from funext he₀]
    exact hArcInvSmooth.comp ((hχ.sub contDiff_const).div_const a)
  have he₀InvSmooth : ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ) := by
    rw [show (e₀.symm : ℝ → ℝ)=(fun u => eχ.symm (eArc u*a+σ)) from funext he₀Inv]
    exact hEχInvSmooth.comp ((hArcSmooth.mul contDiff_const).add contDiff_const)
  have hArcInvDeck (s : ℝ) : eArc.symm (s+L)=eArc.symm s+P := by
    apply eArc.injective
    rw [eArc.apply_symm_apply,hArcDeck,eArc.apply_symm_apply]
  have he₀Deck (x : ℝ) : e₀ (x+S)=e₀ x+P := by
    rw [he₀,he₀,hχDeck]
    have harg : (χ x+S-σ)/a=(χ x-σ)/a+L := by
      calc
        _ = ((χ x-σ)+a*L)/a := congrArg (fun z : ℝ => z/a) (by rw [haL]; ring)
        _ = _ := by field_simp [ha.ne'] <;> ring
    rw [harg,hArcInvDeck]
  have he₀InvDeck (u : ℝ) : e₀.symm (u+P)=e₀.symm u+S := by
    apply e₀.injective
    rw [e₀.apply_symm_apply,he₀Deck,e₀.apply_symm_apply]
  let p₀ : ℂ := (a:ℂ)⁻¹*pAux
  have haC : (a:ℂ)≠0 := by exact_mod_cast ha.ne'
  have hinvC : (a:ℂ)⁻¹=((L/S:ℝ):ℂ) := by exact_mod_cast hinva
  refine ⟨hL,p₀,r,hr,e₀,he₀Smooth,he₀InvSmooth,he₀Deck,he₀InvDeck,
    h,hh,hp,?_,H,hHreal,hHvalue,hHphase,?_⟩
  · intro x
    have hscaled : (a:ℂ)*γ (e₀ x)=pAux+r*(β x+I*(h x:ℂ)*t x) := by
      rw [he₀]
      exact (hgraph x).1
    calc
      γ (e₀ x) = (a:ℂ)⁻¹*((a:ℂ)*γ (e₀ x)) := by
        simp only [← mul_assoc,inv_mul_cancel₀ haC,one_mul]
      _ = (a:ℂ)⁻¹*(pAux+r*(β x+I*(h x:ℂ)*t x)) :=
        congrArg (fun z : ℂ => (a:ℂ)⁻¹*z) hscaled
      _ = p₀+(L/S) • (r*(β x+I*(h x:ℂ)*t x)) := by
        dsimp only [p₀]
        rw [mul_add,hinvC,real_smul]
  · exact hHbound.trans_eq (congrArg (fun z : ℝ => C*Real.sqrt z) hErrorShift)

end Lemniscate
