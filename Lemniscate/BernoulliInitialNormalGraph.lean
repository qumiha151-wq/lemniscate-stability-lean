import Lemniscate.BernoulliReferenceNormalGraph
import Lemniscate.NormalizedCurvatureProfileEntry
import Lemniscate.NormalizedCurvatureProfileScaling
import Lemniscate.PeriodicSobolevConjugation

/-! The physical initial normal graph supplied by the normalized signed
curvature-profile error. Heights retain the spectral circle throughout:
the auxiliary height is divided by sqrt(2), without changing its period.

-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ContDiff ComplexConjugate

private theorem initial_positive_pair_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a>0, ∃ b>0, P a b)
    (k : ∀ a, 0<a → ∀ b, 0<b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

private theorem physical_initial_graph_identity
    (L S a : ℝ) (ha : a≠0) (r β t : ℂ) (h : ℝ) :
    (L/S) • (r*((a:ℂ)*β+I*(h:ℂ)*t))=
      (L/(S/a)) • (r*(β+((h/a:ℝ):ℂ)*(I*t))) := by
  by_cases hS : S=0
  · simp only [hS,div_zero,zero_smul,zero_div]
  have haC : (a:ℂ)≠0 := by exact_mod_cast ha
  have hSC : (S:ℂ)≠0 := by exact_mod_cast hS
  simp only [Complex.real_smul,Complex.ofReal_div]
  push_cast
  field_simp [haC,hSC]

set_option maxHeartbeats 1200000 in
/-- Small physical normalized signed-curvature error gives a genuine
smooth parameter change and a real, phase-fixed initial normal height in
the same Sobolev space used by the normal-graph evolution. -/
theorem bernoulli_initial_normal_graph
    (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    [Fact (0<e (2*Real.pi))]
    (q p : C(AddCircle (e (2*Real.pi)),ℂ))
    (hq : HasCircleDeriv (e (2*Real.pi)) q p)
    (hcurvature : ∀ x : ℝ, (planarSignedCurvature bernoulliCurve (e.symm x):ℂ)=
      3*q (x:AddCircle (e (2*Real.pi))))
    (M : ℕ) (S : ℝ) [Fact (0<S)] (hS : S=(M:ℝ)*e (2*Real.pi))
    (ψ : CircleL2 S) (hψ : circleConjugate S ψ=ψ)
    (hpair : inner ℂ ψ (circleContinuousL2 S
      (circleBernoulliBackground S
        (circlePeriodicExtension (e (2*Real.pi)) S M hS q)
        (circlePeriodicExtension (e (2*Real.pi)) S M hS p)).b)≠0) :
    let Q := circlePeriodicExtension (e (2*Real.pi)) S M hS q
    let ℓ : ℝ := S/Real.sqrt 2
    let κ : ℝ → ℝ := fun s => 3*(Q ((Real.sqrt 2*s):AddCircle S)).re
    let β : ℝ → ℂ := fun s => bernoulliCurve (e.symm (Real.sqrt 2*s))
    let ν : ℝ → ℂ := fun s => I*(bernoulliVelocity (e.symm (Real.sqrt 2*s))/
      (‖bernoulliVelocity (e.symm (Real.sqrt 2*s))‖:ℂ))
    ∃ ε>0, ∃ C>0, ∀ P : ℝ, 0<P → ∀ γ : ℝ → ℂ,
      ContDiff ℝ ∞ γ → Function.Periodic γ P → (∀ u, deriv γ u≠0) →
      normalizedCurvatureProfileError ℓ P γ κ<ε →
      let L := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
      0<L ∧ ∃ p₀ R₀ : ℂ, ‖R₀‖=1 ∧ ∃ e₀ : ℝ ≃o ℝ,
        ContDiff ℝ ∞ (e₀ : ℝ → ℝ) ∧ ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ) ∧
        (∀ s, e₀ (s+ℓ)=e₀ s+P) ∧ (∀ u, e₀.symm (u+P)=e₀.symm u+ℓ) ∧
        ∃ h : ℝ → ℝ, ∃ hh : ContDiff ℝ ∞ h, ∃ hp : Function.Periodic h S,
          (∀ s, γ (e₀ s)=p₀+(L/ℓ) • (R₀*(β s+(h (Real.sqrt 2*s):ℂ)*ν s))) ∧
          ∃ H : CircleSobolevSpace S 2,
            circleSobolevConjugation S 2 H=H ∧
            circleSobolevCoordinate S 2 0 H=circleContinuousL2 S
              (periodicCircleFunction S (fun x => (h x:ℂ))
                (fun x => congrArg Complex.ofReal (hp x))
                (Complex.continuous_ofReal.comp hh.continuous)) ∧
            inner ℂ ψ (circleSobolevCoordinate S 2 0 H)=0 ∧
            ‖H‖≤C*Real.sqrt (normalizedCurvatureProfileError ℓ P γ κ) := by
  let a : ℝ := Real.sqrt 2
  have ha : 0<a := Real.sqrt_pos.mpr (by norm_num)
  have ha0 : a≠0 := ha.ne'
  have haC : (a:ℂ)≠0 := by exact_mod_cast ha0
  let Q := circlePeriodicExtension (e (2*Real.pi)) S M hS q
  let Pq := circlePeriodicExtension (e (2*Real.pi)) S M hS p
  let ℓ : ℝ := S/a
  let κ : ℝ → ℝ := fun s => 3*(Q ((a*s):AddCircle S)).re
  let βa : ℝ → ℂ := fun x => (a:ℂ)*bernoulliCurve (e.symm x)
  let ta : ℝ → ℂ := fun x =>
    bernoulliVelocity (e.symm x)/(‖bernoulliVelocity (e.symm x)‖:ℂ)
  let ka : ℝ → ℝ := fun x => (3/a)*bernoulliProfileQ (e.symm x)
  let ksa : ℝ → ℝ := fun x => (3/a)*bernoulliProfileP (e.symm x)
  let ba : C(AddCircle S,ℂ) := (2:ℂ) • (Q*Pq)
  have hroot : a*ℓ=S := by dsimp only [ℓ]; field_simp [ha0] <;> ring
  have hQactual (x : ℝ) : (Q (x:AddCircle S)).re=bernoulliProfileQ (e.symm x) :=
    by simpa only [Q,circle_periodic_extension_coe,Complex.ofReal_re] using
      congrArg Complex.re ((bernoulli_circle_profile_identification e he q p hq hcurvature x).1)
  have hka : (fun x => κ (x/a)/a)=ka := by
    funext x
    have hscale : a*(x/a)=x := by field_simp [ha0] <;> ring
    dsimp only [κ,ka]
    rw [hscale,hQactual]
    ring
  have herror (P : ℝ) (γ : ℝ → ℂ) :
      normalizedCurvatureProfileError S P γ ka=
        normalizedCurvatureProfileError ℓ P γ κ := by
    simpa only [hroot,hka] using
      normalized_curvature_profile_error_scaling a ℓ P ha γ κ
  obtain ⟨_,hβsmooth,hβper,hframe,hbounds,hba,_,hpaira⟩ :=
    bernoulli_reference_normal_graph e he q p hq hcurvature M S hS ψ hpair
  refine initial_positive_pair_transport
    (normalized_curvature_profile_entry S βa ta ka ksa hβsmooth hβper
      (fun x => (hframe x).1) (fun x => (hframe x).2.1)
      (fun x => (hframe x).2.2.1) (fun x => (hframe x).2.2.2.1)
      3 3 (by norm_num) (by norm_num)
      (fun x => (hbounds x).1) (fun x => (hbounds x).2)
      ba hba ψ hψ hpaira) ?_
  intro ε hε C hC hEntry
  refine ⟨ε,hε,C/a,div_pos hC ha,?_⟩
  intro P hP γ hγsmooth hγper hγreg hsmall
  have hsmallAux : normalizedCurvatureProfileError S P γ ka<ε :=
    (herror P γ).symm ▸ hsmall
  obtain ⟨hL,p₀,R₀,hR,eAux,heAux,heAuxInv,hdeck,hdeckInv,
    hAux,hhAux,hpAux,hgraph,Haux,hHreal,hHvalue,hHphase,hHnorm⟩ :=
      hEntry P hP γ hγsmooth hγper hγreg hsmallAux
  let L : ℝ := ∫ u in (0:ℝ)..P, ‖deriv γ u‖
  let e₀ : ℝ ≃o ℝ := (OrderIso.mulLeft₀ a ha).trans eAux
  let h : ℝ → ℝ := fun x => hAux x/a
  have hh : ContDiff ℝ ∞ h := hhAux.div_const a
  have hp : Function.Periodic h S := fun x => congrArg (·/a) (hpAux x)
  let H : CircleSobolevSpace S 2 := ((1/a:ℝ):ℂ) • Haux
  have he₀ (s : ℝ) : e₀ s=eAux (a*s) := rfl
  have he₀inv (u : ℝ) : e₀.symm u=eAux.symm u/a := by
    change a⁻¹*eAux.symm u=eAux.symm u/a
    rw [div_eq_mul_inv,mul_comm]
  have he₀smooth : ContDiff ℝ ∞ (e₀ : ℝ → ℝ) :=
    heAux.comp (contDiff_const.mul contDiff_id)
  have he₀InvSmooth : ContDiff ℝ ∞ (e₀.symm : ℝ → ℝ) := by
    have hf : (e₀.symm : ℝ → ℝ)=(fun u => eAux.symm u/a) := funext he₀inv
    rw [hf]
    exact heAuxInv.div_const a
  refine ⟨hL,p₀,R₀,hR,e₀,he₀smooth,he₀InvSmooth,?_,?_,h,hh,hp,?_,H,?_,?_,?_,?_⟩
  · intro s
    change eAux (a*(s+ℓ))=eAux (a*s)+P
    rw [mul_add,hroot]
    exact hdeck (a*s)
  · intro u
    rw [he₀inv,he₀inv,hdeckInv]
    change (eAux.symm u+S)/a=eAux.symm u/a+S/a
    ring
  · intro s
    rw [he₀,hgraph (a*s)]
    apply congrArg (p₀+·)
    change (L/S) • (R₀*((a:ℂ)*bernoulliCurve (e.symm (a*s))+
        I*(hAux (a*s):ℂ)*ta (a*s)))=
      (L/(S/a)) • (R₀*(bernoulliCurve (e.symm (a*s))+
        ((hAux (a*s)/a:ℝ):ℂ)*(I*ta (a*s))))
    exact physical_initial_graph_identity L S a ha0 R₀ _ _ _
  · have heq : H=(1/a:ℝ) • Haux := by
      simp only [H,RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [heq,map_smul,hHreal]
  · change circleSobolevCoordinate S 2 0 (((1/a:ℝ):ℂ) • Haux)=_
    rw [map_smul,hHvalue]
    rw [← circle_continuous_l2_smul]
    apply congrArg (circleContinuousL2 S)
    apply ContinuousMap.ext
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i x
    change ((1/a:ℝ):ℂ)*(hAux x:ℂ)=((hAux x/a:ℝ):ℂ)
    push_cast
    ring
  · change inner ℂ ψ (circleSobolevCoordinate S 2 0 (((1/a:ℝ):ℂ) • Haux))=0
    rw [map_smul,inner_smul_right,hHphase,mul_zero]
  · have hn : ‖H‖=(1/a)*‖Haux‖ := by
      change ‖((1/a:ℝ):ℂ) • Haux‖=(1/a)*‖Haux‖
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr ha)]
    rw [hn]
    have hnorm := mul_le_mul_of_nonneg_left hHnorm (one_div_pos.mpr ha).le
    rw [herror P γ] at hnorm
    change (1/a)*‖Haux‖≤(C/a)*Real.sqrt (normalizedCurvatureProfileError ℓ P γ κ)
    calc
      _≤(1/a)*(C*Real.sqrt (normalizedCurvatureProfileError ℓ P γ κ)) := hnorm
      _=_ := by ring

end Lemniscate
