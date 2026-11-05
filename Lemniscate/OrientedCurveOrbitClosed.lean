import Lemniscate.ArclengthOrbitCharacterization
import Lemniscate.ParametricArclengthContinuity
import Lemniscate.PeriodicImmersionArclength
import Mathlib.Topology.Maps.Proper.Basic

/-! Closedness of oriented equivalence uses the compact phase of the
actual fractional arclength parametrizations. No bounds for higher
derivatives of the changing parametrizations are required. -/
noncomputable section
namespace Lemniscate
open Complex Set MeasureTheory
open scoped ContDiff

private theorem curve_arclength_coordinates
    (P : ℝ) (hP : 0<P) (γ : ℝ → ℂ)
    (hγ : ContDiff ℝ ∞ γ) (hper : Function.Periodic γ P)
    (hreg : ∀ s, deriv γ s≠0) :
    ∃ A : ℝ ≃o ℝ,
      (∀ u, A u=∫ s in (0:ℝ)..u, ‖deriv γ s‖) ∧
      ContDiff ℝ ∞ (A : ℝ → ℝ) ∧
      ContDiff ℝ ∞ (A.symm : ℝ → ℝ) ∧
      (∀ s, HasDerivAt (A : ℝ → ℝ) ‖deriv γ s‖ s) ∧
      (∀ q, HasDerivAt (A.symm : ℝ → ℝ) (‖deriv γ (A.symm q)‖)⁻¹ q) ∧
      0<(∫ s in (0:ℝ)..P, ‖deriv γ s‖) ∧
      (∀ s, A (s+P)=A s+(∫ u in (0:ℝ)..P, ‖deriv γ u‖)) := by
  obtain ⟨A,hI,hA,hAi,hD,hDi,hGeom⟩ :=
    periodic_immersion_arclength P hP γ hγ hper hreg
  exact ⟨A,hI,hA,hAi,hD,hDi,hGeom.1,hGeom.2.1⟩

/-- For jointly continuous families of smooth regular closed curves with
jointly continuous spatial velocities, equality up to smooth oriented
reparametrization is a closed condition on the parameter. -/
theorem isClosed_oriented_curve_equivalent
    {X : Type*} [TopologicalSpace X]
    (P Q : ℝ) (hP : 0<P) (hQ : 0<Q)
    (γ η : X × ℝ → ℂ) (hγ : Continuous γ) (hη : Continuous η)
    (hγv : Continuous (fun z : X × ℝ => deriv (fun s => γ (z.1,s)) z.2))
    (hηv : Continuous (fun z : X × ℝ => deriv (fun s => η (z.1,s)) z.2))
    (hγsmooth : ∀ x, ContDiff ℝ ∞ (fun s => γ (x,s)))
    (hηsmooth : ∀ x, ContDiff ℝ ∞ (fun s => η (x,s)))
    (hγreg : ∀ x s, deriv (fun u => γ (x,u)) s≠0)
    (hηreg : ∀ x s, deriv (fun u => η (x,u)) s≠0)
    (hγper : ∀ x, Function.Periodic (fun s => γ (x,s)) P)
    (hηper : ∀ x, Function.Periodic (fun s => η (x,s)) Q) :
    IsClosed {x : X | OrientedCurveEquivalent
      (fun s => γ (x,s)) (fun s => η (x,s)) P Q} := by
  choose A hA using fun x => curve_arclength_coordinates P hP
    (fun s => γ (x,s)) (hγsmooth x) (hγper x) (hγreg x)
  choose B hB using fun x => curve_arclength_coordinates Q hQ
    (fun s => η (x,s)) (hηsmooth x) (hηper x) (hηreg x)
  let L : X → ℝ := fun x => ∫ s in (0:ℝ)..P, ‖deriv (fun u => γ (x,u)) s‖
  let M : X → ℝ := fun x => ∫ s in (0:ℝ)..Q, ‖deriv (fun u => η (x,u)) s‖
  have hAc := parametric_arclength_continuity
    (fun z : X × ℝ => deriv (fun s => γ (z.1,s)) z.2) hγv A (fun x => (hA x).1)
  have hBc := parametric_arclength_continuity
    (fun z : X × ℝ => deriv (fun s => η (z.1,s)) z.2) hηv B (fun x => (hB x).1)
  have hL : Continuous L := by
    have hc := hAc.1.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => P)))
    simpa only [L,(hA _).1,Function.comp_def,id_eq] using hc
  have hM : Continuous M := by
    have hc := hBc.1.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : X => Q)))
    simpa only [M,(hB _).1,Function.comp_def,id_eq] using hc
  let G : X × ℝ → ℂ := fun z => γ (z.1,(A z.1).symm (L z.1*z.2))
  let H : X × ℝ → ℂ := fun z => η (z.1,(B z.1).symm (M z.1*z.2))
  have hG : Continuous G :=
    hγ.comp (continuous_fst.prodMk (hAc.2.comp
      (continuous_fst.prodMk ((hL.comp continuous_fst).mul continuous_snd))))
  have hH : Continuous H :=
    hη.comp (continuous_fst.prodMk (hBc.2.comp
      (continuous_fst.prodMk ((hM.comp continuous_fst).mul continuous_snd))))
  have hiff (x : X) :
      OrientedCurveEquivalent (fun s => γ (x,s)) (fun s => η (x,s)) P Q ↔
        ∃ c ∈ Icc (0:ℝ) 1, ∀ q : ℝ, G (x,q+c)=H (x,q) := by
    rcases hA x with ⟨_,hAs,hAis,hAd,hAid,hLp,hAdeck⟩
    rcases hB x with ⟨_,hBs,hBis,hBd,hBid,hMp,hBdeck⟩
    exact oriented_curve_equivalent_iff_arclength_phase
      (fun s => γ (x,s)) (fun s => η (x,s)) P Q
      (hγsmooth x) (hηsmooth x) (hγreg x) (hηreg x) (hγper x)
      (A x) (B x) hAs hAis hBs hBis hAd hBd hAid hBid
      (L x) (M x) hLp hMp hAdeck hBdeck
  let S : Set (X × Icc (0:ℝ) 1) :=
    {z | ∀ q : ℝ, G (z.1,q+(z.2:ℝ))=H (z.1,q)}
  have hS : IsClosed S := by
    change IsClosed {z : X × Icc (0:ℝ) 1 |
      ∀ q : ℝ, G (z.1,q+(z.2:ℝ))=H (z.1,q)}
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro q
    apply isClosed_eq
    · exact hG.comp (continuous_fst.prodMk
        (continuous_const.add (continuous_subtype_val.comp continuous_snd)))
    · exact hH.comp (continuous_fst.prodMk continuous_const)
  have hImage : IsClosed (Prod.fst '' S) := isClosedMap_fst_of_compactSpace S hS
  have hEq : Prod.fst '' S = {x : X | OrientedCurveEquivalent
      (fun s => γ (x,s)) (fun s => η (x,s)) P Q} := by
    ext x
    constructor
    · rintro ⟨⟨y,c⟩,hc,hx⟩
      change y=x at hx
      subst y
      exact (hiff x).mpr ⟨c,c.property,hc⟩
    · intro hx
      obtain ⟨c,hc,hphase⟩ := (hiff x).mp hx
      exact ⟨(x,⟨c,hc⟩),hphase,rfl⟩
  exact hEq ▸ hImage

end Lemniscate
