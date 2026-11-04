import Lemniscate.PeriodicParabolicLowerOrder
import Lemniscate.PeriodicParabolicPicard
import Lemniscate.PeriodicSobolevPrincipalEstimate

/-! Local solutions of a periodic semilinear equation on the actual
maximal-regularity space.  The principal-plus-lower-order data inverse is
constructed here from the existing linear solver; it is not an input.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal

private theorem unique_subtype_transport {X : Type*} {P S : X → Prop}
    {R : {x : X | P x} → Prop}
    (hRS : ∀ u, R u ↔ S u.1) (hSP : ∀ x, S x → P x)
    (h : ∃! u, R u) : ∃! x, S x := by
  obtain ⟨u,hu,hunique⟩ := h
  refine ⟨u.1,(hRS u).mp hu,?_⟩
  intro x hx
  let v : {x : X | P x} := ⟨x,hSP x hx⟩
  exact congrArg Subtype.val (hunique v ((hRS v).mpr hx))

private theorem parameter_witness_transport {A : Type*} {B : A → Type*}
    {p q : A → Prop} {r : ∀ a, B a → Prop} {s : A → Prop}
    (h : ∃ a, p a ∧ q a ∧ ∃ b, r a b)
    (k : ∀ a, p a → q a → ∀ b, r a b → s a) :
    ∃ a, p a ∧ q a ∧ s a := by
  obtain ⟨a,ha,hq,b,hb⟩ := h
  exact ⟨a,ha,hq,k a ha hq b hb⟩

private theorem radius_witness_transport {P Q : ℝ → ℝ → Prop}
    {δ η : ℝ} (hδη : δ ≤ η)
    (h : ∃ ε > 0, ∃ r > 0, r < δ ∧ P ε r)
    (k : ∀ ε r, r < δ → P ε r → Q ε r) :
    ∃ ε > 0, ∃ r > 0, r < η ∧ Q ε r := by
  obtain ⟨ε,hε,r,hr,hrδ,hP⟩ := h
  exact ⟨ε,hε,r,hr,hrδ.trans_le hδη,k ε r hrδ hP⟩

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
/-- A mixed H2-H4 remainder and a genuine second-order bounded
perturbation give actual local solutions, unique in a parabolic ball
smaller than any prescribed positive radius. -/
theorem circle_parabolic_local_solution
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (D : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T)
    (B : CircleSobolevSpace T 2 →L[ℂ] CircleL2 T)
    (hFzero : F 0 = 0)
    (hBA : ∀ f : CircleSobolevSpace T 4,
      circleSobolevPrincipalOperator T f-
          B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) = -(D f))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (C : ℝ) (hC : 0 ≤ C)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ₀ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ₀ →
      ‖F f-F g-D (f-g)‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖))
    (η : ℝ) (hη : 0 < η) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ u₀ : CircleSobolevSpace T 2, ‖u₀‖ ≤ ε →
        ∃! U : CircleParabolicSpace T τ,
          ‖U‖ ≤ r ∧ circleParabolicInitialValue T τ U = u₀ ∧
            ∀ᵐ t : unitInterval ∂volume,
              circleParabolicTimeDerivative T τ U t = F (circleParabolicH4 T τ U t) := by
  let δ : ℝ := min δ₀ η
  have hδ : 0 < δ := lt_min hδ₀ hη
  have hδold : δ ≤ δ₀ := min_le_left _ _
  let N : CircleSobolevSpace T 4 → CircleL2 T := fun f => F f-D f
  have hNzero : N 0 = 0 := by
    dsimp only [N]
    rw [hFzero,map_zero,sub_zero]
  have hNdiff (f g : CircleSobolevSpace T 4) :
      N f-N g = F f-F g-D (f-g) := by
    dsimp only [N]
    rw [map_sub]
    abel
  have hNtame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖) := by
    intro f g hf hg
    rw [hNdiff]
    exact htame f g (hf.trans_le hδold) (hg.trans_le hδold)
  refine parameter_witness_transport (circle_parabolic_lower_order_isomorphism T B) ?_
  intro τ hτ hτ1 e he
  let A₀ := circleSobolevPrincipalOperator T
  let BT : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
    (B.compLpL 2 (volume : Measure unitInterval)).comp (circleParabolicH2Time T τ)
  let L : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T :=
    (ContinuousLinearMap.snd ℂ (CircleSobolevSpace T 2) (CircleTimeL2 T)).comp
      e.toContinuousLinearMap
  have heapply (U : CircleParabolicSpace T τ) :
      e U = (circleParabolicInitialValue T τ U,circleParabolicPrincipalRHS T τ U-BT U) := by
    have hvalue : e.toContinuousLinearMap U = circleParabolicLowerOrderData T τ B U :=
      congrArg (fun A : CircleParabolicSpace T τ →L[ℂ]
        (CircleSobolevSpace T 2 × CircleTimeL2 T) => A U) he
    simpa only [circleParabolicLowerOrderData] using! hvalue
  have hLapply (U : CircleParabolicSpace T τ) :
      L U = circleParabolicPrincipalRHS T τ U-BT U := congrArg Prod.snd (heapply U)
  let R := circleParabolicNemytskii T τ hδ hC hNzero hNtame
  have hpicard := circle_parabolic_picard T τ hδ hC hNzero hNtame
    L e (fun U => congrArg Prod.fst (heapply U)) (fun _ => rfl)
  have hRrep := (circle_parabolic_nemytskii_tame T τ hδ hC hNzero hNtame).1
  have hLrep (U : CircleParabolicSpace T τ) :
      (L U : unitInterval → CircleL2 T) =ᵐ[volume]
        fun t => circleParabolicTimeDerivative T τ U t-D (circleParabolicH4 T τ U t) := by
    let v := circleParabolicTimeDerivative T τ U
    let w := circleParabolicH4 T τ U
    let z := circleParabolicH2Time T τ U
    have hsub := Lp.coeFn_sub
      (v+(A₀.compLpL 2 (volume : Measure unitInterval)) w)
      ((B.compLpL 2 (volume : Measure unitInterval)) z)
    have hadd := Lp.coeFn_add v ((A₀.compLpL 2 (volume : Measure unitInterval)) w)
    have hA := A₀.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) w
    have hB := B.coeFn_compLpL (p := 2) (μ := (volume : Measure unitInterval)) z
    have hz : (z : unitInterval → CircleSobolevSpace T 2) =ᵐ[volume]
        circleParabolicCurve T τ U :=
      ContinuousMap.coeFn_toLp (p := 2) (volume : Measure unitInterval) (𝕜 := ℂ)
        (circleParabolicCurve T τ U)
    filter_upwards [hsub,hadd,hA,hB,hz,circle_parabolic_h2_h4_ae T τ U]
      with t hst hat hAt hBt hzt hwt
    have hLt := congrArg (fun W : CircleTimeL2 T => W t) (hLapply U)
    change L U t = ((v+(A₀.compLpL 2 (volume : Measure unitInterval)) w)-
      (B.compLpL 2 (volume : Measure unitInterval)) z) t at hLt
    change ((v+(A₀.compLpL 2 (volume : Measure unitInterval)) w)-
      (B.compLpL 2 (volume : Measure unitInterval)) z) t =
      (v+(A₀.compLpL 2 (volume : Measure unitInterval)) w) t-
        ((B.compLpL 2 (volume : Measure unitInterval)) z) t at hst
    change (v+(A₀.compLpL 2 (volume : Measure unitInterval)) w) t =
      v t+((A₀.compLpL 2 (volume : Measure unitInterval)) w) t at hat
    change ((A₀.compLpL 2 (volume : Measure unitInterval)) w) t = A₀ (w t) at hAt
    change ((B.compLpL 2 (volume : Measure unitInterval)) z) t = B (z t) at hBt
    calc
      L U t = ((v+(A₀.compLpL 2 (volume : Measure unitInterval)) w)-
        (B.compLpL 2 (volume : Measure unitInterval)) z) t := hLt
      _ = (v+(A₀.compLpL 2 (volume : Measure unitInterval)) w) t-
        ((B.compLpL 2 (volume : Measure unitInterval)) z) t := hst
      _ = (v t+((A₀.compLpL 2 (volume : Measure unitInterval)) w) t)-B (z t) :=
        congrArg₂ (fun a b : CircleL2 T => a-b) hat hBt
      _ = (v t+A₀ (w t))-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w t))) :=
        congrArg₂ (fun a b : CircleL2 T => a-b)
          (congrArg (fun a : CircleL2 T => v t+a) hAt) (congrArg B (hzt.trans hwt))
      _ = v t+(A₀ (w t)-
        B (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (w t)))) := by abel
      _ = v t+ -(D (w t)) :=
        congrArg (fun a : CircleL2 T => v t+a) (hBA (w t))
      _ = v t-D (w t) := (sub_eq_add_neg (v t) (D (w t))).symm
  have hPDEiff (U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ}) :
      L U.1 = R U ↔
        ∀ᵐ t : unitInterval ∂volume,
          circleParabolicTimeDerivative T τ U.1 t = F (circleParabolicH4 T τ U.1 t) := by
    constructor
    · intro h
      filter_upwards [hLrep U.1,hRrep U] with t hLt hRt
      have ht := congrArg (fun G : CircleTimeL2 T => G t) h
      exact sub_left_inj.mp (hLt.symm.trans (ht.trans hRt))
    · intro h
      apply Lp.ext
      filter_upwards [hLrep U.1,hRrep U,h] with t hLt hRt ht
      exact hLt.trans ((congrArg (fun z : CircleL2 T =>
        z-D (circleParabolicH4 T τ U.1 t)) ht).trans hRt.symm)
  refine radius_witness_transport (min_le_right δ₀ η) hpicard ?_
  intro ε r hrδ hsolve
  intro u₀ hu₀
  exact unique_subtype_transport
    (fun U => and_congr Iff.rfl (and_congr Iff.rfl (hPDEiff U)))
    (fun U hU => (norm_fst_le U.1).trans_lt (hU.1.trans_lt hrδ))
    (hsolve u₀ hu₀)

end Lemniscate
