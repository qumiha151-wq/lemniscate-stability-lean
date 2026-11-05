import Lemniscate.PeriodicParabolicInteriorTime
import Mathlib.Topology.Order.ProjIcc

/-! Positive-time Sobolev regularity of the actual overlapping solution.
The local representatives agree by injectivity of their value coordinate. -/

noncomputable section
namespace Lemniscate
open Filter Set
open scoped Topology NNReal

private theorem continuous_lift_of_local_representatives
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (i : Y → Z) (hi : Function.Injective i) (f : X → Z)
    (h : ∀ x : X, ∃ s ∈ 𝓝 x, ∃ g : X → Y,
      Continuous g ∧ ∀ y ∈ s, i (g y) = f y) :
    ∃ g : C(X,Y), ∀ x, i (g x) = f x := by
  have hex (x : X) : ∃ y : Y, i y = f x := by
    obtain ⟨s,hs,g,_,hg⟩ := h x
    exact ⟨g x,hg x (mem_of_mem_nhds hs)⟩
  choose g hg using hex
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun x => by
    obtain ⟨s,hs,v,hv,heq⟩ := h x
    have he : g =ᶠ[𝓝 x] v := mem_of_superset hs
      (fun y hy => hi ((hg y).trans (heq y hy).symm))
    exact hv.continuousAt.congr he.symm)
  exact ⟨⟨g,hc⟩,hg⟩

variable (T : ℝ) [Fact (0 < T)]

/-- Local Sobolev regularity on the actual overlapping segments gives
one continuous Sobolev representative on the whole positive time axis. -/
theorem circle_parabolic_global_sobolev_lift
    (τ : ℝ) (hτ : 0 < τ) (n : ℕ)
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (U : ℕ → CircleParabolicSpace T τ)
    (hrep : ∀ m r, u (circleParabolicSegmentTime τ hτ m r) =
      circleParabolicCurve T τ (U m) r)
    (hreg : ∀ m : ℕ, ∀ r₀ : ℝ, ∀ hr₀ : 0 < r₀,
      ∃ v : C(Icc r₀ (1:ℝ),CircleSobolevSpace T n), ∀ r : Icc r₀ (1:ℝ),
        circleSobolevCoordinate T n 0 (v r) =
          circleSobolevCoordinate T 2 0 (circleParabolicCurve T τ (U m)
            ⟨(r:ℝ),(hr₀.trans_le r.property.1).le,r.property.2⟩)) :
    ∃ v : C(Ioi (0:ℝ),CircleSobolevSpace T n), ∀ t : Ioi (0:ℝ),
      circleSobolevCoordinate T n 0 (v t) =
        circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩) := by
  apply continuous_lift_of_local_representatives (circleSobolevCoordinate T n 0)
    (circle_sobolev_value_injective T n)
    (fun t : Ioi (0:ℝ) => circleSobolevCoordinate T 2 0 (u ⟨(t:ℝ),t.property.le⟩))
  intro t
  obtain ⟨m,r,hr1,hrlo,htr⟩ := circle_parabolic_interior_time τ hτ (t:ℝ)
    t.property ⟨(t:ℝ),t.property.le⟩ le_rfl
  have hr : 0 < (r:ℝ) := (lt_min (by norm_num : (0:ℝ) < 1/2)
    (div_pos t.property hτ)).trans_le hrlo
  let r₀ : ℝ := (r:ℝ)/2
  have hr₀ : 0 < r₀ := half_pos hr
  have hr₀1 : r₀ ≤ 1 := by dsimp only [r₀]; linarith only [hr1,hr]
  obtain ⟨w,hw⟩ := hreg m r₀ hr₀
  let a : ℝ → ℝ := fun s => s/τ-(m:ℝ)/2
  have ha : Continuous a := (continuous_id.div_const τ).sub continuous_const
  have hat : a (t:ℝ) = (r:ℝ) := by
    have he := congrArg (fun s : ℝ≥0 => (s:ℝ)) htr
    change τ*((m:ℝ)/2+(r:ℝ)) = (t:ℝ) at he
    dsimp only [a]
    rw [← he]
    field_simp [ne_of_gt hτ]
    <;> ring
  let s : Set (Ioi (0:ℝ)) := {y | r₀ < a (y:ℝ) ∧ a (y:ℝ) < 1}
  have hsopen : IsOpen s :=
    (isOpen_lt continuous_const (ha.comp continuous_subtype_val)).inter
      (isOpen_lt (ha.comp continuous_subtype_val) continuous_const)
  have hst : t ∈ s := by
    change r₀ < a (t:ℝ) ∧ a (t:ℝ) < 1
    rw [hat]
    exact ⟨by dsimp only [r₀]; linarith only [hr],hr1⟩
  let g : Ioi (0:ℝ) → CircleSobolevSpace T n :=
    fun y => w (projIcc r₀ 1 hr₀1 (a (y:ℝ)))
  have hg : Continuous g := w.continuous.comp
    ((continuous_projIcc (a := r₀) (b := 1) (h := hr₀1)).comp
      (ha.comp continuous_subtype_val))
  refine ⟨s,hsopen.mem_nhds hst,g,hg,?_⟩
  intro y hy
  have hyr : a (y:ℝ) ∈ Icc r₀ (1:ℝ) := ⟨hy.1.le,hy.2.le⟩
  let z : Icc r₀ (1:ℝ) := ⟨a (y:ℝ),hyr⟩
  let zI : unitInterval := ⟨a (y:ℝ),(hr₀.trans_le hyr.1).le,hyr.2⟩
  have htime : circleParabolicSegmentTime τ hτ m zI =
      (⟨(y:ℝ),y.property.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    change τ*((m:ℝ)/2+(a (y:ℝ))) = (y:ℝ)
    dsimp only [a]
    field_simp [ne_of_gt hτ]
    <;> ring
  change circleSobolevCoordinate T n 0 (w (projIcc r₀ 1 hr₀1 (a (y:ℝ)))) = _
  rw [projIcc_of_mem hr₀1 hyr]
  exact (hw z).trans (congrArg (circleSobolevCoordinate T 2 0)
    ((hrep m zI).symm.trans (congrArg u htime)))

end Lemniscate
