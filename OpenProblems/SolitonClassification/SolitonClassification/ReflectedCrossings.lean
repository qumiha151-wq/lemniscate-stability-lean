import SolitonClassification.ReflectedArc
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen

/-! Crossings of a reflected physical quarter in the frame whose horizontal
axis is tangent to the quarter endpoint. The reflection axis is vertical. -/
noncomputable section
namespace ClosedSimilarity.ReflectedCrossings
open ReflectedArc Set Filter
open scoped Topology

private theorem state_unique {f g : ℝ → State}
    (hf : ∀ t, HasDerivAt f (field (f t)) t)
    (hg : ∀ t, HasDerivAt g (field (g t)) t) {a : ℝ} (ha : f a = g a) : f=g := by
  have cf := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cg := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  let E := {x | f x = g x}
  have closed : IsClosed E := isClosed_eq cf cg
  have hopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have eqx : f x = g x := hx
    obtain ⟨K,V,hV,hK⟩ := ((field_smooth 1).contDiffAt (x := f x)).exists_lipschitzOnWith
    have hfv : ∀ᶠ t in 𝓝 x, f t ∈ V := cf.continuousAt hV
    have hgv : ∀ᶠ t in 𝓝 x, g t ∈ V := cg.continuousAt (eqx ▸ hV)
    exact ODE_solution_unique_of_eventually (v := fun _ => field) (s := fun _ => V)
      (Eventually.of_forall fun _ => hK) (hfv.mono fun t ht => ⟨hf t,ht⟩)
      (hgv.mono fun t ht => ⟨hg t,ht⟩) eqx
  have allE := (show IsClopen E from ⟨closed,hopen⟩).eq_univ ⟨a,ha⟩
  exact funext fun x => (show x∈E from allE.symm ▸ mem_univ x)

def angle (z : ℝ → State) (S t : ℝ) : ℝ := z t 4 - z S 4
def x (z : ℝ → State) (S t : ℝ) : ℝ :=
  z t 3 * Real.cos (angle z S t) - z t 2 * Real.sin (angle z S t)
def y (z : ℝ → State) (S t : ℝ) : ℝ :=
  z t 3 * Real.sin (angle z S t) + z t 2 * Real.cos (angle z S t)

theorem position_derivatives {z : ℝ → State} (S t : ℝ)
    (hz : ∀ r, HasDerivAt z (field (z r)) r) :
    HasDerivAt (x z S) (Real.cos (angle z S t)) t ∧
      HasDerivAt (y z S) (Real.sin (angle z S t)) t := by
  let c (i : Fin 5) (r : ℝ) := z r i
  have d (i : Fin 5) : HasDerivAt (c i) (field (z t) i) t := hasDerivAt_pi.mp (hz t) i
  have dp : HasDerivAt (c 2) (-c 0 t*c 3 t) t := d 2
  have dq : HasDerivAt (c 3) (1+c 0 t*c 2 t) t := d 3
  have da : HasDerivAt (angle z S) (c 0 t) t := (d 4).sub_const (z S 4)
  exact ⟨profileX_hasDerivAt (c 0) (c 2) (c 3) (angle z S) t dp dq da,
    profileY_hasDerivAt (c 0) (c 2) (c 3) (angle z S) t dp dq da⟩

/-- The two vanishing seam coordinates in the physical shooting problem
force reflection of the actual positions and the signed relative angle. -/
theorem seam_reflection {z : ℝ → State} {S : ℝ}
    (hz : ∀ t, HasDerivAt z (field (z t)) t) (hv : z S 1=0) (hq : z S 3=0)
    (t : ℝ) : x z S (2*S-t) = -x z S t ∧ y z S (2*S-t) = y z S t ∧
      angle z S (2*S-t) = -angle z S t := by
  let f := fun r => atAxis (z S 4) (z (2*S-r))
  have df (r : ℝ) : HasDerivAt f (field (f r)) r :=
    axis_reverses (z S 4) z S r (hz (2*S-r))
  have eq : f=z := state_unique df hz (a:=S) (by
    dsimp [f]; rw [show 2*S-S = S by ring]
    ext i; fin_cases i <;> simp [atAxis,hv,hq]
    ring)
  have mirror : z (2*S-t) = atAxis (z S 4) (z t) := by
    have h := (congrFun eq (2*S-t)).symm
    simpa only [f,show 2*S-(2*S-t)=t by ring] using h
  have angleEq : angle z S (2*S-t) = -angle z S t := by
    simp [angle,mirror,atAxis]; ring
  refine ⟨?_,?_,angleEq⟩
  · simp only [x,angleEq,Real.cos_neg,Real.sin_neg,mirror,atAxis]
    dsimp
    ring
  · simp only [y,angleEq,Real.cos_neg,Real.sin_neg,mirror,atAxis]
    dsimp
    ring

private lemma periodic_deriv {f : ℝ → ℝ} {d : ℝ} (pf : Function.Periodic f d)
    (df : Differentiable ℝ f) : Function.Periodic (deriv f) d := by
  intro s
  have h := (df (s+d)).hasDerivAt.comp s ((hasDerivAt_id s).add_const d)
  change HasDerivAt (fun u => f (u+d)) _ s at h
  rw [show (fun u => f (u+d))=f from funext pf] at h
  simpa using h.deriv.symm

private lemma value_mod {f : ℝ → ℝ} {d : ℝ} (hd : 0<d) (per : Function.Periodic f d)
    (s : ℝ) : f (toIcoMod hd 0 s) = f s := by
  rw [← self_sub_toIcoDiv_zsmul hd 0 s]
  exact per.sub_zsmul_eq _

/-- A crossing of the seam axis with both tangent components nonzero gives
two distinct parameter labels with nonparallel tangents in *every* positive
position period. The statement includes any primitive period. -/
theorem transverse_crossing_in_every_period {z : ℝ → State} {S s d : ℝ}
    (hz : ∀ t, HasDerivAt z (field (z t)) t) (hv : z S 1=0) (hq : z S 3=0)
    (onAxis : x z S s=0) (incidence : Real.cos (angle z S s)*Real.sin (angle z S s)≠0)
    (hd : 0<d) (px : Function.Periodic (x z S) d) (py : Function.Periodic (y z S) d) :
    ∃ a∈Ico (0:ℝ) d, ∃ b∈Ico (0:ℝ) d, a≠b ∧
      x z S a=0 ∧ x z S b=0 ∧ y z S a=y z S s ∧ y z S b=y z S s ∧
      deriv (x z S) a * deriv (y z S) b - deriv (y z S) a * deriv (x z S) b ≠ 0 := by
  obtain ⟨rx,ry,ra⟩ := seam_reflection hz hv hq s
  have dx := periodic_deriv px (fun r => (position_derivatives S r hz).1.differentiableAt)
  have dy := periodic_deriv py (fun r => (position_derivatives S r hz).2.differentiableAt)
  let a := toIcoMod hd 0 s
  let b := toIcoMod hd 0 (2*S-s)
  have det : deriv (x z S) a * deriv (y z S) b - deriv (y z S) a * deriv (x z S) b ≠ 0 := by
    dsimp only [a,b]
    rw [value_mod hd dx,value_mod hd dy,value_mod hd dy,value_mod hd dx,
      (position_derivatives S s hz).1.deriv,(position_derivatives S s hz).2.deriv,
      (position_derivatives S (2*S-s) hz).1.deriv,(position_derivatives S (2*S-s) hz).2.deriv,
      ra,Real.sin_neg,Real.cos_neg]
    intro he
    apply incidence
    linarith
  refine ⟨a,toIcoMod_mem_Ico' hd _,b,toIcoMod_mem_Ico' hd _,?_,
    (value_mod hd px s).trans onAxis,?_,value_mod hd py s,(value_mod hd py _).trans ry,det⟩
  · intro he
    apply det
    rw [he]
    ring
  · rw [show x z S b = x z S (2*S-s) from value_mod hd px _,rx,onAxis,neg_zero]

end ClosedSimilarity.ReflectedCrossings

#print axioms ClosedSimilarity.ReflectedCrossings.transverse_crossing_in_every_period
