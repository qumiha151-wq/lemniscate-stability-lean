import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-!
# Analytic reflection bridge for the centroid expander

The input is an actual solution of the polynomial ODE on a neighborhood of
the half interval, with exact shooting endpoint equations. The module proves
reflection preserves the differential equation, gluing is differentiable at
the seam, the doubled arc closes with matching endpoint derivatives, and its
tangent has unit length. Existence of the shooting zero and validated
numerical enclosures are separate obligations, not axioms of this file.
-/

namespace CentroidEscape

noncomputable section

set_option backward.isDefEq.respectTransparency false

abbrev State := Fin 6 → ℝ

def field (z : State) : State :=
  ![z 2, z 3, -z 4 * z 3, z 4 * z 2, z 5,
    -(z 4)^3 / 2 + z 0 * z 3 - z 1 * z 2]

def reverseState (z : State) : State :=
  ![z 0, -z 1, -z 2, z 3, z 4, -z 5]

lemma reverse_involutive (z : State) : reverseState (reverseState z) = z := by
  ext i
  fin_cases i <;> simp [reverseState]

lemma field_reverse (z : State) : field (reverseState z) = -reverseState (field z) := by
  ext i
  fin_cases i <;> simp [field, reverseState]

lemma field_smooth (n : ℕ∞) : ContDiff ℝ n field := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [field] <;> fun_prop

lemma shooting_fixed (z : State) (hy : z 1 = 0) (hu : z 2 = 0) (hv : z 5 = 0) :
    reverseState z = z := by
  ext i
  fin_cases i <;> simp [reverseState, hy, hu, hv]

def reflected (z : ℝ → State) (L t : ℝ) : State := reverseState (z (2*L-t))

lemma reflected_derivative {z : ℝ → State} {L t : ℝ}
    (hz : HasDerivAt z (field (z (2*L-t))) (2*L-t)) :
    HasDerivAt (reflected z L) (field (reflected z L t)) t := by
  have ht : HasDerivAt (fun s : ℝ => 2*L-s) (-1) t := by
    convert! (hasDerivAt_id t).const_sub (2*L) using 1
  have hcomp := hz.scomp t ht
  rw [hasDerivAt_pi] at hcomp ⊢
  intro i
  fin_cases i
  · simpa [reflected, reverseState, field] using hcomp 0
  · convert! (hcomp 1).neg using 1; simp [reflected, reverseState, field]
  · convert! (hcomp 2).neg using 1; simp [reflected, reverseState, field]
  · convert! hcomp 3 using 1; simp [reflected, reverseState, field]
  · simpa [reflected, reverseState, field] using hcomp 4
  · convert! (hcomp 5).neg using 1; simp [reflected, reverseState, field]

/-- Two genuine derivatives with equal value and derivative glue at the seam. -/
lemma hasDerivAt_join {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {c : ℝ} {v : E}
    (hf : HasDerivAt f v c) (hg : HasDerivAt g v c) (hfg : f c = g c) :
    HasDerivAt (fun t => if t ≤ c then f t else g t) v c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Set.Iic c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro t ht
      simp [Set.mem_Iic.mp ht]
    · simp
  have hr : HasDerivWithinAt (fun t => if t ≤ c then f t else g t) v (Set.Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases h : t ≤ c
      · have : t = c := le_antisymm h ht
        subst t
        simpa using hfg
      · simp [h]
    · simpa using hfg
  have hh := hl.union hr
  simpa only [Set.Iic_union_Ici, hasDerivWithinAt_univ] using hh

def doubled (z : ℝ → State) (L t : ℝ) : State :=
  if t ≤ L then z t else reflected z L t

lemma doubled_at_zero {z : ℝ → State} {L : ℝ} (hL : 0 ≤ L) :
    doubled z L 0 = z 0 := by simp [doubled, hL]

lemma doubled_at_end {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (h0 : reverseState (z 0) = z 0) : doubled z L (2*L) = z 0 := by
  have : ¬2*L ≤ L := by linarith
  simp [doubled, this, reflected, h0]

/-- Exact endpoint equations close an actual ODE segment, including the seam. -/
theorem doubled_solves {z : ℝ → State} {L : ℝ}
    (hz : ∀ t ∈ Set.Icc (0:ℝ) L, HasDerivAt z (field (z t)) t)
    (hfix : reverseState (z L) = z L) {t : ℝ} (ht : t ∈ Set.Icc 0 (2*L)) :
    HasDerivAt (doubled z L) (field (doubled z L t)) t := by
  by_cases hlt : t < L
  · have hzt := hz t ⟨ht.1, hlt.le⟩
    have heq : doubled z L =ᶠ[nhds t] z := by
      filter_upwards [eventually_lt_nhds hlt] with s hs
      simp [doubled, hs.le]
    simpa [doubled, hlt.le] using hzt.congr_of_eventuallyEq heq
  · by_cases heq : t = L
    · subst t
      have hL : 0 ≤ L := ht.1
      have hr := reflected_derivative (L := L) (t := L)
        (by simpa only [show 2*L-L=L by ring] using hz L ⟨hL, le_rfl⟩)
      have hv : reflected z L L = z L := by
        simpa [reflected, show 2*L-L=L by ring] using hfix
      have hjoin := hasDerivAt_join (hz L ⟨hL, le_rfl⟩)
        (hv ▸ hr) hv.symm
      convert! hjoin using 1; simp [doubled]
    · have hgt : L < t := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      have hp : 2*L-t ∈ Set.Icc (0:ℝ) L := by
        constructor <;> linarith [ht.1, ht.2]
      have hr := reflected_derivative (L := L) (t := t) (hz _ hp)
      have hev : doubled z L =ᶠ[nhds t] reflected z L := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        simp [doubled, not_le.mpr hs]
      simpa [doubled, not_le.mpr hgt] using hr.congr_of_eventuallyEq hev

/-- Smoothness across the reflected seam follows from the polynomial ODE. -/
theorem doubled_smooth {z : ℝ → State} {L : ℝ}
    (hz : ∀ t ∈ Set.Icc (0:ℝ) L, HasDerivAt z (field (z t)) t)
    (hfix : reverseState (z L) = z L) :
    ContDiffOn ℝ (⊤ : ℕ∞) (doubled z L) (Set.Icc 0 (2*L)) := by
  apply ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
    (f := fun (_ : ℝ) z => field z) (u := Set.univ)
  · exact ((field_smooth ⊤).comp contDiff_snd).contDiffOn
  · intro t ht
    exact (doubled_solves hz hfix ht).hasDerivWithinAt
  · intro t ht
    exact Set.mem_univ _

theorem doubled_endpoint_derivatives {z : ℝ → State} {L : ℝ} (hL : 0 < L)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) L, HasDerivAt z (field (z t)) t)
    (h0 : reverseState (z 0) = z 0) (hLfix : reverseState (z L) = z L) :
    deriv (doubled z L) 0 = deriv (doubled z L) (2*L) := by
  rw [(doubled_solves hz hLfix (show (0:ℝ) ∈ Set.Icc 0 (2*L) by
      constructor <;> linarith)).deriv,
    (doubled_solves hz hLfix (show 2*L ∈ Set.Icc (0:ℝ) (2*L) by
      constructor <;> linarith)).deriv,
    doubled_at_zero hL.le, doubled_at_end hL h0]

def tangentSquare (z : State) : ℝ := (z 2)^2 + (z 3)^2

lemma tangentSquare_derivative {z : ℝ → State} {t : ℝ}
    (hz : HasDerivAt z (field (z t)) t) :
    HasDerivAt (fun s => tangentSquare (z s)) 0 t := by
  rw [hasDerivAt_pi] at hz
  have h := ((hz 2).pow 2).add ((hz 3).pow 2)
  convert! h using 1
  simp [field]
  ring

theorem tangentSquare_constant {z : ℝ → State} {a b : ℝ}
    (hz : ∀ t ∈ Set.Icc a b, HasDerivAt z (field (z t)) t)
    {t : ℝ} (ht : t ∈ Set.Icc a b) : tangentSquare (z t) = tangentSquare (z a) := by
  apply constant_of_has_deriv_right_zero (f := fun s => tangentSquare (z s))
    (fun s hs => (tangentSquare_derivative (hz s hs)).continuousAt.continuousWithinAt)
    (fun s hs => (tangentSquare_derivative (hz s ⟨hs.1, hs.2.le⟩)).hasDerivWithinAt) t ht

/-- Unit initial tangent is preserved on the doubled interval. -/
theorem doubled_unit_tangent {z : ℝ → State} {L : ℝ} (hL : 0 ≤ L)
    (hz : ∀ t ∈ Set.Icc (0:ℝ) L, HasDerivAt z (field (z t)) t)
    (hfix : reverseState (z L) = z L) (hu : z 0 2 = 0) (hw : z 0 3 = 1)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (2*L)) : tangentSquare (doubled z L t) = 1 := by
  rw [tangentSquare_constant (fun s hs => doubled_solves hz hfix hs) ht,
    doubled_at_zero hL]
  simp [tangentSquare, hu, hw]

end

end CentroidEscape

#print axioms CentroidEscape.doubled_solves
#print axioms CentroidEscape.doubled_unit_tangent

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in (← getEnv).constants do
    if (`CentroidEscape).isPrefixOf name then
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Axiom audit failed: {name} depends on {axiomName}"
      checked := checked + 1
  unless checked > 0 do
    throwError "No centroid reflection declarations were checked"
  logInfo m!"Centroid reflection audit passed for {checked} declarations."



