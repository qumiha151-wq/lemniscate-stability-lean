import SolitonClassification.ForceWindingPhase
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section
open Set Function
namespace ClosedSimilarity.ForceWinding

private theorem monotone_periodic_const {f:ℝ→ℝ} {L:ℝ} (lp:0<L)
    (mf : Monotone f) (pf : Periodic f L) : ∀ x,f x=f 0 := by
  have le (s t:ℝ) : f s≤f t := by
    obtain ⟨n,hn⟩ := exists_nat_gt ((s-t)/L)
    have st : s≤t+n*L := by linarith only [(div_lt_iff₀ lp).mp hn]
    exact (mf st).trans_eq (pf.nat_mul n t)
  exact fun x=>le_antisymm (le x 0) (le 0 x)

/-- A nonnegative force on a centre-avoiding periodic orbit forces strictly
positive turning, even if the force has zeros. -/
theorem positive_turn {a b L τ : ℝ} {k θ F H : ℝ→ℝ} (ap : 0<a) (lp : 0<L)
    (dθ : ∀s,HasDerivAt θ (k s) s)
    (dF : ∀s,HasDerivAt F (k s*H s-b) s) (dH : ∀s,HasDerivAt H (a-k s*F s) s)
    (pf : Periodic F L) (ph : Periodic H L) (turn : ∀s,θ (s+L)=θ s+τ)
    (pos : ∀s,0≤F s) (nc : ∀s,F s≠0 ∨ H s≠0) : 0<τ := by
  let ψ := spiralAngle a b θ F H
  let R := fun s=>(a^2+b^2)*F s/(a*supportMass F H s)
  have dv (s:ℝ) : HasDerivAt ψ (R s) s := spiralAngleD ap (dθ s) (dF s) (dH s) (pos s) (nc s)
  have mon : Monotone ψ := monotone_of_deriv_nonneg (fun s=>(dv s).differentiableAt) (fun s=>by
    rw [(dv s).deriv];dsimp [R,supportMass];positivity [pos s])
  have per (s:ℝ) : ψ (s+L)=ψ s+τ := by dsimp [ψ,spiralAngle,supportMass];rw [turn,pf,ph];ring
  by_contra! bad
  have per' : Periodic ψ L := fun s=>le_antisymm (by rw [per];linarith only [bad]) (mon (by linarith))
  have cs := monotone_periodic_const lp mon per'
  have z (s:ℝ) : F s=0 := by
    have con : ψ=fun _=>ψ 0 := funext cs
    have r := (dv s).deriv
    rw [con,deriv_const] at r
    by_contra nz
    have fp := lt_of_le_of_ne (pos s) (Ne.symm nz)
    have positive : 0<R s := by dsimp [R,supportMass];positivity
    linarith only [r,positive]
  have hm : StrictMono H := strictMono_of_hasDerivAt_pos dH (fun s=>by rw [z];simpa)
  have bad' := hm lp
  have ret : H L=H 0 := by simpa using ph 0
  exact (ne_of_lt bad') ret.symm

/-- At a common zero of both intrinsic support components a nonzero pitch
produces a strict force crossing. -/
theorem avoids_centre_of_rotating {b:ℝ} {k F H:ℝ→ℝ} (rot:b≠0)
    (df : ∀s,HasDerivAt F (k s*H s-b) s) (pos : ∀s,0≤F s) (s:ℝ) :
    F s≠0 ∨ H s≠0 := by
  by_contra! bad
  have mn : IsLocalMin F s := Filter.Eventually.of_forall (fun t=>by rw [bad.1];exact pos t)
  have e := mn.hasDerivAt_eq_zero (df s)
  rw [bad.2,mul_zero,zero_sub,neg_eq_zero] at e
  exact rot e

/-- On every rotating support orbit of zero turning, force is strictly
positive somewhere and strictly negative somewhere. -/
theorem zero_turn_rotating_changes_sign {a b L:ℝ} {k θ F H:ℝ→ℝ} (ap:0<a) (lp:0<L) (rot:b≠0)
    (dθ : ∀s,HasDerivAt θ (k s) s)
    (dF : ∀s,HasDerivAt F (k s*H s-b) s) (dH : ∀s,HasDerivAt H (a-k s*F s) s)
    (pf:Periodic F L) (ph:Periodic H L) (pt:Periodic θ L) : (∃s,F s<0) ∧ ∃s,0<F s := by
  have turn (s:ℝ) : θ (s+L)=θ s+0 := by rw [pt,add_zero]
  constructor
  · by_contra! pos
    exact (lt_irrefl (0:ℝ)) (positive_turn ap lp dθ dF dH pf ph turn pos (avoids_centre_of_rotating rot dF pos))
  · by_contra! neg
    let Fn := fun s=> -F s
    let θn := fun s=> -θ s
    let kn := fun s=> -k s
    have dn (s:ℝ) : HasDerivAt Fn (kn s*H s-(-b)) s := by apply (dF s).neg.congr_deriv;dsimp [kn];ring
    have dh (s:ℝ) : HasDerivAt H (a-kn s*Fn s) s := by simpa only [kn,Fn,neg_mul_neg] using dH s
    have dt (s:ℝ) : HasDerivAt θn (kn s) s := (dθ s).neg
    have pp (s:ℝ) : 0≤Fn s := neg_nonneg.mpr (neg s)
    have tp (s:ℝ) : θn (s+L)=θn s+0 := by dsimp [θn];rw [pt,add_zero]
    have fp : Periodic Fn L := fun s=>by dsimp [Fn];rw [pf]
    exact (lt_irrefl (0:ℝ)) (positive_turn ap lp dt dn dh fp ph tp pp (avoids_centre_of_rotating (neg_ne_zero.mpr rot) dn pp))

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.zero_turn_rotating_changes_sign
