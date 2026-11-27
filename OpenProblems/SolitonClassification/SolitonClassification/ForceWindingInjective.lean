import SolitonClassification.ForceWindingTrace
import SolitonClassification.ForceWindingTurn

noncomputable section
open Set Function Filter
open scoped Topology
namespace ClosedSimilarity.ForceWinding

private theorem no_flat_return {a b:ℝ} {k θ F H:ℝ→ℝ} (ap:0<a)
    (dθ:∀s,HasDerivAt θ (k s) s)
    (dF:∀s,HasDerivAt F (k s*H s-b) s) (dH:∀s,HasDerivAt H (a-k s*F s) s)
    (pos:∀s,0≤F s) (nc:∀s,F s≠0 ∨ H s≠0)
    (mon:Monotone (spiralAngle a b θ F H)) {s t:ℝ} (st:s<t)
    (same:supportMass F H s=supportMass F H t) :
    spiralAngle a b θ F H s≠spiralAngle a b θ F H t := by
  intro eq
  have dm (u:ℝ) : HasDerivAt (supportMass F H) (2*(a*H u-b*F u)) u := by
    apply (((dF u).pow 2).add ((dH u).pow 2)).congr_deriv
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one];ring
  have cm : Continuous (supportMass F H) := continuous_iff_continuousAt.mpr (fun u=>(dm u).continuousAt)
  obtain ⟨u,hu,du⟩ := exists_hasDerivAt_eq_zero st cm.continuousOn same (fun u _=>dm u)
  let ψ := spiralAngle a b θ F H
  have localEq : ψ=ᶠ[𝓝 u] (fun _=>ψ s) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with y hy
    exact le_antisymm ((mon hy.2.le).trans_eq eq.symm) (mon hy.1.le)
  have dzero : HasDerivAt ψ 0 u := (hasDerivAt_const u (ψ s)).congr_of_eventuallyEq localEq
  have dψ := spiralAngleD ap (dθ u) (dF u) (dH u) (pos u) (nc u)
  have e := dψ.unique dzero
  have mass : 0<supportMass F H u := by
    obtain x|x := nc u <;> dsimp [supportMass] <;> positivity
  have fn : F u=0 := by
    have v := (div_eq_zero_iff.mp e).resolve_right (mul_pos ap mass).ne'
    exact (mul_eq_zero.mp v).resolve_left (by positivity)
  have hn : H u=0 := by rw [fn,mul_zero,sub_zero] at du;rcases mul_eq_zero.mp du with h|h;norm_num at h;exact (mul_eq_zero.mp h).resolve_left ap.ne'
  exact (nc u).elim (fun h=>h fn) (fun h=>h hn)

/-- Two interior labels differing by less than one period of a one-turn positive-force
profile give distinct reconstructed positions. Force may vanish anywhere away from the centre. -/
theorem one_turn_distinct {a b L:ℝ} {k θ F H:ℝ→ℝ} (ap:0<a)
    (dθ:∀s,HasDerivAt θ (k s) s)
    (dF:∀s,HasDerivAt F (k s*H s-b) s) (dH:∀s,HasDerivAt H (a-k s*F s) s)
    (pf:Periodic F L) (ph:Periodic H L) (turn:∀s,θ (s+L)=θ s+2*Real.pi)
    (pos:∀s,0≤F s) (nc:∀s,F s≠0 ∨ H s≠0)
    {s t:ℝ} (st:s<t) (near:t<s+L) : liftedPoint θ F H s≠liftedPoint θ F H t := by
  let ψ := spiralAngle a b θ F H
  have mon : Monotone ψ := monotone_of_deriv_nonneg (fun u=>(spiralAngleD ap (dθ u) (dF u) (dH u) (pos u) (nc u)).differentiableAt)
    (fun u=>by rw [(spiralAngleD ap (dθ u) (dF u) (dH u) (pos u) (nc u)).deriv]
               dsimp [supportMass];positivity [pos u])
  have per (s:ℝ) : ψ (s+L)=ψ s+2*Real.pi := by dsimp [ψ,spiralAngle,supportMass];rw [turn,pf,ph];ring
  intro eq
  obtain ⟨em,j,je⟩ := duplicate_phase (a:=a) (b:=b) (nc t) eq
  change ψ t=ψ s+j*(2*Real.pi) at je
  have upper := mon near.le
  rw [per] at upper
  have lo : 0≤(j:ℝ) := by
    have : 0≤(j:ℝ)*(2*Real.pi) := by linarith only [je,mon st.le]
    exact nonneg_of_mul_nonneg_left this (by positivity)
  have hi : (j:ℝ)≤1 := by
    apply (le_of_mul_le_mul_right ?_ (show 0<2*Real.pi by positivity))
    rw [one_mul];linarith only [je,upper]
  have j0 : (0:ℤ)≤j := by exact_mod_cast lo
  have j1 : j≤(1:ℤ) := by exact_mod_cast hi
  rcases (show j=0 ∨ j=1 by omega) with z|o
  · rw [z,Int.cast_zero,zero_mul,add_zero] at je
    exact no_flat_return ap dθ dF dH pos nc mon st em je.symm
  · rw [o,Int.cast_one,one_mul] at je
    have next : supportMass F H t=supportMass F H (s+L) := by
      unfold supportMass;rw [pf,ph];exact em.symm
    exact no_flat_return ap dθ dF dH pos nc mon near next (je.trans (per s).symm)

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.one_turn_distinct
