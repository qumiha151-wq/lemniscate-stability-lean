import SolitonClassification.ForceWindingStress
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Filter
open scoped Topology
namespace ClosedSimilarity.ForceWinding

def shiftedProjection (h x:ℝ) := x^2/2+h^2
def shiftedAngle (h:ℝ) (θ k v:ℝ→ℝ) (s:ℝ) :=
  θ s+(rect (shiftedProjection h (k s)) (v s)).arg

theorem shiftedAngleD {h:ℝ} {θ k v F:ℝ→ℝ} {s:ℝ} (hp:0<h)
    (dt:HasDerivAt θ (k s) s) (dk:HasDerivAt k (v s) s) (dv:HasDerivAt v (F s-(k s)^3/2) s) :
    let A:=shiftedProjection h (k s)
    HasDerivAt (shiftedAngle h θ k v) (A*(F s+h^2*k s)/(A^2+(v s)^2)) s := by
  let A := shiftedProjection h (k s)
  have ap : 0<A := by dsimp [A,shiftedProjection];positivity
  have den : 0<A^2+(v s)^2 := by positivity
  have ds : HasDerivAt (fun t=>shiftedProjection h (k t)) (k s*v s) s := by
    apply (((dk.pow 2).div_const 2).add_const (h^2)).congr_deriv
    simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one];ring
  have z := argumentD ds dv (Or.inl ap)
  apply (dt.add z).congr_deriv
  change k s+(A*(F s-k s^3/2)-v s*(k s*v s))/(A^2+v s^2)=A*(F s+h^2*k s)/(A^2+v s^2)
  field_simp [den.ne']
  dsimp [A,shiftedProjection];ring

private theorem tilted_monotone {h:ℝ} {θ k v F:ℝ→ℝ} (hp:0<h)
    (dt:∀s,HasDerivAt θ (k s) s) (dk:∀s,HasDerivAt k (v s) s)
    (dv:∀s,HasDerivAt v (F s-(k s)^3/2) s) (pos:∀s,0≤F s) :
    Monotone (fun s=>shiftedAngle h θ k v s+h*s) := by
  let A := fun s=>shiftedProjection h (k s)
  have der (s:ℝ) : HasDerivAt (fun t=>shiftedAngle h θ k v t+h*t)
      (A s*(F s+h^2*k s)/((A s)^2+(v s)^2)+h) s := by
    simpa only [A,id_eq,mul_one] using (shiftedAngleD hp (dt s) (dk s) (dv s)).fun_add ((hasDerivAt_id s).const_mul h)
  apply monotone_of_deriv_nonneg (fun s=>(der s).differentiableAt)
  intro s
  rw [(der s).deriv]
  have ap : 0<A s := by dsimp [A,shiftedProjection];positivity
  have hh : 0≤A s+h*k s := by
    dsimp [A,shiftedProjection];nlinarith only [sq_nonneg (k s+h),sq_nonneg h]
  have den : 0<(A s)^2+(v s)^2 := by positivity
  rw [←neg_le_iff_add_nonneg]
  apply (le_div_iff₀ den).mpr
  nlinarith only [mul_nonneg (mul_nonneg ap.le hp.le) hh,
    mul_nonneg ap.le (pos s),mul_nonneg hp.le (sq_nonneg (v s))]

private theorem shift_cont {θ k v:ℝ→ℝ} (s:ℝ) (nz:k s≠0) :
    ContinuousAt (fun h=>shiftedAngle h θ k v s) 0 := by
  have slit : rect (shiftedProjection 0 (k s)) (v s)∈Complex.slitPlane := by
    left;simp only [rect_re,shiftedProjection];positivity
  have c : ContinuousAt (fun h:ℝ=>rect (shiftedProjection h (k s)) (v s)) 0 := by unfold rect shiftedProjection;fun_prop
  exact (continuousAt_const (y:=θ s)).add ((Complex.continuousAt_arg slit).comp' (f:=fun h:ℝ=>rect (shiftedProjection h (k s)) (v s)) c)

/-- At zero total turning a weakly nonnegative elastic force must vanish
wherever curvature is nonzero, for arbitrary smooth periodic curvature data. -/
theorem zero_at_regular {L:ℝ} {θ k v F:ℝ→ℝ} (lp:0<L) (pt:Periodic θ L) (pk:Periodic k L)
    (pv:Periodic v L) (dt:∀s,HasDerivAt θ (k s) s) (dk:∀s,HasDerivAt k (v s) s)
    (dv:∀s,HasDerivAt v (F s-(k s)^3/2) s) (pos:∀s,0≤F s) {s:ℝ} (ns:k s≠0) : F s=0 := by
  have le (x y:ℝ) (nx:k x≠0) (ny:k y≠0) : shiftedAngle 0 θ k v x≤shiftedAngle 0 θ k v y := by
    obtain ⟨n,hn⟩ := exists_nat_gt ((x-y)/L)
    have xy : x≤y+n*L := by linarith only [(div_lt_iff₀ lp).mp hn]
    have period (h:ℝ) : Periodic (shiftedAngle h θ k v) L := fun u=>by
      dsimp [shiftedAngle];rw [pt,pk,pv]
    have cmp (h:ℝ) (hp:0<h) : shiftedAngle h θ k v x+h*x≤shiftedAngle h θ k v y+h*(y+n*L) := by
      have z := tilted_monotone hp dt dk dv pos xy
      change _≤shiftedAngle h θ k v (y+n*L)+_ at z
      rwa [(period h).nat_mul n y] at z
    have cx := (shift_cont (θ:=θ) (v:=v) x nx).add (continuousAt_id.mul (continuousAt_const (y:=x)))
    have cy := (shift_cont (θ:=θ) (v:=v) y ny).add (continuousAt_id.mul (continuousAt_const (y:=y+n*L)))
    have bounds := le_of_tendsto_of_tendsto (cx.continuousWithinAt (s:=Ioi (0:ℝ))) cy.continuousWithinAt
      (Filter.mem_of_superset self_mem_nhdsWithin (fun h hh=>cmp h hh))
    simpa only [Pi.add_apply,Pi.mul_apply,id_eq,zero_mul,add_zero] using bounds
  have openN : ∀ᶠ x in 𝓝 s,k x≠0 := (dk s).continuousAt.eventually_ne ns
  let Ψ := shiftedAngle 0 θ k v
  have flat : Ψ=ᶠ[𝓝 s] (fun _=>Ψ s) := by
    filter_upwards [openN] with x hx using le_antisymm (le x s hx ns) (le s x ns hx)
  have dz : HasDerivAt Ψ 0 s := (hasDerivAt_const s (Ψ s)).congr_of_eventuallyEq flat
  have dtot := (dt s).add (stressAngleD (dk s) (dv s) (Or.inl ns))
  have e : Ψ=(fun u=>θ u+stressAngle k v u) := by funext u;simp [Ψ,shiftedAngle,shiftedProjection,stressAngle]
  rw [e] at dz
  have z := dtot.unique dz
  have rr : stressAngleRate k v F s=0 := by linarith only [z]
  unfold stressAngleRate at rr
  have den : 0<2*stressMass k v s := by dsimp [stressMass];positivity
  exact (mul_eq_zero.mp ((div_eq_zero_iff.mp rr).resolve_right den.ne')).resolve_left (pow_ne_zero _ ns)

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.zero_at_regular
