import SolitonClassification.MeromorphicOrdinaryPole

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

/-- Matched leading coefficients together with the first coefficient of the
difference, at an arbitrary fixed positive offset. -/
structure DifferenceJet (x : ℂ) (gap n : ℤ) (c d : ℂ) (f g : ℂ → ℂ) : Prop where
  left : Jet f x n c
  right : Jet g x n c
  change : Jet (fun z => f z-g z) x (n+gap) d

namespace DifferenceJet
variable {x : ℂ} {gap n m : ℤ} {c d e h : ℂ} {f g v w : ℂ → ℂ}

theorem retag (j : DifferenceJet x gap n c d f g) {N : ℤ} {C D : ℂ}
    (a : n=N) (b : c=C) (u : d=D) : DifferenceJet x gap N C D f g := a ▸ b ▸ u ▸ j

theorem mul (j : DifferenceJet x gap n c d f g) (k : DifferenceJet x gap m e h v w) :
    DifferenceJet x gap (n+m) (c*e) (d*e+c*h) (fun z=>f z*v z) (fun z=>g z*w z) := by
  refine ⟨j.left.mul k.left,j.right.mul k.right,?_⟩
  have a := (j.change.mul k.left).retag (m:=n+m+gap) (by omega) rfl
  have b := (j.right.mul k.change).retag (m:=n+m+gap) (by omega) rfl
  apply (a.add b).congr
  filter_upwards with z
  ring

theorem add (j : DifferenceJet x gap n c d f g) (k : DifferenceJet x gap n e h v w) :
    DifferenceJet x gap n (c+e) (d+h) (fun z=>f z+v z) (fun z=>g z+w z) := by
  refine ⟨j.left.add k.left,j.right.add k.right,?_⟩
  apply (j.change.add k.change).congr
  filter_upwards with z
  ring

theorem sub (j : DifferenceJet x gap n c d f g) (k : DifferenceJet x gap n e h v w) :
    DifferenceJet x gap n (c-e) (d-h) (fun z=>f z-v z) (fun z=>g z-w z) := by
  refine ⟨j.left.sub k.left,j.right.sub k.right,?_⟩
  apply (j.change.sub k.change).congr
  filter_upwards with z
  ring

theorem smul (j : DifferenceJet x gap n c d f g) (a : ℂ) :
    DifferenceJet x gap n (a*c) (a*d) (fun z=>a*f z) (fun z=>a*g z) := by
  refine ⟨j.left.smul a,j.right.smul a,?_⟩
  apply (j.change.smul a).congr
  filter_upwards with z
  ring

theorem weaken (j : DifferenceJet x gap n c d f g) (lt : m<n) :
    DifferenceJet x gap m 0 0 f g :=
  ⟨j.left.weaken lt,j.right.weaken lt,j.change.weaken (by omega)⟩

theorem pow (j : DifferenceJet x gap n c d f g) (r : ℕ) :
    DifferenceJet x gap (r*n) (c^r) ((r:ℂ)*c^(r-1)*d)
      (fun z=>f z^r) (fun z=>g z^r) := by
  induction r with
  | zero =>
    refine ⟨j.left.pow 0,j.right.pow 0,?_⟩
    simpa using (Jet.zero x gap)
  | succ r ih =>
    have p := ih.mul j
    simp only [pow_succ, Nat.cast_succ,add_mul,one_mul] at p ⊢
    apply p.retag rfl rfl
    cases r with
    | zero => simp
    | succ r => push_cast; simp only [pow_succ]; ring

private theorem punctured_derivatives {u : ℂ → ℂ} {i : ℤ} {b : ℂ} (j : Jet u x i b) :
    ∀ᶠ z in 𝓝[≠] x, DifferentiableAt ℂ u z := by
  obtain ⟨a,ha,_,eq⟩ := j
  filter_upwards [eventually_eventually_nhdsWithin.mpr eq,ha.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with z h az nz
  rw [isOpen_compl_singleton.nhdsWithin_eq nz] at h
  have dt : HasDerivAt (fun y:ℂ=>y-x) 1 z := (hasDerivAt_id z).sub_const x
  have dp := (hasDerivAt_zpow i (z-x) (Or.inl (sub_ne_zero.mpr nz))).comp z dt
  have diff : DifferentiableAt ℂ (fun z => (z-x)^i*a z) z := by
    simpa only [Function.comp_def] using (dp.fun_mul az.differentiableAt.hasDerivAt).differentiableAt
  exact diff.congr_of_eventuallyEq h

theorem deriv (j : DifferenceJet x gap n c d f g) :
    DifferenceJet x gap (n-1) (n*c) (((n:ℂ)+gap)*d) (deriv f) (deriv g) := by
  refine ⟨j.left.deriv,j.right.deriv,?_⟩
  apply (j.change.deriv.retag (m:=n-1+gap) (by omega) (by push_cast;ring)).congr
  filter_upwards [punctured_derivatives j.left,punctured_derivatives j.right] with z a b
  exact (a.hasDerivAt.fun_sub b.hasDerivAt).deriv.symm

end DifferenceJet
end ClosedSimilarity.MeromorphicCurvature
