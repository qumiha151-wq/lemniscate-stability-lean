import SolitonClassification.ReflectedArc
import SolitonClassification.Rotating.PrimitiveSupportPeriod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Connected.Clopen
import Lean.Util.CollectAxioms

/-! Primitive-period and centre-marker rigidity for reflected pure expanders. -/
noncomputable section
namespace ClosedSimilarity.ReflectedMarker
open Set Filter Function ReflectedArc
open scoped Topology ContDiff
open SolitonClassification.Rotating.PrimitiveSupportPeriod (periods)
set_option backward.isDefEq.respectTransparency false

def Solves (z : ℝ → Support) := ∀ t, HasDerivAt z (supportField (z t)) t

def center (z : Support) : Support := ![-z 0,z 1,-z 2,-z 3]
def axis (z : Support) : Support := ![z 0,-z 1,z 2,-z 3]

private theorem smooth_field : ContDiff ℝ 1 supportField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [supportField] <;> fun_prop

/-- Uniqueness for the actual polynomial support equation. The field need only
be locally Lipschitz, since both solutions are defined on the real line. -/
theorem support_unique {f g : ℝ → Support} (hf : Solves f) (hg : Solves g)
    {a : ℝ} (ha : f a = g a) : f=g := by
  have cf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have cg : Continuous g := continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)
  let E := {x | f x = g x}
  have hclosed : IsClosed E := isClosed_eq cf cg
  have hopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have eqx : f x = g x := hx
    obtain ⟨K,V,hV,hK⟩ := (smooth_field.contDiffAt (x := f x)).exists_lipschitzOnWith
    have hfv : ∀ᶠ t in 𝓝 x, f t ∈ V := cf.continuousAt hV
    have hgv : ∀ᶠ t in 𝓝 x, g t ∈ V := cg.continuousAt (eqx ▸ hV)
    exact ODE_solution_unique_of_eventually (v := fun _ => supportField) (s := fun _ => V)
      (Eventually.of_forall (fun _ => hK)) (hfv.mono (fun t ht => ⟨hf t,ht⟩))
      (hgv.mono (fun t ht => ⟨hg t,ht⟩)) eqx
  have hall := (show IsClopen E from ⟨hclosed,hopen⟩).eq_univ ⟨a,ha⟩
  exact funext (fun x => (show x∈E from hall.symm ▸ mem_univ x))

theorem period_of_recurrence {z : ℝ → Support} (hz : Solves z) {a b : ℝ} (he : z a=z b) :
    Periodic z (a-b) := by
  have hshift : Solves (fun x => z (x+(a-b))) := fun x => (hz (x+(a-b))).comp_add_const x (a-b)
  have eq := support_unique hshift hz (a := b) (by simpa using he)
  exact congrFun eq

private theorem center_flip {z : ℝ → Support} (hz : Solves z) (l : ℝ) :
    Solves (fun s => center (z (2*l-s))) := by
  intro t
  have hc : HasDerivAt (fun s : ℝ => 2*l-s) (-1) t := by
    convert! (hasDerivAt_id t).const_sub (2*l) using 1
  have hd := (hz (2*l-t)).scomp t hc
  simp only [Function.comp_def,neg_one_smul] at hd
  have d := hasDerivAt_pi.mp hd
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (d 0).neg using 1
    simp [center,supportField]
  · convert! d 1 using 1
    simp [center,supportField]
    ring
  · convert! (d 2).neg using 1
    simp [center,supportField]
  · convert! (d 3).neg using 1
    simp [center,supportField]

private theorem axis_flip {z : ℝ → Support} (hz : Solves z) (l : ℝ) :
    Solves (fun s => axis (z (2*l-s))) := by
  intro t
  have hc : HasDerivAt (fun s : ℝ => 2*l-s) (-1) t := by
    convert! (hasDerivAt_id t).const_sub (2*l) using 1
  have hd := (hz (2*l-t)).scomp t hc
  simp only [Function.comp_def,neg_one_smul] at hd
  have d := hasDerivAt_pi.mp hd
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [axis,supportField] using d 0
  · convert! (d 1).neg using 1
    simp [axis,supportField]
  · simpa [axis,supportField] using d 2
  · convert! (d 3).neg using 1
    simp [axis,supportField]

/-- The two boundary conditions at the axial seam determine its action
at twice the segment length from ODE uniqueness. -/
theorem opposite_mark {z : ℝ → Support} (hz : Solves z) {b l : ℝ}
    (hi : z 0=![0,b,0,0]) (hv : z l 1=0) (hq : z l 3=0) :
    z (2*l)=![0,-b,0,0] := by
  have fix : axis (z l)=z l := by ext i; fin_cases i <;> simp [axis,hv,hq]
  have eq := support_unique (axis_flip hz l) hz (a := l) (by
    rwa [show 2*l-l=l by ring])
  have h := congrFun eq (2*l)
  simpa [hi,axis] using h.symm

/-- At any other zero-curvature centre crossing, its phase and its negative
coincide, making twice the crossing time a period. -/
theorem doubled_phase_is_period {z : ℝ → Support} (hz : Solves z) {b s : ℝ}
    (hi : z 0=![0,b,0,0]) (hk : z s 0=0) (hp : z s 2=0) (hq : z s 3=0) :
    Periodic z (2*s) := by
  have eq := support_unique (center_flip hz 0) hz (a := 0) (by
    simp [hi,center])
  have hx := congrFun eq (-s)
  have fix : center (z s)=z s := by ext i; fin_cases i <;> simp [center,hk,hp,hq]
  have h : z s=z (-s) := by simpa [fix] using hx
  simpa only [sub_neg_eq_add, ← two_mul] using period_of_recurrence hz h

/-- Existence of a least positive support period from the positive marker
derivative and any positive recurrence period. -/
theorem least_support_period {z : ℝ → Support} (hz : Solves z) {b T : ℝ}
    (hi : z 0=![0,b,0,0]) (hb : 0<b) (hT : 0<T) (hper : Periodic z T) :
    ∃ P, IsLeast {d : ℝ | Periodic z d ∧ 0<d} P := by
  let S := periods z
  have hd : HasDerivAt (fun s => z s 0) b 0 := by
    simpa [supportField,hi] using hasDerivAt_pi.mp (hz 0) 0
  have hsl := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  have hn : {s : ℝ | 0 < slope (fun t => z t 0) 0 s} ∈ 𝓝[>] (0:ℝ) :=
    hsl (Ioi_mem_nhds hb)
  obtain ⟨δ,hδ,hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hn
  have hdis : Disjoint (S : Set ℝ) (Ioo 0 δ) := by
    apply Set.disjoint_left.mpr
    intro s hs ht
    have h := hsmall ht
    have he := congrArg (fun a : Support => a 0) (show Periodic z s from hs).eq
    change 0<slope (fun t => z t 0) 0 s at h
    simp [slope_def_field,he] at h
  have hne : S≠⊥ := by
    intro e
    have ht : T∈S := hper
    rw [e] at ht
    exact hT.ne' (by simpa using ht)
  exact AddSubgroup.exists_isLeast_pos hne (show 0<δ from hδ) hdis

/-- The two possible support states of any phase whose double is a period. -/
theorem at_period_or_half {Y : Type*} {z : ℝ → Y} {P s : ℝ}
    (hP : IsLeast {d : ℝ | Periodic z d ∧ 0<d} P) (hs : Periodic z (2*s)) :
    z s=z 0 ∨ z s=z (P/2) := by
  let S := periods z
  have hgen := AddSubgroup.cyclic_of_min (H := S) hP
  have hmem : 2*s∈S := hs
  rw [hgen,AddSubgroup.mem_closure_singleton] at hmem
  obtain ⟨n,hn⟩ := hmem
  rw [zsmul_eq_mul] at hn
  rcases Int.even_or_odd n with ⟨j,hj⟩ | ⟨j,hj⟩
  · subst n
    push_cast at hn
    left
    rw [show s=(j:ℝ)*P by linarith]
    exact hP.1.1.int_mul_eq j
  · subst n
    push_cast at hn
    right
    rw [show s=P/2+(j:ℝ)*P by linarith]
    exact hP.1.1.int_mul j (P/2)

/-- Every global orbit having the two certified seam conditions is periodic.
All zero-curvature visits to the centre have precisely one of the two
marked states, and their curvature derivatives have the same magnitude. -/
theorem primitive_marker_of_seams {z : ℝ → Support} (hz : Solves z) {b l : ℝ}
    (hb : 0<b) (hl : 0<l) (hi : z 0=![0,b,0,0]) (hv : z l 1=0) (hq : z l 3=0) :
    ∃ P, IsLeast {d : ℝ | Periodic z d ∧ 0<d} P ∧
      z (2*l)=![0,-b,0,0] ∧ z (P/2)=![0,-b,0,0] ∧
      ∀ s, z s 0=0 → z s 2=0 → z s 3=0 →
        (z s=z 0 ∨ z s=z (P/2)) ∧ |deriv (fun x => z x 0) s|=b := by
  have hop := opposite_mark hz hi hv hq
  have hdouble := doubled_phase_is_period (s := 2*l) hz hi (by simp [hop]) (by simp [hop]) (by simp [hop])
  have hper : Periodic z (4*l) := by simpa only [show 2*(2*l)=4*l by ring] using hdouble
  obtain ⟨P,hP⟩ := least_support_period hz hi hb (by linarith : 0<4*l) hper
  have hhalf : z (2*l)=z (P/2) := by
    rcases at_period_or_half hP hdouble with h|h
    · have hh := congrArg (fun y : Support => y 1) h
      simp [hi,hop] at hh
      linarith
    · exact h
  have hm : z (P/2)=![0,-b,0,0] := hhalf.symm.trans hop
  refine ⟨P,hP,hop,hm,fun s hk hp hq' => ?_⟩
  have hstates := at_period_or_half hP (doubled_phase_is_period hz hi hk hp hq')
  refine ⟨hstates,?_⟩
  have hd : deriv (fun x => z x 0) s = z s 1 :=
    (show HasDerivAt (fun x => z x 0) (z s 1) s from hasDerivAt_pi.mp (hz s) 0).deriv
  rw [hd]
  rcases hstates with h|h
  · simp [h,hi,abs_of_pos hb]
  · simp [h,hm,abs_of_pos hb]

/-- The four phase-space coordinates of the smooth five-state closure,
discarding only the continuous lift of the tangent angle. -/
def support (y : ℝ → State) (s : ℝ) : Support := ![y s 0,y s 1,y s 2,y s 3]

private theorem solves_support {y : ℝ → State} (hy : ∀ s, HasDerivAt y (field (y s)) s) :
    Solves (support y) := by
  intro s
  apply hasDerivAt_pi.mpr
  intro i
  have d := hasDerivAt_pi.mp (hy s)
  fin_cases i
  · simpa [support,supportField,field] using d 0
  · simpa [support,supportField,field] using d 1
  · simpa [support,supportField,field] using d 2
  · simpa [support,supportField,field] using d 3

/-- From a genuine finite solving arc to a smooth closing state with its
least support period and unique absolute centre-crossing curvature slope.
Centre crossings are tested on the reconstructed Cartesian position. -/
theorem closed_marker_of_quarter {z : ℝ → Support} {l b : ℝ} (hl : 0<l) (hb : 0<b)
    (cz : Continuous z) (hz : ∀ t∈Icc 0 l, HasDerivAt z (supportField (z t)) t)
    (hi : z 0=![0,b,0,0]) (hv : z l 1=0) (hq : z l 3=0) :
    ∃ y : ℝ → State, Periodic y (4*l) ∧ ContDiff ℝ ∞ y ∧
      (∀ t, HasDerivAt y (field (y t)) t) ∧ (∀ t∈Icc 0 l, y t=withAngle z t) ∧
      ∃ P, IsLeast {d : ℝ | Periodic (support y) d ∧ 0<d} P ∧
        support y 0=![0,b,0,0] ∧ support y (P/2)=![0,-b,0,0] ∧
        ∀ s, y s 0=0 →
          profileX (fun t => y t 2) (fun t => y t 3) (fun t => y t 4) s=0 →
          profileY (fun t => y t 2) (fun t => y t 3) (fun t => y t 4) s=0 →
          |deriv (fun t => y t 0) s|=b := by
  obtain ⟨y,hper,cy,dy,agree,_,_⟩ := closed_state_of_quarter hl cz hz hi hv hq
  have a0 := agree 0 ⟨le_rfl,hl.le⟩
  have al := agree l ⟨hl.le,le_rfl⟩
  have init : support y 0=![0,b,0,0] := by ext i; fin_cases i <;> simp [support,a0,withAngle,hi]
  obtain ⟨P,hP,_,hm,hmk⟩ := primitive_marker_of_seams (solves_support dy) hb hl init
    (by simp [support,al,withAngle,hv]) (by simp [support,al,withAngle,hq])
  refine ⟨y,hper,cy,dy,agree,P,hP,init,hm,fun s hk hx hy => ?_⟩
  have hp := normal_support (fun t => y t 2) (fun t => y t 3) (fun t => y t 4) s
  have hq' := tangent_support (fun t => y t 2) (fun t => y t 3) (fun t => y t 4) s
  rw [hx,hy] at hp hq'
  exact (hmk s hk (by simpa [support] using hp.symm) (by simpa [support] using hq'.symm)).2

end ClosedSimilarity.ReflectedMarker

open Lean Elab Command in
run_cmd do
  let names := #[`ClosedSimilarity.ReflectedMarker.support_unique,
    `ClosedSimilarity.ReflectedMarker.period_of_recurrence,
    `ClosedSimilarity.ReflectedMarker.opposite_mark,
    `ClosedSimilarity.ReflectedMarker.doubled_phase_is_period,
    `ClosedSimilarity.ReflectedMarker.least_support_period,
    `ClosedSimilarity.ReflectedMarker.at_period_or_half,
    `ClosedSimilarity.ReflectedMarker.primitive_marker_of_seams,
    `ClosedSimilarity.ReflectedMarker.closed_marker_of_quarter]
  for n in names do
    for a in (← collectAxioms n) do
      unless #[`propext,`Classical.choice,`Quot.sound].contains a do throwError "Unexpected axiom {a} in {n}"
  logInfo "REFLECTED_MARKER: primitive support period and actual Cartesian centre-crossing derivative magnitude."
