import SolitonClassification.GeometricSimilarity

noncomputable section
namespace ClosedSimilarity.ReflectedArc
open Set
open scoped ContDiff

private theorem periodic_derivative {f : ℝ→ℝ} {L : ℝ} (pf : Function.Periodic f L)
    (df : ContDiff ℝ ∞ f) : Function.Periodic (deriv f) L := by
  intro s
  have h := ((df.differentiable (by simp) (s+L)).hasDerivAt).comp s ((hasDerivAt_id s).add_const L)
  change HasDerivAt (fun u => f (u+L)) _ s at h
  rw [show (fun u => f (u+L))=f from funext pf] at h
  simpa using h.deriv.symm

namespace ZeroTurnExpander
variable {L b : ℝ} (P : ZeroTurnExpander L b)

def peakSlope : ℝ := sSup (range fun s => |deriv P.k s|)

theorem slopes_bounded (hL : 0<L) : BddAbove (range fun s => |deriv P.k s|) := by
  have pk : Function.Periodic P.k L := by
    have px := periodic_derivative P.closed_X P.X_smooth
    have py := periodic_derivative P.closed_Y P.Y_smooth
    have pxx := periodic_derivative px (contDiff_infty_iff_deriv.mp P.X_smooth).2
    have pyy := periodic_derivative py (contDiff_infty_iff_deriv.mp P.Y_smooth).2
    intro s; rw [← P.curvature,← P.curvature s,px,py,pxx,pyy]
  have pd := periodic_derivative pk P.k_smooth
  obtain ⟨M,hM⟩ := (isCompact_Icc (α:=ℝ) (a:=0) (b:=L)).bddAbove_image
    (contDiff_infty_iff_deriv.mp P.k_smooth).2.continuous.abs.continuousOn
  refine ⟨M,?_⟩
  rintro _ ⟨s,rfl⟩
  have mem := Ico_subset_Icc_self (toIcoMod_mem_Ico' hL s)
  have eq : deriv P.k (toIcoMod hL 0 s)=deriv P.k s := by
    rw [← self_sub_toIcoDiv_zsmul hL 0 s]
    exact pd.sub_zsmul_eq _
  exact hM ⟨_,mem,congrArg abs eq⟩

theorem marker_le_peak (hL : 0<L) : b ≤ P.peakSlope := by
  exact (le_abs_self b).trans (le_csSup (P.slopes_bounded hL)
    ⟨0,congrArg abs P.center_crossing.2.2.2⟩)

theorem peak_invariant {T d : ℝ} {Q : ZeroTurnExpander T d}
    (S : GeometricSimilarity P Q) (hb : b≠0) : P.peakSlope=Q.peakSlope := by
  obtain ⟨A,_,_,_⟩ := S.lifted
  obtain ⟨a4,_,_⟩ := A.scale_and_centre hb
  have area : |A.m*A.q-A.n*A.p|=1 := by
    have h := (sq_eq_sq_iff_abs_eq_abs (A.m*A.q-A.n*A.p) 1).mp (by
      simpa [a4] using A.area)
    simpa using h
  have curve (s : ℝ) : |deriv Q.k (A.a*s+A.offset)|=|deriv P.k s| := by
    have slope := congrArg abs (A.pull_slope s)
    simpa [a4,abs_mul,area] using slope
  unfold peakSlope
  congr 1
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨_,curve s⟩
  · rintro ⟨s,rfl⟩
    refine ⟨(s-A.offset)/A.a,?_⟩
    change |deriv P.k ((s-A.offset)/A.a)|=|deriv Q.k s|
    rw [← curve,show A.a*((s-A.offset)/A.a)+A.offset=s by field_simp [A.regular]; ring]

end ZeroTurnExpander

structure MarkedClosedExpander where
  period : ℝ
  marker : ℝ
  period_pos : 0<period
  marker_pos : 0<marker
  curve : ZeroTurnExpander period marker

/-- Arbitrarily large actual marked slopes yield a sequence of inequivalent
    immersed curves, modulo similarities, reparametrizations and covers. -/
theorem distinct_family_of_unbounded
    (many : ∀ r : ℝ, ∃ b>r, ∃ L> (0:ℝ), Nonempty (ZeroTurnExpander L b)) :
    ∃ family : ℕ → MarkedClosedExpander,
      StrictMono (fun n => (family n).curve.peakSlope) ∧
      (∀ i j : ℕ, i≠j → IsEmpty (GeometricSimilarity (family i).curve (family j).curve)) := by
  classical
  have above (r : ℝ) : ∃ P : MarkedClosedExpander, r<P.curve.peakSlope := by
    obtain ⟨b,hb,L,hL,⟨Q⟩⟩ := many (max r 0)
    let P : MarkedClosedExpander := ⟨L,b,hL,(le_max_right ..).trans_lt hb,Q⟩
    exact ⟨P,((le_max_left ..).trans_lt hb).trans_le (Q.marker_le_peak hL)⟩
  choose next larger using above
  let F : ℕ→MarkedClosedExpander := fun n => Nat.rec (next 0) (fun _ P => next P.curve.peakSlope) n
  have inc : StrictMono (fun n => (F n).curve.peakSlope) :=
    strictMono_nat_of_lt_succ (fun n => larger (F n).curve.peakSlope)
  refine ⟨F,inc,fun i j h => ⟨fun S => h (inc.injective ?_)⟩⟩
  exact (F i).curve.peak_invariant S (F i).marker_pos.ne'

end ClosedSimilarity.ReflectedArc
#print axioms ClosedSimilarity.ReflectedArc.distinct_family_of_unbounded
