import Migration.ProjectedAdjoint
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
namespace MigrationGeometry.Adjoint.Frame
variable {r L : ℝ} (f : Frame r L) {a : ℝ} (ha : 0<a) (rate : r=a^4)

def normalize : Frame 1 (a*L) := by
  have dt (s : ℝ) : HasDerivAt (fun t : ℝ => t/a) (1/a) s := (hasDerivAt_id s).div_const a
  refine {
    k := fun t => f.k (t/a)/a, v := fun t => f.v (t/a)/a^2,
    p := fun t => a*f.p (t/a), q := fun t => a*f.q (t/a),
    h := fun t => a*f.h (t/a), u := fun t => f.u (t/a), n := fun t => f.n (t/a),
    kD := ?_, vD := ?_, pD := ?_, qD := ?_, hD := ?_, uD := ?_, nD := ?_,
    decompose := ?_, periodic := ?_ }
  · intro s
    apply (((f.kD _).comp s (dt s)).div_const a).congr_deriv
    field_simp
  · intro s
    apply (((f.vD _).comp s (dt s)).div_const (a^2)).congr_deriv
    generalize f.k (s/a)=k
    generalize f.p (s/a)=p
    rw [rate]; field_simp
  · intro s
    apply (((f.pD _).comp s (dt s)).const_mul a).congr_deriv
    field_simp
  · intro s
    apply (((f.qD _).comp s (dt s)).const_mul a).congr_deriv
    field_simp
  · intro s
    apply (((f.hD _).comp s (dt s)).const_mul a).congr_deriv
    field_simp
  · intro s
    apply ((f.uD _).comp s (dt s)).congr_deriv
    ring
  · intro s
    apply ((f.nD _).comp s (dt s)).congr_deriv
    ring
  · intro s
    rw [f.decompose]; ring
  · intro s
    rw [show (s+a*L)/a=s/a+L by field_simp]
    obtain ⟨k,v,p,q,h,u,n⟩ := f.periodic (s/a)
    simp [k,v,p,q,h,u,n]

end MigrationGeometry.Adjoint.Frame
