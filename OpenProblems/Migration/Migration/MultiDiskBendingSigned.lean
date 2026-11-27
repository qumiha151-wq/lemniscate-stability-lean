import Migration.MultiDiskBendingRecord
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set Function MeasureTheory
open scoped ContDiff
namespace MigrationGeometry.Flow.MultiBending

private theorem for_oriented (P : ℝ) (six : 6≤P) (u d e : Fn) (pu : Periodic u P) (pd : Periodic d P)
    (du : ∀t,HasDerivAt u (d t) t) (dd : ∀t,HasDerivAt d (e t) t)
    (unit : mass P (u^2)=P) (lo : mass P u<P) (hi : P≤mass P u+3/5) :
    (1/2:ℝ)*mass P (u*normalizedForce u e)<mass P ((normalizedForce u e)^2) := by
  have eq : (u-1)^2=u^2-(2:ℝ) • u+1 := by ext t;simp [smul_eq_mul];ring
  have var : mass P ((u-1)^2)=2*(P-mass P u) := by rw [eq,map_add,map_sub,map_smul,smul_eq_mul,unit,mass_one];ring
  apply strict_record P six u d e pu pd du dd unit <;> rw [var] <;> linarith

theorem signed_record (P : ℝ) (six : 6≤P) (u d e : Fn) (pu : Periodic u P) (pd : Periodic d P)
    (du : ∀t,HasDerivAt u (d t) t) (dd : ∀t,HasDerivAt d (e t) t)
    (unit : mass P (u^2)=P) (lo : |mass P u|<P) (hi : P≤|mass P u|+3/5) :
    (1/2:ℝ)*mass P (u*normalizedForce u e)<mass P ((normalizedForce u e)^2) := by
  by_cases sign : 0≤mass P u
  · rw [abs_of_nonneg sign] at lo hi
    exact for_oriented P six u d e pu pd du dd unit lo hi
  rw [abs_of_neg (lt_of_not_ge sign)] at lo hi
  have sq : (-u)^2=u^2 := by ring
  have force : normalizedForce (-u) (-e)= -normalizedForce u e := by
    ext t;simp [normalizedForce,smul_eq_mul];ring
  have z := for_oriented P six (-u) (-d) (-e) (fun t=>by simp [pu t]) (fun t=>by simp [pd t])
    (fun t=>(du t).neg) (fun t=>(dd t).neg) (sq ▸ unit)
    (by rwa [map_neg]) (by rwa [map_neg])
  simpa [force] using z

theorem strict_for_rms {u : ℝ→ℝ} {P : ℝ} (six : 6≤P) (cu : ContDiff ℝ ∞ u)
    (pu : Periodic u P) (unit : (∫x in 0..P,u x^2)=P)
    (lo : |∫x in 0..P,u x|<P) (hi : P≤|∫x in 0..P,u x|+3/5) :
    let f:=fun x=>deriv (deriv u) x+(1/2:ℝ)*u x^3
    (1/2:ℝ)*(∫x in 0..P,u x*f x)<∫x in 0..P,f x^2 := by
  have cd := (contDiff_infty_iff_deriv.mp cu).2
  let U : Fn := ⟨u,cu.continuous⟩
  let D : Fn := ⟨deriv u,cd.continuous⟩
  let E : Fn := ⟨deriv (deriv u),(contDiff_infty_iff_deriv.mp cd).2.continuous⟩
  have dd (t) : HasDerivAt U (D t) t := (cu.differentiable (by simp) t).hasDerivAt
  have de (t) : HasDerivAt D (E t) t := (cd.differentiable (by simp) t).hasDerivAt
  have pd : Periodic D P := by
    intro t
    have z := (dd (t+P)).comp_add_const t P
    change HasDerivAt (fun s=>u (s+P)) (D (t+P)) t at z
    rw [funext pu] at z
    exact z.unique (dd t)
  exact signed_record P six U D E pu pd dd de unit lo hi

end MigrationGeometry.Flow.MultiBending
#print axioms MigrationGeometry.Flow.MultiBending.strict_for_rms

