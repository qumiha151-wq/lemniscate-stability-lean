import SolitonClassification.ForceWindingPhysical
import SolitonClassification.Rotating.IntegerFinalDoublePoints

noncomputable section
open Function Set
namespace SolitonClassification.Rotating.IntegerTarget.Physical
open ClosedSimilarity ClosedSimilarity.ForceWinding

theorem sign_change_of_two_double_points {P:Seed} (ev:DoublePointEvolution P) :
    (∃u, deriv (deriv P.I.k) u + (P.I.k u)^3/2<0) ∧
    ∃v, 0<deriv (deriv P.I.k) v+(P.I.k v)^3/2 := by
  let I := P.I
  let θ := I.theta
  let p := fun u=>I.x u*(-Real.sin (θ u))+I.y u*Real.cos (θ u)
  let q := fun u=>I.x u*Real.cos (θ u)+I.y u*Real.sin (θ u)
  have dp (u:ℝ) : HasDerivAt p (-(I.k u)*q u) u := by
    apply (((I.tangentX u).mul (I.angleDerivative u).sin.neg).add
      ((I.tangentY u).mul (I.angleDerivative u).cos)).congr_deriv
    dsimp [q,θ];ring
  have dq (u:ℝ) : HasDerivAt q (1+I.k u*p u) u := by
    apply (((I.tangentX u).mul (I.angleDerivative u).cos).add
      ((I.tangentY u).mul (I.angleDerivative u).sin)).congr_deriv
    dsimp [p,θ];linear_combination Real.cos_sq_add_sin_sq (I.theta u)
  have pp : Periodic p P.L := fun u=>by
    dsimp only [p,θ];rw [I.turning,I.periodX,I.periodY,Real.sin_sub_two_pi,Real.cos_sub_two_pi]
  have pq : Periodic q P.L := fun u=>by
    dsimp only [q,θ];rw [I.turning,I.periodX,I.periodY,Real.sin_sub_two_pi,Real.cos_sub_two_pi]
  have px (u:ℝ) : profileX p q θ u=I.x u := by
    dsimp [profileX,p,q];linear_combination I.x u*Real.cos_sq_add_sin_sq (θ u)
  have py (u:ℝ) : profileY p q θ u=I.y u := by
    dsimp [profileY,p,q];linear_combination I.y u*Real.cos_sq_add_sin_sq (θ u)
  obtain ⟨z,_⟩ := ev.initial_pairs
  let s := (z.pair 0).1
  let t := (z.pair 0).2
  obtain ⟨lo,st,hi⟩ := z.inside 0
  have s0 : -(P.L/2)≤s := lo
  have t1 : t<P.L/2 := hi
  have e := z.coincide 0
  have ex : profileX p q θ s=profileX p q θ t := by
    rw [px,px];exact congrArg Prod.fst e
  have ey : profileY p q θ s=profileY p q θ t := by
    rw [py,py];exact congrArg Prod.snd e
  have bz : P.b≠0 := by linarith only [ev.evolution.rotation_range.1]
  have lp : 0<P.L := by linarith only [ev.evolution.length_range.1]
  obtain ⟨⟨u,hu⟩,v,hv⟩ := physical_crossing (a:=1) (by norm_num) lp bz I.angleDerivative dp dq pp pq
    I.turning st (show t<s+P.L by linarith only [s0,t1]) ex ey
  have fx (r:ℝ) : deriv (deriv I.k) r+(I.k r)^3/2 = -(1:ℝ)*p r-P.b*q r := by
    rw [I.soliton,(I.tangentX r).deriv,(I.tangentY r).deriv]
    dsimp [p,q,θ];ring
  exact ⟨⟨u,(fx u).trans_lt hu⟩,v,hv.trans_eq (fx v).symm⟩

theorem exists_rotating_crossings_and_signed_force :
    ∃P:Seed,DoublePointEvolution P ∧
      (∃u,deriv (deriv P.I.k) u+(P.I.k u)^3/2<0) ∧
      ∃v,0<deriv (deriv P.I.k) v+(P.I.k v)^3/2 := by
  obtain ⟨P,ev⟩ := exists_primitive_two_double_point_evolution
  exact ⟨P,ev,sign_change_of_two_double_points ev⟩

end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.exists_rotating_crossings_and_signed_force
