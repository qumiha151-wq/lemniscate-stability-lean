import SolitonClassification.CentreExpanderRadius
import SolitonClassification.UnboundedClosedExpanders

noncomputable section
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open GlobalSupport OuterStress MeasureTheory Set

/-- The initial centre orbit has at least ⌊b/(4608π)⌋ distinct simple
    curvature zeros at positive times at most √b/576. -/
theorem many_early_simple_inflections {L b : ℝ} (P : ZeroTurnExpander L b) (large : 32≤b) :
    let N := ⌊b/(4608*Real.pi)⌋₊
    ∃ v : Fin N → ℝ, Function.Injective v ∧
      ∀ i, 0<v i ∧ v i≤Real.sqrt b/576 ∧ P.k (v i)=0 ∧ deriv P.k (v i)≠0 := by
  have bp : 0<b := by linarith
  let δ := b⁻¹
  let z := centreData b bp
  have hd : 0<δ := inv_pos.mpr bp
  have small : δ≤1/32 := by change b⁻¹≤_; rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) large
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨hk,hv,hp,hq⟩ := init
  have bounds (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      Rates δ x z.root z.shape z.slope z.along z.across ∧ |z.along x|≤1 ∧ |z.across x|≤1 ∧
      4*1*δ≤z.root x^3 ∧ 1/2≤z.root x := by
    obtain ⟨pq,amp⟩ := z.centre_bounds hd hk hv hp hq hx.1
    have x2 := pow_le_pow_left₀ hx.1 hx.2 2
    have lower : 1/2≤z.amplitude x := by nlinarith
    have apos : 0<z.amplitude x := by linarith
    have rsq : z.root x^2=z.amplitude x := Real.sq_sqrt apos.le
    have pos : 0≤z.root x := Real.sqrt_nonneg _
    have rlo : 1/2≤z.root x := le_of_sq_le_sq (by nlinarith) pos
    have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rlo 3
    have frame := z.radius_sq x apos
    refine ⟨z.normalized_rates x apos hd,?_,?_,by linarith,rlo⟩
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
  let T := (1/576:ℝ)
  have st : 0≤T := by norm_num [T]
  have T1 : T≤1 := by norm_num [T]
  have inside (x : ℝ) (h : x∈Icc 0 T) : x∈Icc (0:ℝ) 1 := ⟨h.1,h.2.trans T1⟩
  let g := Angle.spin δ z.root z.shape z.slope z.along z.across
  let θ := fun x : ℝ => ∫ v in (0:ℝ)..x, g v
  have cg : ContinuousOn g (uIcc 0 T) := by
    rw [uIcc_of_le st]
    exact fun x hx => (Angle.spin_continuousAt (bounds x (inside x hx)).1).continuousWithinAt
  have ct : ContinuousOn θ (Icc 0 T) := by
    simpa only [uIcc_of_le st] using intervalIntegral.continuousOn_primitive_interval
      (cg.integrableOn_compact isCompact_uIcc (μ := volume))
  have θ0 : θ 0=0 := by simp [θ]
  have endAngle : b/4608≤θ T := by
    have est := Angle.winding_on_interval st (fun x hx => bounds x (inside x hx))
    convert est using 1
    dsimp [T,δ]
    field_simp; norm_num
  let N := ⌊b/(4608*Real.pi)⌋₊
  let n := fun i : Fin N => i.val+1
  have hit (i : Fin N) : ∃ t ∈ Icc (0:ℝ) T, θ t=(n i:ℝ)*Real.pi := by
    have upper : (n i:ℝ) ≤ b/(4608*Real.pi) :=
      (show (n i:ℝ)≤N by exact_mod_cast i.isLt).trans (Nat.floor_le (by positivity))
    have R := (le_div_iff₀ (by positivity : (0:ℝ)<4608*Real.pi)).mp upper
    apply intermediate_value_Icc st ct
    refine ⟨?_,(show (n i:ℝ)*Real.pi≤b/4608 by linarith).trans endAngle⟩
    rw [θ0]
    positivity
  choose t times values using hit
  let f := Real.sqrt δ
  have fp : 0<f := Real.sqrt_pos.mpr hd
  have recipro : 1/f=Real.sqrt b := by simp [f,δ,Real.sqrt_inv]
  have lift := physical_centre_winding large
  refine ⟨fun i => t i/f,?_,?_⟩
  · intro i j h
    have eqt := (div_left_inj' fp.ne').mp h
    have eqn := (mul_left_inj' Real.pi_ne_zero).mp
      ((values i).symm.trans ((congrArg θ eqt).trans (values j)))
    have eq : n i=n j := by exact_mod_cast eqn
    exact Fin.ext (Nat.add_right_cancel eq)
  · intro i
    have rg := inside (t i) (times i)
    have point := (lift.1 (t i) rg).2
    change Angle.sn z.shape (t i)=Real.sin (θ (t i)) ∧
      Angle.cs z.shape z.slope (t i)=Real.cos (θ (t i)) at point
    rw [values i,Real.sin_nat_mul_pi,Real.cos_nat_mul_pi] at point
    have shift : 0<t i := lt_of_le_of_ne (times i).1 (fun bad => by
      have v := values i
      rw [←bad,θ0] at v
      have nn : 0<(n i:ℝ) := by dsimp [n]; positivity
      exact (mul_pos nn Real.pi_pos).ne v)
    have bound : t i/f≤Real.sqrt b/576 := by
      calc
        _ ≤ T/f := div_le_div_of_nonneg_right (times i).2 fp.le
        _ = Real.sqrt b/576 := by rw [←recipro]; dsimp [T]; ring
    have support := congrFun P.cartesianSupport_eq_solution (t i/f)
    have K : z.K (t i)=f*P.k (t i/f) := by change f*(solution 1 ![0,b,0,0] (t i/f) 0)=_; rw [←support]; rfl
    have V : z.V (t i)=δ*deriv P.k (t i/f) := by change δ*(solution 1 ![0,b,0,0] (t i/f) 1)=_; rw [←support]; rfl
    have rp : 0<z.root (t i) := lt_of_lt_of_le (by norm_num) (lift.1 (t i) rg).1
    have canon : z.shape (t i)=0 := (div_eq_zero_iff.mp point.1).resolve_right (by positivity)
    have zeroK : z.K (t i)=0 := (div_eq_zero_iff.mp canon).resolve_right rp.ne'
    rw [K] at zeroK
    refine ⟨div_pos shift fp,bound,
      (mul_eq_zero.mp zeroK).resolve_left fp.ne',?_⟩
    intro null
    have v0 : z.V (t i)=0 := by rw [V,null,mul_zero]
    have c0 := point.2
    simp only [Angle.cs,Data.slope,v0,zero_div] at c0
    exact (pow_ne_zero _ (by norm_num : (-1:ℝ)≠0)) c0.symm

/-- The initial part of the centre orbit crosses all phase levels before
    its lift reaches b/4608. The interval is shorter than any full period. -/
theorem many_simple_inflections {L b : ℝ} (P : ZeroTurnExpander L b) (large : 32≤b)
    {d : ℝ} (dp : 0<d) (px : Function.Periodic P.X d) (py : Function.Periodic P.Y d) :
    let N := ⌊b/(4608*Real.pi)⌋₊
    ∃ v : Fin N → ℝ, Function.Injective v ∧
      ∀ i, v i∈Ioo 0 d ∧ P.k (v i)=0 ∧ deriv P.k (v i)≠0 := by
  obtain ⟨v, inj, early⟩ := P.many_early_simple_inflections large
  refine ⟨v, inj, fun i => ?_⟩
  obtain ⟨pos, bound, zero, simple⟩ := early i
  exact ⟨⟨pos, bound.trans_lt (P.lower_bound_for_each_period large dp px py)⟩, zero, simple⟩

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.many_early_simple_inflections
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.many_simple_inflections

namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

/-- Arbitrarily many simple curvature zeros occur already in one primitive
    traversal. The same witness works for every positive position period. -/
theorem unbounded_primitive_inflection_counts (n : ℕ) :
    ∃ b>0, ∃ L>0, ∃ P : ZeroTurnExpander L b,
      ∀ d>0, Function.Periodic P.X d → Function.Periodic P.Y d →
      ∃ v : Fin n → ℝ, Function.Injective v ∧
        ∀ i, v i∈Ioo 0 d ∧ P.k (v i)=0 ∧ deriv P.k (v i)≠0 := by
  obtain ⟨b,high,L,lp,⟨P⟩⟩ := unbounded_closed_zero_turn_expanders
    (max 32 ((n:ℝ)*(4608*Real.pi)))
  have large : 32≤b := (le_max_left ..).trans high.le
  have cnt : n≤⌊b/(4608*Real.pi)⌋₊ := Nat.le_floor ((le_div_iff₀ (by positivity)).mpr
    ((le_max_right ..).trans high.le))
  refine ⟨b,by linarith,L,lp,P,?_⟩
  intro d dp px py
  obtain ⟨v,inj,inflect⟩ := P.many_simple_inflections large dp px py
  exact ⟨fun i => v (Fin.castLE cnt i),inj.comp (Fin.castLE_injective cnt),
    fun i => inflect (Fin.castLE cnt i)⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.unbounded_primitive_inflection_counts
