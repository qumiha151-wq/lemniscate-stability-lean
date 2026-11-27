import SolitonClassification.PrimitiveInflections
import SolitonClassification.CentreShotAlignment

noncomputable section
namespace ClosedSimilarity.ReflectedArc.ZeroTurnExpander
open GlobalSupport OuterStress Set

/-- At curvature zeros in the initial half slow-time interval the absolute
elastic force increases by at least one seventy-second of the arclength gap. -/
theorem force_gap_on_initial_zeros {L b : ℝ} (P : ZeroTurnExpander L b)
    (large : 32≤b) {s t : ℝ} (hs : 0≤s) (hst : s≤t) (ht : t≤Real.sqrt b/2)
    (ks : P.k s=0) (kt : P.k t=0) :
    (t-s)/72 ≤ |deriv (deriv P.k) t| - |deriv (deriv P.k) s| := by
  have bp : 0<b := by linarith
  let δ := b⁻¹
  let f := Real.sqrt δ
  let z := centreData b bp
  have hd : 0<δ := inv_pos.mpr bp
  have fp : 0<f := Real.sqrt_pos.mpr hd
  have rf : f*Real.sqrt b=1 := by
    dsimp [f,δ]; rw [Real.sqrt_inv,inv_mul_cancel₀ (Real.sqrt_pos.mpr bp).ne']
  have small : δ≤1/32 := by
    change b⁻¹≤_; rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) large
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  obtain ⟨hk,hv,hp,hq⟩ := init
  have mono := z.centre_alignment_monotone hd small hk hv hp hq
  have interval (r : ℝ) (lo : 0≤r) (hi : r≤Real.sqrt b/2) :
      f*r ∈ Icc (0:ℝ) (1/2) :=
    ⟨mul_nonneg fp.le lo,by nlinarith only [mul_le_mul_of_nonneg_left hi fp.le,rf]⟩
  have atZero (r : ℝ) (hr : f*r ∈ Icc (0:ℝ) (1/2)) (kr : P.k r=0) :
      z.shape (f*r)=0 ∧ z.along (f*r)=f*|deriv (deriv P.k) r| := by
    have cancel : f*r/f=r := by field_simp
    have cart := congrFun P.cartesianSupport_eq_solution r
    have K : z.K (f*r)=0 := by
      change f*(solution 1 ![0,b,0,0] (f*r/f) 0)=0
      rw [cancel,←cart]; change f*P.k r=0; rw [kr,mul_zero]
    have U : z.shape (f*r)=0 := by simp [Data.shape,K]
    have fromZero := mono (show (0:ℝ)∈Icc (0:ℝ) (1/2) by constructor <;> norm_num) hr hr.1
    have initial : z.along 0=0 := by simp [Data.along,Data.radial,hk,hp,hq]
    simp only [initial,Data.shape,hk,K,zero_div,zero_mul,mul_zero,add_zero,sub_zero] at fromZero
    have pos : 0≤z.along (f*r) := by linarith [hr.1]
    have eq := P.dilation_equation r
    rw [kr] at eq
    have p : z.p (f*r)= -f*deriv (deriv P.k) r := by
      change f*(solution 1 ![0,b,0,0] (f*r/f) 2)=_
      rw [cancel,←cart]
      change f*(-P.X r*deriv P.Y r+P.Y r*deriv P.X r)=_
      linear_combination f*eq
    have bound := (z.centre_bounds hd hk hv hp hq hr.1).2
    have ru := pow_le_pow_left₀ hr.1 hr.2 2
    have apos : 0<z.amplitude (f*r) := by nlinarith
    have amp : z.amplitude (f*r)=|z.V (f*r)| := by simp [Data.amplitude,K,Real.sqrt_sq_eq_abs]
    refine ⟨U,?_⟩
    calc
      z.along (f*r) = |z.along (f*r)| := (abs_of_nonneg pos).symm
      _ = |z.p (f*r)| := by
        simp only [Data.along,Data.radial,K,zero_pow (by decide : 2≠0),zero_div,zero_mul,zero_add,
          abs_div,abs_mul,abs_of_pos apos,←amp]
        field_simp
      _ = f*|deriv (deriv P.k) r| := by rw [p,abs_mul,abs_neg,abs_of_pos fp]
  have S := interval s hs (hst.trans ht)
  have T := interval t (hs.trans hst) ht
  obtain ⟨Us,As⟩ := atZero s S ks
  obtain ⟨Ut,At'⟩ := atZero t T kt
  have comp := mono S T (mul_le_mul_of_nonneg_left hst fp.le)
  simp only [Us,Ut,As,At',zero_mul,mul_zero,add_zero] at comp
  apply le_of_mul_le_mul_left (a:=f) _ fp
  linarith

/-- One primitive traversal realizes a linearly growing number of different
absolute force values, all at the same curvature value zero. -/
theorem many_distinct_inflection_forces {L b : ℝ} (P : ZeroTurnExpander L b) (large : 32≤b)
    {d : ℝ} (dp : 0<d) (px : Function.Periodic P.X d) (py : Function.Periodic P.Y d) :
    let N := ⌊b/(4608*Real.pi)⌋₊
    ∃ v : Fin N → ℝ, Function.Injective (fun i => |deriv (deriv P.k) (v i)|) ∧
      ∀ i, v i∈Ioo 0 d ∧ P.k (v i)=0 ∧ deriv P.k (v i)≠0 := by
  obtain ⟨v,inj,valid⟩ := P.many_early_simple_inflections large
  have short := P.lower_bound_for_each_period large dp px py
  have limit (i) : v i≤Real.sqrt b/2 := by linarith [(valid i).2.1,Real.sqrt_nonneg b]
  refine ⟨v,?_,fun i => ⟨⟨(valid i).1,(valid i).2.1.trans_lt short⟩,(valid i).2.2⟩⟩
  intro i j eq
  apply inj
  rcases le_total (v i) (v j) with ij|ji
  · have sep := P.force_gap_on_initial_zeros large (valid i).1.le ij (limit j)
      (valid i).2.2.1 (valid j).2.2.1
    linarith
  · have sep := P.force_gap_on_initial_zeros large (valid j).1.le ji (limit i)
      (valid j).2.2.1 (valid i).2.2.1
    linarith

end ClosedSimilarity.ReflectedArc.ZeroTurnExpander
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.force_gap_on_initial_zeros
#print axioms ClosedSimilarity.ReflectedArc.ZeroTurnExpander.many_distinct_inflection_forces

namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

/-- No fixed finite number of curvature-only branches can describe every
profile. The candidate functions may be chosen after seeing this profile. -/
theorem escapes_every_finite_force_law (n : ℕ) :
    ∃ b>0, ∃ L>0, ∃ P : ZeroTurnExpander L b,
      ∀ d>0, Function.Periodic P.X d → Function.Periodic P.Y d →
      ∀ G : Fin n → ℝ → ℝ, ∃ s∈Ioo 0 d, P.k s=0 ∧ deriv P.k s≠0 ∧
        ∀ i, deriv (deriv P.k) s+(P.k s)^3/2 ≠ G i (P.k s) := by
  classical
  obtain ⟨b,high,L,lp,⟨P⟩⟩ := unbounded_closed_zero_turn_expanders
    (max 32 (((n+1:ℕ):ℝ)*(4608*Real.pi)))
  have large : 32≤b := (le_max_left ..).trans high.le
  let N := ⌊b/(4608*Real.pi)⌋₊
  have count : n+1≤N :=
    Nat.le_floor ((le_div_iff₀ (by positivity)).mpr ((le_max_right ..).trans high.le))
  refine ⟨b,by linarith,L,lp,P,?_⟩
  intro d dp px py G
  obtain ⟨v,inj,info⟩ := P.many_distinct_inflection_forces large dp px py
  by_contra! bad
  have found (j : Fin N) : ∃ i, deriv (deriv P.k) (v j)=G i 0 := by
    obtain ⟨mem,zero,simple⟩ := info j
    obtain ⟨i,h⟩ := bad (v j) mem zero simple
    exact ⟨i,by simpa [zero] using h⟩
  choose branch agrees using found
  have single : Function.Injective branch := by
    intro i j eq
    exact inj (congrArg abs ((agrees i).trans ((eq ▸ agrees j).symm)))
  have card := Fintype.card_le_of_injective branch single
  simp only [Fintype.card_fin] at card
  omega

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.escapes_every_finite_force_law
