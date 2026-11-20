import SolitonClassification.FrozenEndpointError
import SolitonClassification.FrozenIntegerPolynomial

/-! Interpreting one integer polynomial certificate for the frozen field. -/
namespace ClosedSimilarity.FrozenStress.Endpoint
open IntegerPoly
structure Row where
  k : P
  v : P
  p : P
  q : P

def S : ℕ := 2^504
def T : ℕ := 2^432
def Row.dk (r : Row) := plus (scale 32 (deriv r.k)) (scale (-1) r.v)
def Row.dv (r : Row) := plus
  (scale (2*(S:ℤ)^2) (plus (scale 32 (deriv r.v)) r.p))
  (times (times r.k r.k) r.k)
def Row.dp (r : Row) := plus (scale (32*(S:ℤ)) (deriv r.p)) (times r.k r.q)
def Row.dq (r : Row) := plus (scale (32*(S:ℤ)) (deriv r.q)) (scale (-1) (times r.k r.p))

def Good (r : Row) : Prop :=
  size r.k≤8*S ∧ size r.dk*T≤S ∧ size r.dv*T≤16*S^3 ∧
  size r.dp*T≤S^2 ∧ size r.dq*T≤S^2
instance (r : Row) : Decidable (Good r) := by unfold Good; infer_instance

noncomputable def Row.atTime (r : Row) (a t : ℝ) : State := ![
  value r.k (32*(t-a))/S, value r.v (32*(t-a))/(8*S),
  value r.p (32*(t-a))/S, value r.q (32*(t-a))/S]
noncomputable def Row.speed (r : Row) (a t : ℝ) : State := ![
  32*value (deriv r.k) (32*(t-a))/S,32*value (deriv r.v) (32*(t-a))/(8*S),
  32*value (deriv r.p) (32*(t-a))/S,32*value (deriv r.q) (32*(t-a))/S]

private theorem step_deriv (p : P) (a t d : ℝ) :
    HasDerivAt (fun s => value p (32*(s-a))/d) (32*value (deriv p) (32*(t-a))/d) t := by
  have ht : HasDerivAt (fun s : ℝ => 32*(s-a)) 32 t := by
    simpa using ((hasDerivAt_id t).sub_const a).const_mul 32
  convert! ((hasDeriv p (32*(t-a))).comp t ht).div_const d using 1
  ring

theorem Row.derivative (r : Row) (a t : ℝ) :
    HasDerivAt (r.atTime a) (r.speed a t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i <;> apply step_deriv

private theorem norm_quot (p : P) (B : ℕ) (hB : 0<B) (hb : size p*T≤B)
    {x : ℝ} (hx : |x|≤1) : |value p x/(B:ℝ)|≤1/(T:ℝ) := by
  have tpos : 0<(T:ℝ) := by unfold T; positivity
  have bpos : 0<(B:ℝ) := by exact_mod_cast hB
  have co : (size p:ℝ)*(T:ℝ)≤(B:ℝ) := by exact_mod_cast hb
  rw [abs_div,abs_of_pos bpos,div_le_div_iff₀ bpos tpos,one_mul]
  exact (mul_le_mul_of_nonneg_right (norm_value p hx) tpos.le).trans co

theorem Row.cap (r : Row) (hr : Good r) (a t : ℝ) (hx : |32*(t-a)|≤1) :
    |r.atTime a t 0|≤8 := by
  have h := norm_value r.k hx
  have co : (size r.k:ℝ)≤8*S := by exact_mod_cast hr.1
  have sp : 0<(S:ℝ) := by unfold S; positivity
  change |value r.k _/(S:ℝ)|≤8
  rw [abs_div,abs_of_pos sp,div_le_iff₀ sp]
  exact h.trans co

theorem Row.defect (r : Row) (hr : Good r) (a t : ℝ) (hx : |32*(t-a)|≤1) :
    ‖r.speed a t-field (r.atTime a t)‖≤1/(T:ℝ) := by
  have hz : (S:ℝ)≠0 := by unfold S; positivity
  have sn : 0<S := by decide +kernel
  rcases hr with ⟨_,hk,hv,hp,hq⟩
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  fin_cases i
  · apply le_trans (le_of_eq ?_) (norm_quot r.dk S sn hk hx)
    change |(32*value (deriv r.k) _/S-8*(value r.v _/(8*S)))|=_
    rw [Row.dk,value_plus,value_scale,value_scale]
    simp only [Int.cast_ofNat,Int.cast_neg,Int.cast_one,neg_one_mul]
    congr 1
    ring
  · apply le_trans (le_of_eq ?_) (norm_quot r.dv (16*S^3) (by positivity) hv hx)
    change |32*value (deriv r.v) _/(8*S)-(-(value r.k _/S)^3/16-(value r.p _/S)/8)|=_
    simp only [Row.dv,value_plus,value_scale,value_times,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_ofNat,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_natCast]
    congr 1
    field_simp [hz]
    ring
  · apply le_trans (le_of_eq ?_) (norm_quot r.dp (S^2) (by positivity) hp hx)
    change |32*value (deriv r.p) _/S-(-(value r.k _/S)*(value r.q _/S))|=_
    simp only [Row.dp,value_plus,value_scale,value_times,Nat.cast_pow,Int.cast_mul,
      Int.cast_ofNat,Int.cast_natCast]
    congr 1
    field_simp [hz]
    ring
  · apply le_trans (le_of_eq ?_) (norm_quot r.dq (S^2) (by positivity) hq hx)
    change |32*value (deriv r.q) _/S-(value r.k _/S*(value r.p _/S))|=_
    simp only [Row.dq,value_plus,value_scale,value_times,Nat.cast_pow,Int.cast_mul,
      Int.cast_ofNat,Int.cast_natCast,Int.cast_neg,Int.cast_one]
    congr 1
    field_simp [hz]
    ring

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.Row.defect
