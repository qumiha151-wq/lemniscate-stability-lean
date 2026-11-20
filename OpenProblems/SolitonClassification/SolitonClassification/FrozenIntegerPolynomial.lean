import SolitonClassification.FrozenStress
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! A computable dense integer polynomial and a real interpretation for
checking uniform ODE defects on the unit interval. -/
namespace ClosedSimilarity.FrozenStress.IntegerPoly
abbrev P := List ℤ

def value : P → ℝ → ℝ
  | [], _ => 0
  | a::p, x => a+x*value p x

def plus : P → P → P
  | [],q => q
  | p,[] => p
  | a::p,b::q => (a+b)::plus p q

def scale (c : ℤ) (p : P) := p.map (c * ·)

def times : P → P → P
  | [],_ => []
  | a::p,q => plus (scale a q) (0::times p q)

def weighted (n : ℕ) : P → P
  | [] => []
  | a::p => ((n:ℤ)*a)::weighted (n+1) p

def deriv (p : P) : P := weighted 1 p.tail

def size : P → ℕ
  | [] => 0
  | a::p => a.natAbs + size p

theorem value_plus (p q : P) (t : ℝ) :
    value (plus p q) t=value p t+value q t := by
  induction p generalizing q with
  | nil => simp [plus,value]
  | cons a p ih =>
    cases q with
    | nil => simp [plus,value]
    | cons b q => simp [value,plus,ih]; ring

theorem value_scale (c : ℤ) (p : P) (t : ℝ) :
    value (scale c p) t=c*value p t := by
  induction p with
  | nil => simp [scale,value]
  | cons a p ih =>
    change ((c*a:ℤ):ℝ)+t*value (scale c p) t=_ 
    rw [ih,Int.cast_mul]
    simp only [value]
    ring

theorem value_times (p q : P) (t : ℝ) :
    value (times p q) t=value p t*value q t := by
  induction p with
  | nil => simp [times,value]
  | cons a p ih =>
    rw [times,value_plus,value_scale]
    simp only [value,Int.cast_zero,zero_add,ih]
    ring

private theorem value_weighted (n : ℕ) (p : P) (t : ℝ) :
    value (weighted n p) t=(n:ℝ)*value p t+t*value (deriv p) t := by
  induction p generalizing n with
  | nil => simp [weighted,deriv,value]
  | cons a p ih =>
    simp only [weighted,value,Int.cast_mul,Int.cast_natCast,deriv,List.tail_cons]
    rw [ih (n+1),ih 1]
    push_cast
    ring

theorem hasDeriv (p : P) (t : ℝ) :
    HasDerivAt (value p) (value (deriv p) t) t := by
  induction p with
  | nil => simpa [value,deriv,weighted] using hasDerivAt_const t (0:ℝ)
  | cons a p ih =>
    have hd := ((hasDerivAt_id t).mul ih).const_add (a:ℝ)
    change HasDerivAt (fun x => (a:ℝ)+x*value p x) (value (weighted 1 p) t) t
    simpa only [value_weighted,Nat.cast_one,one_mul,Pi.mul_apply,id_eq] using hd

theorem norm_value (p : P) {t : ℝ} (ht : |t|≤1) : |value p t|≤size p := by
  induction p with
  | nil => simp [value,size]
  | cons a p ih =>
    have hm := mul_le_mul ht ih (abs_nonneg _) (by norm_num)
    calc
      _ ≤ |(a:ℝ)|+|t*value p t| := abs_add_le _ _
      _ ≤ |(a:ℝ)|+size p := by rw [abs_mul]; linarith
      _ = _ := by simp [size,Nat.cast_natAbs]

end ClosedSimilarity.FrozenStress.IntegerPoly
