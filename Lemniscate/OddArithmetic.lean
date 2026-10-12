import Lemniscate.CoarseArithmetic
import Mathlib.Data.Nat.Choose.Basic

/-! The 84 odd-sector Bernstein comparisons and 12 zero-parameter rows.
All entries are evaluated from the paper's rational formulas, including the
analytic upper bound for columns beyond 25. The infinite-tail interpretation
of this rational bound is a separate theorem, not assumed by these checks.
-/
namespace Lemniscate.OddArithmetic
open CoarseArithmetic

abbrev Poly := List ℚ
def coeff (p : Poly) (j : ℕ) : ℚ := p[j]?.getD 0
def polyAdd (p q : Poly) : Poly :=
  (List.range (max p.length q.length)).map (fun j => coeff p j+coeff q j)
def polyScale (p : Poly) (t : ℚ) : Poly := p.map (fun x => t*x)
def polyMul (p q : Poly) : Poly :=
  (List.range (p.length+q.length-1)).map
    (fun j => sumTo (j+1) (fun k => coeff p k*coeff q (j-k)))
def polyEval (p : Poly) (t : ℚ) : ℚ := sumTo p.length (fun j => coeff p j*t^j)

def weight (n : ℤ) : Poly :=
  if n = 1 then [1]
  else if n = -1 then [1,-8/5,4/5]
  else if n = 3 then [1/2,-1/2,3/25]
  else if n = -3 then [1/2,0,3/10]
  else
    let base : Poly := if 0 < n then [2/25,-3/25,2/25] else [2/25,0,1/20]
    if n.natAbs = 5 then base
    else polyScale base ((3/25:ℚ)*a^((n.natAbs-7)/2))

def absoluteEntryPolynomial (n m : ℤ) : Poly :=
  let nr : ℚ := n
  let mr : ℚ := m
  let p : Poly := [45*nr*mr-(15/4:ℚ)*(nr-mr)^2,45*(nr+mr),45]
  let p0 := polyEval p 0
  let p1 := polyEval p (1/2)
  let majorant := if 0 ≤ min p0 p1 then p
    else if max p0 p1 ≤ 0 then polyScale p (-1)
    else p.map abs
  polyScale majorant (rhi*hUpper ((n-m).natAbs/2))

def omittedOneSign (n sign : ℤ) : ℚ :=
  let v : ℚ := (n.natAbs:ℚ)+1/2
  let L : ℕ := ((27-sign*n)/2).toNat
  let exponent : ℤ := (sign*n-7)/2
  45*rhi*H*(3/250:ℚ)*a^exponent*
    (v^2*tail1 (qb*a) L+2*v*tail2 (qb*a) L+tail3 (qb*a) L/3)

def omitted (n : ℤ) : ℚ := omittedOneSign n (-1)+omittedOneSign n 1

def oddIndices : List ℤ := (List.range 26).map (fun j => -25+2*(j:ℤ))

def rowPolynomial (n : ℤ) : Poly :=
  let k2 := polyMul [(n:ℚ),1] [(n:ℚ),1]
  let negativeDiagonal := polyAdd
    (polyAdd (polyScale (polyMul k2 k2) (4*rlo^2))
      (polyScale k2 (-45*rhi*hUpper 0))) [41]
  let initial := polyMul negativeDiagonal (weight n)
  let withHead := oddIndices.foldl
    (fun p m => if m = n then p
      else polyAdd p (polyScale (polyMul (absoluteEntryPolynomial n m) (weight m)) (-1)))
    initial
  polyAdd withHead [-omitted n]

def bernsteinSix (p : Poly) (k : ℕ) : ℚ :=
  sumTo (k+1) (fun j => coeff p j*(k.choose j:ℚ)/(2^j*((6:ℕ).choose j:ℚ)))

def lowIndex (j : Fin 12) : ℤ := -11+2*(j.val:ℤ)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_odd_bernstein_comparisons :
    ∀ i : Fin 12, ∀ k : Fin 7, (1/2:ℚ) < bernsteinSix (rowPolynomial (lowIndex i)) k.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_odd_zero_comparisons :
    ∀ i : Fin 12, (5:ℚ) < coeff (rowPolynomial (lowIndex i)) 0 / coeff (weight (lowIndex i)) 0 := by
  decide +kernel

end Lemniscate.OddArithmetic
