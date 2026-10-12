import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.Range

/-!
Executable exact rational definitions of the nine cosine rows (3.12).
These are the expressions themselves, not decimal values copied from a table.
No floating point operations or native-decide proofs are used.
The analytic enclosure of the Fourier coefficients is a separate obligation.
-/
namespace Lemniscate.CoarseArithmetic

def qlo : ℚ := 4321/100000
def qhi : ℚ := 2161/50000
def rlo : ℚ := 7177/10000
def rhi : ℚ := 3589/5000
def qb : ℚ := 11/250
def a : ℚ := 1/10
def H : ℚ := 8*rhi/(1-qb^2)
def C : ℚ := 105*rhi*H

def sumTo (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range n).map f).sum

def moment (p : ℕ) (z : ℚ) : ℚ :=
  match p with
  | 0 => 1/(1-z)
  | 1 => z/(1-z)^2
  | 2 => z*(1+z)/(1-z)^3
  | 3 => z*(1+4*z+z^2)/(1-z)^4
  | 4 => z*(1+11*z+11*z^2+z^3)/(1-z)^5
  | 5 => z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6
  | 6 => z*(1+57*z+302*z^2+302*z^3+57*z^4+z^5)/(1-z)^7
  | _ => 0

def tail1 (z : ℚ) (L : ℕ) : ℚ :=
  z^L*((L:ℚ)*moment 0 z+moment 1 z)
def tail2 (z : ℚ) (L : ℕ) : ℚ :=
  z^L*((L:ℚ)^2*moment 0 z+2*(L:ℚ)*moment 1 z+moment 2 z)
def tail3 (z : ℚ) (L : ℕ) : ℚ :=
  z^L*((L:ℚ)^3*moment 0 z+3*(L:ℚ)^2*moment 1 z+
    3*(L:ℚ)*moment 2 z+moment 3 z)

def hLowerPositive (j : ℕ) : ℚ := 8*rlo*(j:ℚ)*qlo^j/(1-qlo^(2*j))
def hUpperPositive (j : ℕ) : ℚ := 8*rhi*(j:ℚ)*qhi^j/(1-qhi^(2*j))
def hLower (j : ℕ) : ℚ :=
  if j = 0 then 1-2*sumTo 4 (fun k => hUpperPositive (k+1))-
    16*rhi*tail1 qhi 5/(1-qhi^2)
  else hLowerPositive j
def hUpper (j : ℕ) : ℚ :=
  if j = 0 then 1-2*sumTo 4 (fun k => hLowerPositive (k+1))
  else hUpperPositive j

structure Interval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def point (q : ℚ) : Interval := ⟨q,q⟩
def add (x y : Interval) : Interval := ⟨x.lo+y.lo,x.hi+y.hi⟩
def mul (x y : Interval) : Interval :=
  ⟨min (min (x.lo*y.lo) (x.lo*y.hi)) (min (x.hi*y.lo) (x.hi*y.hi)),
   max (max (x.lo*y.lo) (x.lo*y.hi)) (max (x.hi*y.lo) (x.hi*y.hi))⟩
def scale (x : Interval) (q : ℚ) : Interval := mul x (point q)
def absUpper (x : Interval) : ℚ := max |x.lo| |x.hi|
def hInterval (j : ℕ) : Interval := ⟨hLower j,hUpper j⟩

def cosineEntry (j k : ℕ) : Interval :=
  let n : ℚ := 2*(j:ℚ)
  let m : ℚ := 2*(k:ℚ)
  if j = 0 ∧ k = 0 then point (-42)
  else if j = 0 ∨ k = 0 then
    scale (mul (mul ⟨rlo,rhi⟩ (hInterval (j+k))) ⟨707/500,283/200⟩)
      (-(15/4:ℚ)*(n+m)^2)
  else
    let nonconstant := mul ⟨rlo,rhi⟩
      (add (scale (hInterval (j-k+(k-j))) (45*n*m-(15/4:ℚ)*(n-m)^2))
           (scale (hInterval (j+k)) (-45*n*m-(15/4:ℚ)*(n+m)^2)))
    if j = k then add nonconstant ⟨-4*rhi^2*n^4-42,-4*rlo^2*n^4-42⟩
    else nonconstant

def weight (j : ℕ) : ℚ :=
  match j with
  | 0 => 1/9
  | 1 => 1
  | 2 => 11/50
  | j+3 => (29/1000:ℚ)*a^j

def finiteRow (j : ℕ) : ℚ :=
  let n : ℚ := 2*(j:ℚ)
  (cosineEntry j j).hi +
  sumTo 20 (fun k => if k = j then 0 else absUpper (cosineEntry j k)*weight k/weight j) +
  C*weight 3*(a^j/a^3)/weight j*
    (n^2*tail1 (qb*a) (20-j)+2*n*tail2 (qb*a) (20-j)+tail3 (qb*a) (20-j))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cosine_rows : ∀ j : Fin 9, finiteRow j.val < -(21/4:ℚ) := by decide +kernel

theorem cosine_row_zero : finiteRow 0 < -(21/4:ℚ) := cosine_rows ⟨0, by decide⟩

end Lemniscate.CoarseArithmetic
