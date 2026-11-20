import SolitonClassification.FrozenIntegerPolynomial

/-! Signed Kronecker substitution for exact integer ODE residuals. Under the
    explicit bound on coefficient magnitudes there are no ambiguous carries.
    Multiplication of packed integers is ordinary kernel integer arithmetic. -/
namespace ClosedSimilarity.FrozenStress.IntegerPoly

def pack (B : ℤ) : P → ℤ
  | [] => 0
  | c::p => c+B*pack B p

def digitsSize (half : ℕ) : ℕ → ℤ → ℕ
  | 0,_ => 0
  | n+1,z =>
    let h : ℤ := half
    let B := 2*h
    let shifted := z+h
    (shifted % B-h).natAbs + digitsSize half n (shifted / B)

theorem pack_plus (B : ℤ) (p q : P) : pack B (plus p q)=pack B p+pack B q := by
  induction p generalizing q with
  | nil => simp [plus,pack]
  | cons c p ih =>
    cases q with
    | nil => simp [plus,pack]
    | cons d q => simp [plus,pack,ih]; ring

theorem pack_scale (B c : ℤ) (p : P) : pack B (scale c p)=c*pack B p := by
  induction p with
  | nil => simp [scale,pack]
  | cons a p ih =>
    change c*a+B*pack B (scale c p)=c*(a+B*pack B p)
    rw [ih]; ring

theorem pack_times (B : ℤ) (p q : P) : pack B (times p q)=pack B p*pack B q := by
  induction p with
  | nil => simp [times,pack]
  | cons a p ih =>
    rw [times,pack_plus,pack_scale]
    simp only [pack,zero_add,ih]
    ring

private theorem read_digit {half : ℕ} {a z : ℤ} (small : a.natAbs < half) :
    let h : ℤ := half
    let B := 2*h
    ((a+B*z+h)%B-h = a) ∧ ((a+B*z+h)/B = z) := by
  dsimp only
  have h : |a| < (half:ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast small
  obtain ⟨al,ar⟩ := abs_lt.mp h
  have sign : 0 ≤ a+(half:ℤ) := by omega
  have hi : a+(half:ℤ) < 2*(half:ℤ) := by omega
  have bp : 0 < 2*(half:ℤ) := by omega
  rw [show a+2*(half:ℤ)*z+half = (a+half)+(2*(half:ℤ))*z by ring]
  constructor
  · rw [Int.add_mul_emod_self_left,Int.emod_eq_of_lt sign hi]
    omega
  · rw [Int.add_mul_ediv_left _ _ bp.ne',Int.ediv_eq_zero_of_lt sign hi,zero_add]

private theorem digitsSize_zero {half : ℕ} (h : 0 < half) (n : ℕ) :
    digitsSize half n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have digit := read_digit (a := 0) (z := 0) (half := half) (by simpa using h)
    simp only [mul_zero,zero_add] at digit
    simp [digitsSize,digit.1,digit.2,ih]

/-- Reading n balanced digits of a polynomial packed at base 2*half exactly
    recovers the sum of its absolute coefficients, including any zero padding. -/
theorem digitsSize_pack {half : ℕ} (p : P) (n : ℕ) (hh : size p < half)
    (hn : p.length ≤ n) : digitsSize half n (pack (2*(half:ℤ)) p)=size p := by
  induction p generalizing n with
  | nil => exact digitsSize_zero hh n
  | cons a p ih =>
    cases n with
    | zero => simp at hn
    | succ n =>
      change a.natAbs + size p < half at hh
      obtain ⟨digit,tail⟩ := read_digit (z := pack (2*(half:ℤ)) p) (a := a) (half := half) (by omega)
      change ((a+2*(half:ℤ)*pack (2*(half:ℤ)) p+half)%(2*(half:ℤ))-half).natAbs +
        digitsSize half n ((a+2*(half:ℤ)*pack (2*(half:ℤ)) p+half)/(2*(half:ℤ))) = _
      rw [digit,tail,ih n (by omega) (by simpa using hn)]
      rfl

end ClosedSimilarity.FrozenStress.IntegerPoly
#print axioms ClosedSimilarity.FrozenStress.IntegerPoly.digitsSize_pack
