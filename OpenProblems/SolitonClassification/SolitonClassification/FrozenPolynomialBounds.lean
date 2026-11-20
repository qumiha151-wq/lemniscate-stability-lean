import SolitonClassification.FrozenIntegerPolynomial

/-! Cheap degree and coefficient bounds for integer polynomial expressions. -/
namespace ClosedSimilarity.FrozenStress.IntegerPoly

theorem size_plus (p q : P) : size (plus p q)≤size p+size q := by
  induction p generalizing q with
  | nil => simp [plus,size]
  | cons a p ih =>
    cases q with
    | nil => simp [plus,size]
    | cons b q =>
      simp only [plus,size]
      have ha := Int.natAbs_add_le a b
      have hb := ih q
      omega

theorem length_plus (p q : P) : (plus p q).length≤max p.length q.length := by
  induction p generalizing q with
  | nil => simp [plus]
  | cons a p ih =>
    cases q with
    | nil => simp [plus]
    | cons b q =>
      simp only [plus,List.length_cons]
      have h := ih q
      omega

theorem size_scale (c : ℤ) (p : P) : size (scale c p)=c.natAbs*size p := by
  induction p with
  | nil => simp [scale,size]
  | cons a p ih =>
    change (c*a).natAbs+size (scale c p)=c.natAbs*(a.natAbs+size p)
    rw [ih,Int.natAbs_mul,Nat.mul_add]

theorem length_scale (c : ℤ) (p : P) : (scale c p).length=p.length := by simp [scale]

theorem size_times (p q : P) : size (times p q)≤size p*size q := by
  induction p with
  | nil => simp [times,size]
  | cons a p ih =>
    apply (size_plus (scale a q) (0::times p q)).trans
    simpa [size,size_scale,Nat.add_mul] using Nat.add_le_add_left ih (a.natAbs*size q)

theorem length_times (p q : P) : (times p q).length≤p.length+q.length := by
  induction p with
  | nil => simp [times]
  | cons a p ih =>
    apply (length_plus (scale a q) (0::times p q)).trans
    simp only [length_scale,List.length_cons]
    omega

inductive Formula where
  | atom (p : P)
  | add (x y : Formula)
  | mul (x y : Formula)
  | smul (c : ℤ) (x : Formula)

def Formula.polynomial : Formula → P
  | .atom p => p
  | .add x y => plus x.polynomial y.polynomial
  | .mul x y => times x.polynomial y.polynomial
  | .smul c x => scale c x.polynomial

def Formula.magnitude : Formula → ℕ
  | .atom p => size p
  | .add x y => x.magnitude+y.magnitude
  | .mul x y => x.magnitude*y.magnitude
  | .smul c x => c.natAbs*x.magnitude

def Formula.width : Formula → ℕ
  | .atom p => p.length
  | .add x y => max x.width y.width
  | .mul x y => x.width+y.width
  | .smul _ x => x.width

theorem Formula.bounds (e : Formula) :
    size e.polynomial≤e.magnitude ∧ e.polynomial.length≤e.width := by
  induction e with
  | atom p => exact ⟨le_rfl,le_rfl⟩
  | add x y ix iy => exact ⟨(size_plus _ _).trans (Nat.add_le_add ix.1 iy.1),
      (length_plus _ _).trans (max_le_max ix.2 iy.2)⟩
  | mul x y ix iy => exact ⟨(size_times _ _).trans (Nat.mul_le_mul ix.1 iy.1),
      (length_times _ _).trans (Nat.add_le_add ix.2 iy.2)⟩
  | smul c x ih =>
    exact ⟨(size_scale _ _).le.trans (Nat.mul_le_mul_left c.natAbs ih.1),
      (length_scale _ _).le.trans ih.2⟩

end ClosedSimilarity.FrozenStress.IntegerPoly
