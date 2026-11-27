import SolitonClassification.Rotating.ResetPolynomial

namespace SolitonClassification.Rotating.DyadicReset
inductive Term where
  | atom (p : List ℤ)
  | constant (c : ℤ)
  | add (a b : Term)
  | times (a b : Term)
  | scale (c : ℤ) (a : Term)

namespace Term
instance : Add Term := ⟨.add⟩
instance : Mul Term := ⟨.times⟩
instance : Neg Term := ⟨.scale (-1)⟩
instance : Sub Term := ⟨fun a b => .add a (.scale (-1) b)⟩

def coeffs : Term → List ℤ
  | .atom p => p
  | .constant c => [c]
  | .add a b => plus a.coeffs b.coeffs
  | .times a b => DyadicReset.times a.coeffs b.coeffs
  | .scale c a => DyadicReset.scale c a.coeffs

def packed (x : ℤ) : Term → ℤ
  | .atom p => pack x p
  | .constant c => c
  | .add a b => a.packed x+b.packed x
  | .times a b => a.packed x*b.packed x
  | .scale c a => c*a.packed x

noncomputable def realValue (x : ℝ) : Term → ℝ
  | .atom p => eval x p
  | .constant c => c
  | .add a b => a.realValue x+b.realValue x
  | .times a b => a.realValue x*b.realValue x
  | .scale c a => c*a.realValue x

def degree : Term → ℕ
  | .atom p => p.length-1
  | .constant _ => 0
  | .add a b => max a.degree b.degree
  | .times a b => a.degree+b.degree
  | .scale _ a => a.degree

def mass : Term → ℕ
  | .atom p => l1 p
  | .constant c => c.natAbs
  | .add a b => a.mass+b.mass
  | .times a b => a.mass*b.mass
  | .scale c a => c.natAbs*a.mass

theorem pack_coeffs (e : Term) (b : ℤ) : pack b e.coeffs=e.packed b := by
  induction e <;> simp_all [coeffs,packed,pack,pack_plus,pack_scale,pack_times]

theorem eval_coeffs (e : Term) (t : ℝ) : eval t e.coeffs=e.realValue t := by
  induction e <;> simp_all [coeffs,realValue,eval,eval_plus,eval_scale,eval_times]

theorem length_coeffs (e : Term) : e.coeffs.length≤e.degree+1 := by
  induction e with
  | atom p => simp only [coeffs,degree]; omega
  | constant c => simp [coeffs,degree]
  | add a b ha hb => simp only [coeffs,degree,length_plus]; omega
  | times a b ha hb =>
    apply (length_times _ _).trans
    change _≤a.degree+b.degree+1
    omega
  | scale c a ha => simpa [coeffs,degree,DyadicReset.scale] using ha

theorem mass_coeffs (e : Term) : l1 e.coeffs≤e.mass := by
  induction e with
  | atom p => exact le_rfl
  | constant c => simp [coeffs,mass]
  | add a b ha hb => exact (l1_plus _ _).trans (Nat.add_le_add ha hb)
  | times a b ha hb => exact (l1_times _ _).trans (Nat.mul_le_mul ha hb)
  | scale c a ha => simp only [coeffs,mass,l1_scale]; exact Nat.mul_le_mul_left _ ha

theorem bound (e : Term) {k : ℤ} (hk : 0<k) {n : Nat} (deg : e.degree<n)
    (cap : (e.mass:ℤ)<k) {t : ℝ} (ht : |t|≤1) :
    |e.realValue t|≤(l1 (extract k n (e.packed (2*k))):ℝ) := by
  rw [←eval_coeffs,←pack_coeffs]
  apply abs_eval_of_packed hk e.coeffs n (e.length_coeffs.trans (by omega)) _ ht
  exact (by exact_mod_cast e.mass_coeffs : (l1 e.coeffs:ℤ)≤e.mass).trans_lt cap

end Term

def differential (p : List ℤ) := (p.drop 1).zipIdx.map (fun (c,j) => ((j+1:Nat):ℤ)*c)

def form (p : ℕ → List ℤ) (d : ℤ) (i : ℕ) : Term := Id.run do
  let x := fun j => Term.atom (p j)
  let k:=x 0
  let u:=x 1
  let z:=x 2
  let q:=x 3
  let b:=x 4
  if i<6 then
    return (#[.scale (128*d^2) u, -(k*k*k)-.scale (2*d^2) z-.scale (2*d) (b*q),
      .scale (-16*d) (k*q),.constant (16*d^3)+.scale (16*d) (k*z),.constant 0,.scale (16*d^2) k] : Array Term)[i]?.getD (.constant 0)
  let j := (i-6)/5
  let s := 6+5*j
  let sk := x s
  let su := x (s+1)
  let sp := x (s+2)
  let sq := x (s+3)
  return (#[.scale (128*d^2) su,.scale (-3) (k*k*sk)-.scale (2*d^2) sp-.scale (2*d) (b*sq)-
    (if j=4 then .scale (2*d^2) q else .constant 0),
    .scale (-16*d) (q*sk+k*sq),.scale (16*d) (z*sk+k*sp),.scale (16*d^2) sk] : Array Term)[(i-6)%5]?.getD (.constant 0)

def defectTerm (p : Nat → List ℤ) (d hn hd : ℤ) (i : ℕ) :=
    (Term.scale (16*hd*d^2) (.atom (differential (p i)))) - (Term.scale hn (form p d i))

end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.Term.bound
