import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace SolitonClassification.Rotating.DyadicReset

/-- Horner packing with no numerical rounding. -/
def pack (b : ℤ) : List ℤ → ℤ
  | [] => 0
  | a::xs => a+b*pack b xs

def plus : List ℤ → List ℤ → List ℤ
  | [],ys => ys
  | x::xs,[] => x::xs
  | x::xs,y::ys => (x+y)::plus xs ys

def scale (c : ℤ) (xs : List ℤ) := xs.map (c*·)
def times : List ℤ → List ℤ → List ℤ
  | [],_ => []
  | x::xs,ys => plus (scale x ys) (0::times xs ys)

theorem pack_plus (b : ℤ) (xs ys : List ℤ) :
    pack b (plus xs ys)=pack b xs+pack b ys := by
  induction xs generalizing ys with
  | nil => simp [pack,plus]
  | cons x xs ih => cases ys with
    | nil => simp [pack,plus]
    | cons y ys => simp only [plus,pack,ih]; ring

theorem pack_scale (b c : ℤ) (xs : List ℤ) :
    pack b (scale c xs)=c*pack b xs := by
  induction xs with
  | nil => simp [scale,pack]
  | cons x xs ih =>
    change c*x+b*pack b (scale c xs)=c*(x+b*pack b xs)
    rw [ih]; ring

theorem pack_times (b : ℤ) (xs ys : List ℤ) :
    pack b (times xs ys)=pack b xs*pack b ys := by
  induction xs with
  | nil => simp [times,pack]
  | cons x xs ih => simp only [times,pack_plus,pack_scale,pack,ih]; ring

/-- Centered base-2k extraction. -/
def digit (k v : ℤ) := (v+k)%(2*k)-k
def extract (k : ℤ) : Nat → ℤ → List ℤ
  | 0,_ => []
  | n+1,v => digit k v :: extract k n ((v-digit k v)/(2*k))

theorem extract_pack {k : ℤ} (hk : 0<k) (xs : List ℤ)
    (cap : ∀a∈xs,-k ≤ a ∧ a < k) :
    extract k xs.length (pack (2*k) xs)=xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    let b := 2*k
    let t := pack b xs
    have ca := cap a (by simp)
    have hb : 0<b := by dsimp [b]; omega
    have mod_eq : (a+k)%b=a+k := Int.emod_eq_of_lt (by omega) (by dsimp [b]; omega)
    have one : digit k (a+b*t)=a := by
      change ((a+b*t+k)%b)-k=a
      rw [show a+b*t+k=(a+k)+b*t by ring,Int.add_mul_emod_self_left,mod_eq]; ring
    have next : (a+b*t-a)/b=t := by
      rw [show a+b*t-a=t*b by ring,Int.mul_ediv_cancel _ hb.ne']
    change digit k (a+b*t)::extract k xs.length ((a+b*t-digit k (a+b*t))/b) = a::xs
    rw [one,next,ih (fun v hv => cap v (List.mem_cons_of_mem a hv))]

def l1 (xs : List ℤ) : ℕ := (xs.map Int.natAbs).sum

/-- The coefficient sum read from a packed polynomial is exact whenever
the arithmetic coefficient bounds lie in the centered digit range. -/
theorem packed_l1 {k : ℤ} (hk : 0<k) (xs : List ℤ)
    (cap : ∀a∈xs,-k ≤ a ∧ a < k) :
    l1 (extract k xs.length (pack (2*k) xs))=l1 xs := by rw [extract_pack hk xs cap]

end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.packed_l1
#print axioms SolitonClassification.Rotating.DyadicReset.pack_times
