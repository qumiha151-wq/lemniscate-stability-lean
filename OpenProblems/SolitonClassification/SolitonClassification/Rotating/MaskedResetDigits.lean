import SolitonClassification.Rotating.DyadicResetDigits
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum

namespace SolitonClassification.Rotating.DyadicReset
def digits (w : ℕ) : ℕ → ℕ → List ℕ
  | 0,_=>[]
  | n+1,x=>x%2^w :: digits w n (x>>>w)

private theorem digits_len (w n x : ℕ) : (digits w n x).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [digits,ih]

theorem mask_bounds {w U M T n : ℕ} (hm : U &&& M=U)
    (hT : ∀a∈digits w n M,a≤T) : ∀a∈digits w n U,a≤T := by
  induction n generalizing U M with
  | zero => simp [digits]
  | succ n ih =>
    have modu := congrArg (fun k=>k%2^w) hm
    change (U &&& M)%2^w=U%2^w at modu
    rw [Nat.and_mod_two_pow] at modu
    have sh := congrArg (fun k=>k>>>w) hm
    change (U &&& M)>>>w=U>>>w at sh
    rw [Nat.shiftRight_and_distrib] at sh
    intro a ha
    rcases List.mem_cons.mp ha with ea|ea
    · subst a
      exact (modu.symm.le.trans Nat.and_le_right).trans (hT _ (by simp [digits]))
    · exact ih sh (fun x hx => hT x (List.mem_cons_of_mem _ hx)) a ea

theorem pack_digits (w n x : Nat) (bound : x<(2^w)^n) :
    pack (2^w) ((digits w n x).map Nat.cast)=(x:ℤ) := by
  induction n generalizing x with
  | zero =>
    simp only [pow_zero] at bound
    have zx : x=0 := by omega
    subst x; rfl
  | succ n ih =>
    have bp : 0<2^w := Nat.two_pow_pos w
    have sub : x>>>w < (2^w)^n := by
      rw [Nat.shiftRight_eq_div_pow,Nat.div_lt_iff_lt_mul bp,pow_succ] at *
      exact bound
    change (↑(x%2^w):ℤ)+(2^w:ℤ)*pack (2^w) ((digits w n (x>>>w)).map Nat.cast)=(x:ℤ)
    rw [ih _ sub,Nat.shiftRight_eq_div_pow]
    exact_mod_cast Nat.mod_add_div x (2^w)

private theorem pack_translate (b t : ℤ) (l : List ℕ) :
    pack b (l.map fun (j : ℕ)=>(j:ℤ)-t)=
      pack b (l.map Nat.cast)-t*pack b (List.replicate l.length (1:ℤ)) := by
  induction l with
  | nil => simp [pack]
  | cons v l ih => simp only [List.map_cons,List.length_cons,List.replicate_succ,pack,ih]; ring

private theorem translated_l1 (L : Nat) (l : List ℕ) (cl : ∀i∈l,i≤2*L) :
    l1 (l.map fun (i : ℕ)=>(i:ℤ)-(L:ℤ))≤l.length*L := by
  induction l with
  | nil => simp [l1]
  | cons i l ih =>
    have c := cl i (by simp)
    have h : ((i:ℤ)-(L:ℤ)).natAbs≤L := by omega
    have d := ih (fun a ha => cl a (List.mem_cons_of_mem _ ha))
    simpa [l1,Nat.succ_mul,Nat.add_comm] using Nat.add_le_add h d

/-- A single parallel bit-mask test controls the signed coefficient sum
of a high-degree packed polynomial. The shared mask's digits are
certified once. No per-cell digit loop is needed in the numerical check. -/
theorem mask_l1 {w n U M L : Nat} {k v : ℤ} (hk : 0<k) (base : 2*k=(2^w:ℤ))
    (small : (L:ℤ)<k) (high : U<(2^w)^n)
    (hb : v=(U:ℤ)-L*pack (2*k) (List.replicate n (1:ℤ)))
    (bits : U &&& M=U) (mask : ∀a∈digits w n M,a≤2*L) :
    l1 (extract k n v)≤n*L := by
  let l := digits w n U
  have len : l.length=n := digits_len .. 
  have cap : ∀a∈l,a≤2*L := mask_bounds bits mask
  let s := l.map fun (a : ℕ)=>(a:ℤ)-(L:ℤ)
  have eq : pack (2*k) s=v := by
    rw [hb,pack_translate,len,base]
    have e := pack_digits w n U high
    change pack (2^w) (l.map Nat.cast) - ↑L * _ = _
    rw [e]
  have cap2 : ∀a∈s,-k≤a ∧ a<k := by
    intro a ha
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp ha
    have := cap b hb
    omega
  have sz : s.length=n := by simp [s,len]
  rw [← eq,← sz,extract_pack hk s cap2]
  simpa only [s,List.length_map] using translated_l1 L l cap
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.mask_l1
