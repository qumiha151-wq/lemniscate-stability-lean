import SolitonClassification.Rotating.DyadicResetDigits
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum

namespace SolitonClassification.Rotating.DyadicReset
noncomputable section
def eval (t : ℝ) : List ℤ → ℝ
  | [] => 0
  | c::p => (c:ℝ)+t*eval t p

theorem eval_plus (t : ℝ) (p q : List ℤ) : eval t (plus p q)=eval t p+eval t q := by
  induction p generalizing q with
  | nil => simp [plus,eval]
  | cons a p ih => cases q with
    | nil => simp [plus,eval]
    | cons b q => simp only [plus,eval,ih,Int.cast_add]; ring

theorem eval_scale (t : ℝ) (c : ℤ) (p : List ℤ) : eval t (scale c p)=(c:ℝ)*eval t p := by
  induction p with
  | nil => simp [scale,eval]
  | cons a p ih =>
    change (↑(c*a):ℝ)+t*eval t (scale c p)=c*((a:ℝ)+t*eval t p)
    rw [ih,Int.cast_mul]; ring

theorem eval_times (t : ℝ) (p q : List ℤ) : eval t (times p q)=eval t p*eval t q := by
  induction p with
  | nil => simp [times,eval]
  | cons a p ih => simp only [times,eval_plus,eval_scale,eval,ih,Int.cast_zero]; ring

@[simp] theorem l1_cons (a : ℤ) (p : List ℤ) : l1 (a::p)=a.natAbs+l1 p := by simp [l1]
@[simp] theorem l1_nil : l1 []=0 := rfl

theorem l1_plus (p q : List ℤ) : l1 (plus p q)≤l1 p+l1 q := by
  induction p generalizing q with
  | nil => simp [plus]
  | cons a p ih => cases q with
    | nil => simp [plus]
    | cons b q =>
      simp only [plus,l1_cons]
      have h := Int.natAbs_add_le a b
      have g := ih q
      omega

theorem l1_scale (a : ℤ) (p : List ℤ) : l1 (scale a p)=a.natAbs*l1 p := by
  induction p with
  | nil => simp [scale]
  | cons b p ih => change l1 (a*b::scale a p)=_; rw [l1_cons,ih,l1_cons,Int.natAbs_mul,Nat.mul_add]

theorem l1_times (p q : List ℤ) : l1 (times p q)≤l1 p*l1 q := by
  induction p with
  | nil => simp [times]
  | cons a p ih =>
    apply (l1_plus _ _).trans
    simpa [l1_scale,Nat.add_mul] using Nat.add_le_add_left ih (a.natAbs*l1 q)

theorem length_plus (p q : List ℤ) : (plus p q).length=max p.length q.length := by
  induction p generalizing q with
  | nil => simp [plus]
  | cons a p ih => cases q with
    | nil => simp [plus]
    | cons b q => simp [plus,ih]

theorem length_times (p q : List ℤ) : (times p q).length≤p.length+(q.length-1) := by
  induction p with
  | nil => simp [times]
  | cons a p ih =>
    simp only [times,length_plus,List.length_cons,scale,List.length_map]
    omega

theorem abs_eval (p : List ℤ) {t : ℝ} (ht : |t|≤1) : |eval t p|≤(l1 p:ℝ) := by
  induction p with
  | nil => simp [eval]
  | cons a p ih =>
    rw [eval,l1_cons,Nat.cast_add,Nat.cast_natAbs,Int.cast_abs]
    apply (abs_add_le ..).trans (add_le_add_right ?_ _)
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans (by simpa using ih)

theorem l1_extract_pad {k : ℤ} (hk : 0<k) (p : List ℤ) (n : Nat) (hlen : p.length≤n)
    (cap : (l1 p:ℤ)<k) : l1 (extract k n (pack (2*k) p))=l1 p := by
  let padded := p ++ List.replicate (n-p.length) (0:ℤ)
  have lpad : ∀j, l1 (p++List.replicate j (0:ℤ))=l1 p := by
    intro j; simp [l1]
  have packzero (j : ℕ) : pack (2*k) (List.replicate j 0)=0 := by
    induction j with | zero => rfl | succ j ih => simp [List.replicate_succ,pack,ih]
  have eq (q : List ℤ) (j : ℕ) : pack (2*k) (q++List.replicate j 0)=pack (2*k) q := by
    induction q with | nil => simpa [pack] using packzero j | cons a q ih => simp [pack,ih]
  have bound (q : List ℤ) (a : ℤ) (h : a∈q) : a.natAbs≤l1 q := by
    induction q with
    | nil => simp at h
    | cons b q ih =>
      simp only [l1_cons]
      rcases List.mem_cons.mp h with rfl | hh
      · omega
      · exact (ih hh).trans (Nat.le_add_left ..)
  have caps (a : ℤ) (ha : a∈padded) : -k≤a ∧ a<k := by
    have bd := bound padded a ha
    rw [show l1 padded=l1 p from lpad _] at bd
    omega
  have length : padded.length=n := by simp only [padded,List.length_append,List.length_replicate]; omega
  have res := congrArg l1 (extract_pack hk padded caps)
  dsimp only [padded] at res length
  rw [length,eq,lpad] at res
  exact res

/-- The real value of the actual polynomial is controlled by its packed
residual when the no-carry and degree certificates hold. -/
theorem abs_eval_of_packed {k : ℤ} (hk : 0<k) (p : List ℤ) (n : Nat) (hlen : p.length≤n)
    (cap : (l1 p:ℤ)<k) {t : ℝ} (ht : |t|≤1) :
    |eval t p|≤ (l1 (extract k n (pack (2*k) p)):ℝ) := by
  rw [l1_extract_pad hk p n hlen cap]; exact abs_eval p ht

end
end SolitonClassification.Rotating.DyadicReset
#print axioms SolitonClassification.Rotating.DyadicReset.abs_eval_of_packed
