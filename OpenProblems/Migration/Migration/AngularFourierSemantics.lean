import Migration.AngularFourierResidual
import Migration.AngularSlabConstants
import Migration.AngularFirstVelocity

noncomputable section
open Set
namespace MigrationGeometry.AngularGauge.FourierExample

variable {B : Type*} [CommRing B]

/-- Evaluation at any system of weights on joint frequency / time degree. -/
def value (ω : Int × Nat → B) : Poly → B
  | [] => 0
  | (k,a)::t => (a:B)*ω k+value ω t

private theorem append_value (ω : Int × Nat → B) (p q : Poly) :
    value ω (p++q)=value ω p+value ω q := by
  induction p with
  | nil => simp [value]
  | cons h p ih => rcases h with ⟨k,b⟩; simp [value,ih,add_assoc]

theorem merge_value (ω : Int × Nat → B) (m : Nat) (p q : Poly) :
    value ω (merge m p q)=value ω p+value ω q := by
  induction m generalizing p q with
  | zero => exact append_value ω p q
  | succ m ih =>
    cases p with
    | nil => simp [merge,value]
    | cons h p =>
      cases q with
      | nil => simp [merge,value]
      | cons g q =>
        rcases h with ⟨i,a⟩; rcases g with ⟨j,b⟩
        by_cases eq : i=j
        · subst j
          simp [merge,value,ih,add_mul]; ring
        · simp only [merge,if_neg eq]
          split <;> simp [value,ih] <;> ring

theorem plus_value (ω : Int × Nat → B) (p q : Poly) :
    value ω (plus p q)=value ω p+value ω q := merge_value ω _ p q

theorem scale_value (ω : Int × Nat → B) (a : Int) (p : Poly) :
    value ω (scale a p)=(a:B)*value ω p := by
  induction p with
  | nil => simp [value,scale]
  | cons h p ih =>
    rcases h with ⟨i,b⟩
    change (↑(a*b):B)*ω i+value ω (scale a p)=(a:B)*((b:B)*ω i+value ω p)
    rw [ih,Int.cast_mul]; ring

private theorem shift_value (ω : Int × Nat → B)
    (hom : ∀i j : Int × Nat,ω (i.1+j.1,i.2+j.2)=ω i*ω j)
    (k : Int × Nat) (a : Int) (q : Poly) :
    value ω (q.map fun (l,b) => ((k.1+l.1,k.2+l.2),a*b))=
      (a:B)*ω k*value ω q := by
  induction q with
  | nil => simp [value]
  | cons h q ih =>
    rcases h with ⟨l,b⟩
    simp only [List.map_cons,value,ih,Int.cast_mul,hom k l]; ring

/-- Sparse multiplication evaluates to the product even when a list has
duplicates, a noncanonical order, or explicitly stored zero coefficients. -/
theorem times_value (ω : Int × Nat → B)
    (hom : ∀i j : Int × Nat,ω (i.1+j.1,i.2+j.2)=ω i*ω j)
    (p q : Poly) : value ω (times p q)=value ω p*value ω q := by
  let operation : Poly → ((Int × Nat) × Int) → Poly := fun r (k,a) =>
    plus r (q.map (fun ((l,b) : (Int × Nat) × Int) => ((k.1+l.1,k.2+l.2),a*b)))
  have f (s r : Poly) : value ω (s.foldl operation r)=value ω r+value ω s*value ω q := by
    induction s generalizing r with
    | nil => simp [value]
    | cons h s ih =>
      rcases h with ⟨i,b⟩
      simp only [List.foldl_cons,ih,operation,plus_value,shift_value ω hom,value]; ring
  simpa only [times,operation,value,zero_add] using f p []

/-- The weights for the actual periodic spatial coordinate and normalized
polynomial time. Negative spatial modes use inverse powers. -/
def fourierWeight (x t : ℝ) (k : Int × Nat) : ℂ :=
  (Complex.exp ((x:ℂ)*Complex.I))^k.1 * (t:ℂ)^k.2

theorem evaluate_product (x t : ℝ) (p q : Poly) :
    value (fourierWeight x t) (times p q)=
      value (fourierWeight x t) p*value (fourierWeight x t) q := by
  apply times_value
  intro i j
  simp only [fourierWeight,zpow_add₀ (Complex.exp_ne_zero _),pow_add]; ring

private theorem fold_abs (p : Poly) (t : Nat) :
    p.foldl (fun acc e => acc+e.2.natAbs) t = t+absSum p := by
  induction p generalizing t with
  | nil => simp [absSum]
  | cons a l ih =>
    simp only [List.foldl_cons]
    change _=t+(List.foldl _ (0+a.2.natAbs) l)
    rw [zero_add]
    rw [ih,ih a.2.natAbs]
    omega

theorem value_norm (ω : Int × Nat → ℂ) (cap : ∀k,‖ω k‖≤1) (p : Poly) :
    ‖value ω p‖≤(absSum p:ℝ) := by
  induction p with
  | nil => simp [value,absSum]
  | cons a p ih =>
    obtain ⟨k,b⟩ := a
    change ‖(b:ℂ)*ω k+value ω p‖≤(p.foldl (fun acc e => acc+e.2.natAbs) (0+b.natAbs):Nat)
    rw [zero_add,fold_abs,Nat.cast_add]
    apply (norm_add_le ..).trans (add_le_add ?_ ih)
    rw [norm_mul]
    have inorm : ‖(b:ℂ)‖=(b.natAbs:ℝ) := by simp [Complex.norm_intCast,Nat.cast_natAbs]
    rw [inorm]
    exact le_of_le_of_eq (mul_le_mul_of_nonneg_left (cap k) (Nat.cast_nonneg _)) (mul_one _)

/-- A Fourier coefficient of a time-polynomial series at one slab time. -/
def mode (t : ℝ) (n : Int) : Poly → ℝ
  | [] => 0
  | ((k,j),a)::p => (if n=k then (a:ℝ)*t^j else 0)+mode t n p

/-- The unweighted Fourier sum at any time is bounded by the exact total
coefficient majorant. This applies to every finite choice of frequencies. -/
theorem fourier_mass (S : Finset Int) {t : ℝ} (ht : |t|≤1) (p : Poly) :
    (∑ n ∈ S, |mode t n p|) ≤ (absSum p:ℝ) := by
  induction p with
  | nil => simp [mode,absSum]
  | cons term p ih =>
    obtain ⟨⟨k,j⟩,a⟩ := term
    have coeff : |(a:ℝ)*t^j|≤(a.natAbs:ℝ) := by
      rw [abs_mul,abs_pow,Nat.cast_natAbs,Int.cast_abs]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) ht) (abs_nonneg _)).trans_eq (mul_one _)
    have h : (∑ n ∈ S, |if n=k then (a:ℝ)*t^j else 0|)≤(a.natAbs:ℝ) := by
      simp only [apply_ite abs,abs_zero,Finset.sum_ite_eq']
      split_ifs <;> first | exact coeff | positivity
    change _ ≤ ((p.foldl (fun acc e => acc+e.2.natAbs) (0+a.natAbs):Nat):ℝ)
    rw [zero_add,fold_abs,Nat.cast_add]
    calc
      _ ≤ ∑ n ∈ S,(|if n=k then (a:ℝ)*t^j else 0|+|mode t n p|) :=
        Finset.sum_le_sum fun _ _ => abs_add_le .. 
      _ ≤ _ := by rw [Finset.sum_add_distrib]; exact add_le_add h ih

theorem residual_fourier_bound (S : Finset Int) {t : ℝ} (ht : |t|≤1) :
    (∑ n ∈ S, |mode t n residual|)/((2*D^5*C:Int):ℝ) ≤ defectBound := by
  have denpos : (0:ℝ)<((2*D^5*C:Int):ℝ) := by norm_num [D,C]
  have t0 : (absSum residual:ℝ)*10^9 ≤ 47091*((2*D^5*C:Int):ℝ) := by
    exact_mod_cast residual_certificate.2.2.2
  apply (div_le_iff₀ denpos).mpr
  unfold defectBound
  linarith only [t0,fourier_mass S ht residual]

/-- The exact coefficient counts in the residual and derivative certificate
give a numerical threshold after normalization by their actual denominators. -/
theorem certified_coefficient_barrier :
    (slab+Real.sqrt (2*slab))*
    ((absSum residual : ℝ) / ((2*D^5*C:Int):ℝ)
      + coefficient ((absSum vCoeffs : ℝ)/(D:ℝ)+radius/2)
          ((absSum wCoeffs : ℝ)/(D:ℝ)+radius)*radius) ≤ 67490/1000000000000 ∧
    (67490/1000000000000 : ℝ)<radius := by
  have dpos : (0:ℝ)<(D:ℝ) := by norm_num [D]
  have denpos : (0:ℝ)<((2*D^5*C:Int):ℝ) := by norm_num [D,C]
  have v : (absSum vCoeffs:ℝ)*10^8 ≤ 120000222*(D:ℝ) := by
    exact_mod_cast derivative_certificate.1
  have w : (absSum wCoeffs:ℝ)*10^8 ≤ 40000573*(D:ℝ) := by
    exact_mod_cast derivative_certificate.2
  have t : (absSum residual:ℝ)*10^9 ≤ 47091*((2*D^5*C:Int):ℝ) := by
    exact_mod_cast residual_certificate.2.2.2
  apply numerical_barrier
  · dsimp [radius]; positivity
  · dsimp [radius]; positivity
  · exact div_nonneg (Nat.cast_nonneg _) denpos.le
  · apply add_le_add_left
    apply (div_le_iff₀ dpos).mpr
    linarith only [v]
  · apply add_le_add_left
    apply (div_le_iff₀ dpos).mpr
    linarith only [w]
  · apply (div_le_iff₀ denpos).mpr
    unfold defectBound
    linarith only [t]

end MigrationGeometry.AngularGauge.FourierExample
#print axioms MigrationGeometry.AngularGauge.FourierExample.times_value
#print axioms MigrationGeometry.AngularGauge.FourierExample.certified_coefficient_barrier
