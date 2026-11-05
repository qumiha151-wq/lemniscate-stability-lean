import Lemniscate.PeriodicSobolevClassicalJet
import Lemniscate.PeriodicClassicalSobolevFamily
import Lemniscate.PeriodicCoefficientAlgebra
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-! Finite classical circle jets, represented by iterated first-order
square-zero extensions. The redundant coordinates avoid combinatorial
product formulas. Invertibility depends only on the value coordinate. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ContDiff

@[reducible] def CircleClassicalJetAlgebra (T : ℝ) : ℕ → Type
  | 0 => C(AddCircle T, ℂ)
  | n+1 => TrivSqZeroExt (CircleClassicalJetAlgebra T n)
      (CircleClassicalJetAlgebra T n)

@[reducible] def circleClassicalJetNormedCommRing (T : ℝ) [Fact (0 < T)] :
    ∀ n, NormedCommRing (CircleClassicalJetAlgebra T n)
  | 0 => inferInstanceAs (NormedCommRing C(AddCircle T, ℂ))
  | n+1 => by
    letI := circleClassicalJetNormedCommRing T n
    exact inferInstanceAs (NormedCommRing (TrivSqZeroExt
      (CircleClassicalJetAlgebra T n) (CircleClassicalJetAlgebra T n)))

attribute [instance] circleClassicalJetNormedCommRing

@[reducible] def circleClassicalJetNormedAlgebra (T : ℝ) [Fact (0 < T)] :
    ∀ n, NormedAlgebra ℂ (CircleClassicalJetAlgebra T n)
  | 0 => inferInstanceAs (NormedAlgebra ℂ C(AddCircle T, ℂ))
  | n+1 => by
    letI := circleClassicalJetNormedAlgebra T n
    exact inferInstanceAs (NormedAlgebra ℂ (TrivSqZeroExt
      (CircleClassicalJetAlgebra T n) (CircleClassicalJetAlgebra T n)))

attribute [instance] circleClassicalJetNormedAlgebra

@[reducible] def circleClassicalJetCompleteSpace (T : ℝ) [Fact (0 < T)] :
    ∀ n, CompleteSpace (CircleClassicalJetAlgebra T n)
  | 0 => inferInstanceAs (CompleteSpace C(AddCircle T, ℂ))
  | n+1 => by
    letI := circleClassicalJetCompleteSpace T n
    exact inferInstanceAs (CompleteSpace (TrivSqZeroExt
      (CircleClassicalJetAlgebra T n) (CircleClassicalJetAlgebra T n)))

attribute [instance] circleClassicalJetCompleteSpace

def circleClassicalJetValue (T : ℝ) [Fact (0 < T)] :
    ∀ n, CircleClassicalJetAlgebra T n →ₐ[ℂ] C(AddCircle T, ℂ)
  | 0 => AlgHom.id ℂ _
  | n+1 => (circleClassicalJetValue T n).comp
      (TrivSqZeroExt.fstHom ℂ _ _)

def circleClassicalJetValueCLM (T : ℝ) [Fact (0 < T)] :
    ∀ n, CircleClassicalJetAlgebra T n →L[ℂ] C(AddCircle T, ℂ)
  | 0 => ContinuousLinearMap.id ℂ _
  | n+1 => (circleClassicalJetValueCLM T n).comp
      ((TrivSqZeroExt.fstCLM _ _).restrictScalars ℂ)

@[simp] theorem circle_classical_jet_value_clm (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (z : CircleClassicalJetAlgebra T n) :
    circleClassicalJetValueCLM T n z = circleClassicalJetValue T n z := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih z.fst

theorem circle_classical_jet_isUnit (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (z : CircleClassicalJetAlgebra T n) :
    IsUnit z ↔ IsUnit (circleClassicalJetValue T n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
    exact ih z.fst

def circleClassicalJetPack (T : ℝ) [Fact (0 < T)] :
    ∀ n, (Fin (n+1) → C(AddCircle T, ℂ)) →L[ℂ] CircleClassicalJetAlgebra T n
  | 0 => ContinuousLinearMap.proj 0
  | n+1 =>
    ((TrivSqZeroExt.inlCLM _ _).restrictScalars ℂ).comp
      ((circleClassicalJetPack T n).comp
        (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.castSucc)) +
    ((TrivSqZeroExt.inrCLM _ _).restrictScalars ℂ).comp
      ((circleClassicalJetPack T n).comp
        (ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj j.succ))

@[simp] theorem circle_classical_jet_pack_fst (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (F : Fin (n+2) → C(AddCircle T, ℂ)) :
    TrivSqZeroExt.fst (circleClassicalJetPack T (n+1) F) =
      circleClassicalJetPack T n (fun j => F j.castSucc) := by
  simp only [circleClassicalJetPack,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    TrivSqZeroExt.inlCLM_apply,TrivSqZeroExt.inrCLM_apply,
    TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_inl,TrivSqZeroExt.fst_inr,add_zero]
  rfl

@[simp] theorem circle_classical_jet_pack_snd (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (F : Fin (n+2) → C(AddCircle T, ℂ)) :
    TrivSqZeroExt.snd (circleClassicalJetPack T (n+1) F) =
      circleClassicalJetPack T n (fun j => F j.succ) := by
  simp only [circleClassicalJetPack,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    TrivSqZeroExt.inlCLM_apply,TrivSqZeroExt.inrCLM_apply,
    TrivSqZeroExt.snd_add,TrivSqZeroExt.snd_inl,TrivSqZeroExt.snd_inr,zero_add]
  rfl

@[simp] theorem circle_classical_jet_pack_value (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (F : Fin (n+1) → C(AddCircle T, ℂ)) :
    circleClassicalJetValue T n (circleClassicalJetPack T n F) = F 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change circleClassicalJetValue T n (circleClassicalJetPack T (n+1) F).fst = F 0
    rw [circle_classical_jet_pack_fst]
    exact ih _

def CircleClassicalJetHolonomic (T : ℝ) [Fact (0 < T)] :
    ∀ n, CircleClassicalJetAlgebra T n → Prop
  | 0, _ => True
  | n+1, z => CircleClassicalJetHolonomic T n z.fst ∧
      CircleClassicalJetHolonomic T n z.snd ∧
      HasCircleDeriv T (circleClassicalJetValue T n z.fst)
        (circleClassicalJetValue T n z.snd)

theorem circle_classical_jet_pack_holonomic (T : ℝ) [Fact (0 < T)]
    (n : ℕ) (F : Fin (n+1) → C(AddCircle T, ℂ))
    (hF : ∀ j : Fin n, HasCircleDeriv T (F j.castSucc) (F j.succ)) :
    CircleClassicalJetHolonomic T n (circleClassicalJetPack T n F) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change CircleClassicalJetHolonomic T n
        (TrivSqZeroExt.fst (circleClassicalJetPack T (n+1) F)) ∧
      CircleClassicalJetHolonomic T n
        (TrivSqZeroExt.snd (circleClassicalJetPack T (n+1) F)) ∧ _
    rw [circle_classical_jet_pack_fst,circle_classical_jet_pack_snd]
    change CircleClassicalJetHolonomic T n (circleClassicalJetPack T n
        (fun j => F j.castSucc)) ∧
      CircleClassicalJetHolonomic T n (circleClassicalJetPack T n
        (fun j => F j.succ)) ∧ _
    refine ⟨ih _ (fun j => ?_),ih _ (fun j => ?_),?_⟩
    · exact hF j.castSucc
    · simpa only [Fin.succ_castSucc] using hF j.succ
    · simpa only [circle_classical_jet_pack_value] using hF 0

namespace CircleClassicalJetHolonomic
variable {T : ℝ} [Fact (0 < T)]

theorem const (n : ℕ) (c : ℂ) :
    CircleClassicalJetHolonomic T n (algebraMap ℂ _ c) := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
    simp only [CircleClassicalJetHolonomic,TrivSqZeroExt.algebraMap_eq_inl',
      TrivSqZeroExt.fst_inl,TrivSqZeroExt.snd_inl]
    refine ⟨ih c,?_,?_⟩
    · simpa only [map_zero] using (ih 0)
    · intro x
      change HasDerivAt (fun y : ℝ => circleClassicalJetValue T n
        (algebraMap ℂ _ c) (y : AddCircle T))
        (circleClassicalJetValue T n 0 (x : AddCircle T)) x
      simpa only [AlgHom.commutes,algebraMap_apply,
        smul_eq_mul,mul_one,map_zero,ContinuousMap.zero_apply] using hasDerivAt_const x c

theorem add {n : ℕ} {z w : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z)
    (hw : CircleClassicalJetHolonomic T n w) :
    CircleClassicalJetHolonomic T n (z+w) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hz.1 hw.1,ih hz.2.1 hw.2.1,?_⟩
    intro x
    simpa only [TrivSqZeroExt.fst_add,TrivSqZeroExt.snd_add,map_add,
      ContinuousMap.add_apply] using! (hz.2.2 x).add (hw.2.2 x)

theorem neg {n : ℕ} {z : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z) :
    CircleClassicalJetHolonomic T n (-z) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hz.1,ih hz.2.1,?_⟩
    intro x
    simpa only [TrivSqZeroExt.fst_neg,TrivSqZeroExt.snd_neg,map_neg,
      ContinuousMap.neg_apply] using! (hz.2.2 x).neg

theorem sub {n : ℕ} {z w : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z)
    (hw : CircleClassicalJetHolonomic T n w) :
    CircleClassicalJetHolonomic T n (z-w) := by
  simpa only [sub_eq_add_neg] using hz.add hw.neg

theorem mul {n : ℕ} {z w : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z)
    (hw : CircleClassicalJetHolonomic T n w) :
    CircleClassicalJetHolonomic T n (z*w) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    refine ⟨ih hz.1 hw.1,?_,?_⟩
    · simpa only [TrivSqZeroExt.snd_mul,op_smul_eq_smul,smul_eq_mul] using
        (ih hz.1 hw.2.1).add (ih hw.1 hz.2.1)
    · intro x
      have h := (hz.2.2 x).mul (hw.2.2 x)
      simpa only [TrivSqZeroExt.fst_mul,TrivSqZeroExt.snd_mul,
        op_smul_eq_smul,smul_eq_mul,map_add,map_mul,ContinuousMap.mul_apply,
        ContinuousMap.add_apply,mul_comm,add_comm] using! h

theorem pow {n : ℕ} {z : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z) (k : ℕ) :
    CircleClassicalJetHolonomic T n (z^k) := by
  induction k with
  | zero => simpa only [pow_zero,map_one] using (const n 1 :
      CircleClassicalJetHolonomic T n (algebraMap ℂ _ 1))
  | succ k ih => simpa only [pow_succ] using ih.mul hz

theorem smul {n : ℕ} {z : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z) (c : ℂ) :
    CircleClassicalJetHolonomic T n (c • z) := by
  simpa only [Algebra.smul_def] using (const n c).mul hz

private theorem circle_inverse_deriv {f df : C(AddCircle T, ℂ)}
    (hf : HasCircleDeriv T f df) (hu : IsUnit f) :
    HasCircleDeriv T (Ring.inverse f) (-((Ring.inverse f)^2)*df) := by
  intro x
  have hx := (ContinuousMap.isUnit_iff_forall_ne_zero f).mp hu (x : AddCircle T)
  have heq : (fun y : ℝ => Ring.inverse f (y : AddCircle T)) =
      (fun y : ℝ => (f (y : AddCircle T))⁻¹) :=
    funext fun y => continuous_map_ring_inverse_apply f hu _
  rw [heq]
  convert! (hf x).inv hx using 1
  simp only [ContinuousMap.mul_apply,ContinuousMap.neg_apply,
    ContinuousMap.pow_apply,continuous_map_ring_inverse_apply f hu]
  field_simp

private theorem inverse_pair (R : Type*) [CommRing R]
    (z : TrivSqZeroExt R R) (hu : IsUnit z) :
    Ring.inverse z =
      TrivSqZeroExt.inl (Ring.inverse z.fst) +
        TrivSqZeroExt.inr (-((Ring.inverse z.fst)^2)*z.snd) := by
  have hf : IsUnit z.fst := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hu
  let y : TrivSqZeroExt R R :=
    TrivSqZeroExt.inl (Ring.inverse z.fst) +
      TrivSqZeroExt.inr (-((Ring.inverse z.fst)^2)*z.snd)
  have hzy : z*y=1 := by
    apply TrivSqZeroExt.ext
    · simpa only [y,TrivSqZeroExt.fst_mul,TrivSqZeroExt.fst_add,
        TrivSqZeroExt.fst_inl,TrivSqZeroExt.fst_inr,add_zero,TrivSqZeroExt.fst_one]
        using Ring.mul_inverse_cancel z.fst hf
    · simp only [y,TrivSqZeroExt.snd_mul,TrivSqZeroExt.snd_add,
        TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_inl,TrivSqZeroExt.fst_inr,
        TrivSqZeroExt.snd_inl,TrivSqZeroExt.snd_inr,add_zero,zero_add,
        TrivSqZeroExt.snd_one,op_smul_eq_smul,smul_eq_mul]
      calc
        _ = -(z.fst*Ring.inverse z.fst)*(Ring.inverse z.fst*z.snd)+
            Ring.inverse z.fst*z.snd := by ring
        _ = 0 := by rw [Ring.mul_inverse_cancel z.fst hf]; ring
  calc
    Ring.inverse z = Ring.inverse z * 1 := (mul_one _).symm
    _ = Ring.inverse z * (z*y) := by rw [hzy]
    _ = y := Ring.inverse_mul_cancel_left z y hu

theorem inverse {n : ℕ} {z : CircleClassicalJetAlgebra T n}
    (hz : CircleClassicalJetHolonomic T n z) (hu : IsUnit z) :
    CircleClassicalJetHolonomic T n (Ring.inverse z) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hf : IsUnit z.fst := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp hu
    rw [inverse_pair _ z hu]
    simp only [CircleClassicalJetHolonomic,TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl,TrivSqZeroExt.fst_inr,add_zero,
      TrivSqZeroExt.snd_add,TrivSqZeroExt.snd_inl,TrivSqZeroExt.snd_inr,zero_add]
    refine ⟨ih hz.1 hf,((ih hz.1 hf).pow 2).neg.mul hz.2.1,?_⟩
    have hval : circleClassicalJetValue T n (Ring.inverse z.fst) =
        Ring.inverse (circleClassicalJetValue T n z.fst) := by
      apply (IsUnit.map (circleClassicalJetValue T n) hf).mul_left_cancel
      rw [← map_mul,Ring.mul_inverse_cancel z.fst hf,map_one,
        Ring.mul_inverse_cancel _ (IsUnit.map _ hf)]
    simpa only [TrivSqZeroExt.fst_add,TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr,add_zero,TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl,TrivSqZeroExt.snd_inr,zero_add,
      map_mul,map_neg,map_pow,hval] using
      circle_inverse_deriv hz.2.2 (IsUnit.map _ hf)

end CircleClassicalJetHolonomic

def circleClassicalJetCoordinate (T : ℝ) [Fact (0 < T)] :
    ∀ n, Fin (n+1) → CircleClassicalJetAlgebra T n →L[ℂ] C(AddCircle T, ℂ)
  | 0, _ => circleClassicalJetValueCLM T 0
  | n+1, j => Fin.cases (circleClassicalJetValueCLM T (n+1))
      (fun i => (circleClassicalJetCoordinate T n i).comp
        ((TrivSqZeroExt.sndCLM _ _).restrictScalars ℂ)) j

@[simp] theorem circle_classical_jet_coordinate_zero (T : ℝ) [Fact (0 < T)] (n : ℕ)
    (z : CircleClassicalJetAlgebra T n) :
    circleClassicalJetCoordinate T n 0 z = circleClassicalJetValue T n z := by
  cases n <;> exact circle_classical_jet_value_clm T _ z

theorem circle_classical_jet_coordinate_deriv (T : ℝ) [Fact (0 < T)]
    (n : ℕ) (z : CircleClassicalJetAlgebra T n)
    (hz : CircleClassicalJetHolonomic T n z) (j : Fin n) :
    HasCircleDeriv T (circleClassicalJetCoordinate T n j.castSucc z)
      (circleClassicalJetCoordinate T n j.succ z) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) j
    · change HasCircleDeriv T (circleClassicalJetValueCLM T (n+1) z)
        (circleClassicalJetCoordinate T n 0 z.snd)
      rw [circle_classical_jet_coordinate_zero,circle_classical_jet_value_clm]
      exact hz.2.2
    · rw [Fin.castSucc_succ]
      exact ih z.snd hz.2.1 i

/-- A holonomic jet whose coordinates depend smoothly on a parameter yields
the actual Sobolev family, with exactly the same parameter regularity. -/
theorem circle_classical_jet_sobolev_family (T : ℝ) [Fact (0 < T)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (m : ℕ∞ω) (U : Set E)
    (F : E → CircleClassicalJetAlgebra T n)
    (hF : ContDiffOn ℝ m F U)
    (hhol : ∀ x ∈ U, CircleClassicalJetHolonomic T n (F x)) :
    ∃ u : E → CircleSobolevSpace T n,
      ContDiffOn ℝ m u U ∧
      ∀ x ∈ U, ∀ j : Fin (n+1),
        circleSobolevCoordinate T n j (u x) =
          circleContinuousL2 T (circleClassicalJetCoordinate T n j (F x)) := by
  apply periodic_classical_sobolev_family T n m U
    (fun j x => circleClassicalJetCoordinate T n j (F x))
  · intro j
    exact ((circleClassicalJetCoordinate T n j).restrictScalars ℝ).contDiff.comp_contDiffOn hF
  · intro x hx j
    exact circle_classical_jet_coordinate_deriv T n (F x) (hhol x hx) j

end Lemniscate
