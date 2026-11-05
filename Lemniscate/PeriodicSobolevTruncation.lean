import Lemniscate.PeriodicSobolevDerivatives

/-! Order truncation on the actual Sobolev scale, by composing the
already proved adjacent inclusions. -/
noncomputable section
namespace Lemniscate
open Complex
variable (T : ℝ) [Fact (0<T)]

def circleSobolevTruncation (m N : ℕ) (h : m≤N) :
    CircleSobolevSpace T N →L[ℂ] CircleSobolevSpace T m :=
  Nat.leRec (motive := fun N _ => CircleSobolevSpace T N →L[ℂ] CircleSobolevSpace T m)
    (ContinuousLinearMap.id ℂ (CircleSobolevSpace T m))
    (fun {k} _ F => F.comp (circleSobolevInclusion T k)) h

@[simp] theorem circle_sobolev_truncation_self (m : ℕ) :
    circleSobolevTruncation T m m le_rfl=ContinuousLinearMap.id ℂ (CircleSobolevSpace T m) := by
  simp only [circleSobolevTruncation,Nat.leRec_self]

theorem circle_sobolev_truncation_step (m N : ℕ) (h : m≤N) :
    circleSobolevTruncation T m (N+1) (Nat.le_succ_of_le h)=
      (circleSobolevTruncation T m N h).comp (circleSobolevInclusion T N) :=
  Nat.leRec_succ _ _ h

@[simp] theorem circle_sobolev_truncation_coordinate (m N : ℕ) (h : m≤N)
    (j : Fin (m+1)) (f : CircleSobolevSpace T N) :
    circleSobolevCoordinate T m j (circleSobolevTruncation T m N h f)=
      circleSobolevCoordinate T N
        ⟨j.val,lt_of_lt_of_le j.isLt (Nat.add_le_add_right h 1)⟩ f := by
  induction h using Nat.leRec with
  | refl => simp only [circle_sobolev_truncation_self,ContinuousLinearMap.id_apply]
  | @le_succ_of_le N h ih =>
      rw [circle_sobolev_truncation_step T m N h,ContinuousLinearMap.comp_apply,ih,
        circle_sobolev_inclusion_coordinate]
      rfl

@[simp] theorem circle_sobolev_truncation_value (m N : ℕ) (h : m≤N)
    (f : CircleSobolevSpace T N) :
    circleSobolevCoordinate T m 0 (circleSobolevTruncation T m N h f)=
      circleSobolevCoordinate T N 0 f :=
  circle_sobolev_truncation_coordinate T m N h 0 f

theorem circle_sobolev_truncation_comp (l m N : ℕ) (hlm : l≤m) (hmN : m≤N) :
    (circleSobolevTruncation T l m hlm).comp (circleSobolevTruncation T m N hmN)=
      circleSobolevTruncation T l N (hlm.trans hmN) := by
  apply ContinuousLinearMap.ext
  intro f
  apply circle_sobolev_value_injective T l
  simp only [ContinuousLinearMap.comp_apply,circle_sobolev_truncation_value]

end Lemniscate
