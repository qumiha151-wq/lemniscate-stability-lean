import Lemniscate.PeriodicSobolevClassicalJet
import Lemniscate.PeriodicSmoothClassicalJet
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! A standard C^j estimate for a normal graph, using the actual classical
jet of its Sobolev height. The constant is an operator norm of the finite
Leibniz map; no numerical derivative estimates or height smallness enter.

-/
noncomputable section
namespace Lemniscate
open Complex Set
open scoped ContDiff BigOperators

/-- The usual sum of the suprema of derivatives through order j.
For the periodic C^j functions below each supremum is finite. -/
def periodicCjNorm (j : ℕ) (E : ℝ → ℂ) : ℝ :=
  ∑ i : Fin (j+1), sSup (Set.range (fun x : ℝ => ‖iteratedDeriv i.val E x‖))

private def normalGraphReferenceJet
    (T : ℝ) (j : ℕ) (β : ℝ → ℂ)
    (hβ : ContDiff ℝ (j : ℕ∞ω) β) (hp : Function.Periodic β T) :
    Fin (j+1) → C(AddCircle T,ℂ) := fun i =>
  ⟨(periodic_iterated_deriv T β hp i.val).lift,
    (hβ.continuous_iteratedDeriv i.val
      (by exact_mod_cast Nat.le_of_lt_succ i.isLt)).quotient_lift _⟩

private theorem normal_graph_reference_jet_apply
    (T : ℝ) (j : ℕ) (β : ℝ → ℂ)
    (hβ : ContDiff ℝ (j : ℕ∞ω) β) (hp : Function.Periodic β T)
    (i : Fin (j+1)) (x : ℝ) :
    normalGraphReferenceJet T j β hβ hp i (x:AddCircle T)=iteratedDeriv i.val β x := rfl

variable (T : ℝ) [Fact (0<T)]

private def normalGraphLeibnizJet (j : ℕ) (N : Fin (j+1) → C(AddCircle T,ℂ)) :
    (Fin (j+1) → C(AddCircle T,ℂ)) →L[ℂ] (Fin (j+1) → C(AddCircle T,ℂ)) :=
  ContinuousLinearMap.pi fun i =>
    ∑ r : Fin (i.val+1), ((i.val.choose r.val : ℕ):ℂ) •
      ((ContinuousLinearMap.mul ℂ C(AddCircle T,ℂ)
        (N ⟨i.val-r.val,by omega⟩)).comp
        (ContinuousLinearMap.proj (⟨r.val,by omega⟩ : Fin (j+1))))

private theorem normal_graph_leibniz_jet_apply
    (j : ℕ) (N D : Fin (j+1) → C(AddCircle T,ℂ))
    (i : Fin (j+1)) (x : ℝ) :
    normalGraphLeibnizJet T j N D i (x:AddCircle T)=
      ∑ r : Fin (i.val+1), (i.val.choose r.val : ℂ)*
        D ⟨r.val,by omega⟩ (x:AddCircle T)*N ⟨i.val-r.val,by omega⟩ (x:AddCircle T) := by
  simp [normalGraphLeibnizJet,ContinuousLinearMap.mul_apply',mul_comm,mul_left_comm,mul_assoc]

private theorem normal_graph_standard_norm_le
    (j : ℕ) (E : ℝ → ℂ) (J : Fin (j+1) → C(AddCircle T,ℂ))
    (hJ : ∀ (i : Fin (j+1)) (x : ℝ), iteratedDeriv i.val E x=J i (x:AddCircle T)) :
    periodicCjNorm j E≤(j+1:ℝ)*‖J‖ := by
  calc
    _≤∑ _i : Fin (j+1), ‖J‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨x,rfl⟩
      change ‖iteratedDeriv i.val E x‖≤‖J‖
      rw [hJ i x]
      exact ((J i).norm_coe_le_norm (x:AddCircle T)).trans (norm_le_pi_norm J i)
    _=(j+1:ℝ)*‖J‖ := by simp

private theorem normal_graph_rotation_jet_bound
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (A : X →L[ℂ] Y) (B : Y) (f : X) (z w : ℂ) (hz : ‖z‖=1) :
    ‖(z-w) • B+z • A f‖≤(‖B‖+‖A‖+1)*(‖f‖+‖z-w‖) := by
  let C : ℝ := ‖B‖+‖A‖+1
  have hCB : ‖B‖≤C := by dsimp only [C]; linarith only [norm_nonneg A]
  have hCA : ‖A‖≤C := by dsimp only [C]; linarith only [norm_nonneg B]
  calc
    _≤‖(z-w) • B‖+‖z • A f‖ := norm_add_le _ _
    _=‖z-w‖*‖B‖+‖A f‖ := by rw [norm_smul,norm_smul,hz,one_mul]
    _≤‖z-w‖*‖B‖+‖A‖*‖f‖ := add_le_add (le_refl _) (A.le_opNorm f)
    _≤C*‖z-w‖+C*‖f‖ := add_le_add
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hCB (norm_nonneg (z-w)))
      (mul_le_mul_of_nonneg_right hCA (norm_nonneg f))
    _=C*(‖f‖+‖z-w‖) := by ring

set_option maxHeartbeats 800000 in
/-- The normal-graph curve error has its actual Leibniz derivative jet and
a standard C^j bound controlled by the H^(j+1) height and the rotation error.
Only the graph rotation z needs unit norm; the comparison scalar w is arbitrary.
-/
theorem normal_graph_cj_estimate
    (j : ℕ) (β ν : ℝ → ℂ)
    (hβ : ContDiff ℝ (j : ℕ∞ω) β) (hν : ContDiff ℝ (j : ℕ∞ω) ν)
    (hβper : Function.Periodic β T) (hνper : Function.Periodic ν T) :
    ∃ C>0, ∀ (f : CircleSobolevSpace T (j+1)) (z w : ℂ), ‖z‖=1 →
      let D := circleSobolevClassicalJet T j f
      let h : ℝ → ℂ := fun x => D 0 (x:AddCircle T)
      let E : ℝ → ℂ := fun x => z*(β x+h x*ν x)-w*β x
      ContDiff ℝ (j : ℕ∞ω) E ∧
        (∀ (i : Fin (j+1)) (x : ℝ), iteratedDeriv i.val E x=
          (z-w)*iteratedDeriv i.val β x+
            z*(∑ r : Fin (i.val+1), (i.val.choose r.val : ℂ)*
              D ⟨r.val,by omega⟩ (x:AddCircle T)*iteratedDeriv (i.val-r.val) ν x)) ∧
        periodicCjNorm j E≤C*(‖f‖+‖z-w‖) := by
  let B := normalGraphReferenceJet T j β hβ hβper
  let N := normalGraphReferenceJet T j ν hν hνper
  let A : CircleSobolevSpace T (j+1) →L[ℂ] (Fin (j+1) → C(AddCircle T,ℂ)) :=
    (normalGraphLeibnizJet T j N).comp (circleSobolevClassicalJet T j)
  have hB (i : Fin (j+1)) (x : ℝ) : B i (x:AddCircle T)=iteratedDeriv i.val β x :=
    normal_graph_reference_jet_apply T j β hβ hβper i x
  have hN (i : Fin (j+1)) (x : ℝ) : N i (x:AddCircle T)=iteratedDeriv i.val ν x :=
    normal_graph_reference_jet_apply T j ν hν hνper i x
  let C₀ : ℝ := ‖B‖+‖A‖+1
  refine ⟨(j+1:ℝ)*C₀,by dsimp only [C₀]; positivity,?_⟩
  intro f z w hz
  let D := circleSobolevClassicalJet T j f
  let h : ℝ → ℂ := fun x => D 0 (x:AddCircle T)
  let E : ℝ → ℂ := fun x => z*(β x+h x*ν x)-w*β x
  have hregular := circle_sobolev_classical_regularity T j f
  have hh : ContDiff ℝ (j : ℕ∞ω) h := hregular.1
  have hE : E=(fun x => (z-w)*β x+z*(h x*ν x)) := by
    funext x
    dsimp only [E]
    ring
  have hEsmooth : ContDiff ℝ (j : ℕ∞ω) E := by
    rw [hE]
    exact (contDiff_const.mul hβ).add (contDiff_const.mul (hh.mul hν))
  have hproduct (i : Fin (j+1)) (x : ℝ) :
      iteratedDeriv i.val (fun x => h x*ν x) x=A f i (x:AddCircle T) := by
    have hle : (i.val : ℕ∞ω)≤j := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hhi : ContDiffAt ℝ (i.val : ℕ∞ω) h x := (hh.of_le hle).contDiffAt
    have hνi : ContDiffAt ℝ (i.val : ℕ∞ω) ν x := (hν.of_le hle).contDiffAt
    rw [iteratedDeriv_fun_mul hhi hνi]
    change (∑ r ∈ Finset.range (i.val+1), (i.val.choose r : ℂ)*
      iteratedDeriv r h x*iteratedDeriv (i.val-r) ν x)=
        normalGraphLeibnizJet T j N D i (x:AddCircle T)
    rw [normal_graph_leibniz_jet_apply]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    have hr : iteratedDeriv r.val h x=D ⟨r.val,by omega⟩ (x:AddCircle T) :=
      congrFun (hregular.2 ⟨r.val,by omega⟩) x
    rw [hr]
    rw [hN]
  let J : Fin (j+1) → C(AddCircle T,ℂ) := (z-w) • B+z • A f
  have hJ (i : Fin (j+1)) (x : ℝ) : iteratedDeriv i.val E x=J i (x:AddCircle T) := by
    have hle : (i.val : ℕ∞ω)≤j := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    rw [hE,iteratedDeriv_fun_add
      (contDiff_const.mul (hβ.of_le hle)).contDiffAt
      (contDiff_const.mul ((hh.of_le hle).mul (hν.of_le hle))).contDiffAt]
    rw [iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field,hproduct]
    change (z-w)*iteratedDeriv i.val β x+z*(A f i) (x:AddCircle T)=
      (z-w)*(B i (x:AddCircle T))+z*(A f i) (x:AddCircle T)
    rw [hB]
  refine ⟨hEsmooth,?_,?_⟩
  · intro i x
    rw [hJ]
    change (z-w)*(B i (x:AddCircle T))+z*(A f i) (x:AddCircle T)=_
    rw [hB]
    apply congrArg (fun v : ℂ => (z-w)*iteratedDeriv i.val β x+z*v)
    change normalGraphLeibnizJet T j N D i (x:AddCircle T)=_
    rw [normal_graph_leibniz_jet_apply]
    apply Finset.sum_congr rfl
    intro r _
    rw [hN]
  · calc
      periodicCjNorm j E≤(j+1:ℝ)*‖J‖ := normal_graph_standard_norm_le T j E J hJ
      _≤(j+1:ℝ)*(C₀*(‖f‖+‖z-w‖)) :=
        mul_le_mul_of_nonneg_left (normal_graph_rotation_jet_bound A B f z w hz) (by positivity)
      _=((j+1:ℝ)*C₀)*(‖f‖+‖z-w‖) := by ring

end Lemniscate
