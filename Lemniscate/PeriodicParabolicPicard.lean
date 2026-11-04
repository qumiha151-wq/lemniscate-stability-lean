import Lemniscate.PeriodicParabolicNormedSpace
import Lemniscate.PeriodicTimeNonlinearRemainder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Abel

/-! Local nonlinear maximal-regularity solutions by contraction.

The nonlinear time map is the already constructed actual Nemytskii map.
The linear data equivalence records the actual initial value and a given
linear PDE map. No nonlinear solution or nonlinear inverse is assumed.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

variable (T : ℝ) [Fact (0 < T)] (τ : ℝ)

private theorem picard_curve_norm_le (U : CircleParabolicSpace T τ) :
    ‖circleParabolicCurve T τ U‖ ≤ ‖U‖ := norm_fst_le U.1

private theorem picard_h4_norm_le (U : CircleParabolicSpace T τ) :
    ‖circleParabolicH4 T τ U‖ ≤ ‖U‖ :=
  (norm_fst_le U.1.2).trans (norm_snd_le U.1)

private theorem banach_picard
    {X F G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (R : {u : X | ‖u‖ < δ} → G)
    (hR0 : ∀ u : {u : X | ‖u‖ < δ}, u.1 = 0 → R u = 0)
    (hRtame : ∀ u v : {u : X | ‖u‖ < δ},
      ‖R u-R v‖ ≤ K*(‖u.1‖+‖v.1‖)*‖u.1-v.1‖)
    (e : X ≃L[ℂ] (F × G)) :
    ∃ ε > 0, ∃ r > 0, r < δ ∧
      ∀ u0 : F, ‖u0‖ ≤ ε →
        ∃! U : {u : X | ‖u‖ < δ},
          ‖U.1‖ ≤ r ∧ (e U.1).1 = u0 ∧ (e U.1).2 = R U := by
  let E : (F × G) →L[ℂ] X := e.symm.toContinuousLinearMap
  obtain ⟨M,hMpos,hEbound⟩ := E.bound
  have hM : 0 ≤ M := hMpos.le
  let r : ℝ := min (δ/2) (1/(4*K*M+1))
  have hden : 0 < 4*K*M+1 := by positivity
  have hr : 0 < r := lt_min (half_pos hδ) (one_div_pos.mpr hden)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hproduct : 2*K*M*r ≤ (1/2:ℝ) := by
    have h := (le_div_iff₀ hden).mp (min_le_right (δ/2) (1/(4*K*M+1)))
    change r*(4*K*M+1) ≤ 1 at h
    linear_combination (1/2:ℝ)*h+(1/2:ℝ)*hr.le
  let ε : ℝ := r/(2*M+1)
  have hε : 0 < ε := div_pos hr (by positivity)
  refine ⟨ε,hε,r,hr,hrδ,?_⟩
  intro u0 hu0
  let Ball := {U : X | ‖U‖ ≤ r}
  have hclosed : IsClosed {U : X | ‖U‖ ≤ r} :=
    isClosed_le continuous_norm continuous_const
  letI : CompleteSpace Ball := hclosed.isComplete.completeSpace_coe
  let z : Ball := ⟨0,by
    change ‖(0 : X)‖ ≤ r
    simpa only [norm_zero] using hr.le⟩
  letI : Nonempty Ball := ⟨z⟩
  let incl : Ball → {u : X | ‖u‖ < δ} := fun U => ⟨U.1,U.2.trans_lt hrδ⟩
  have hRzero : R (incl z) = 0 := hR0 (incl z) rfl
  have hRdiff (U V : Ball) :
      ‖R (incl U)-R (incl V)‖ ≤ (2*K*r)*‖U.1-V.1‖ := by
    calc
      ‖R (incl U)-R (incl V)‖ ≤ K*(‖U.1‖+‖V.1‖)*‖U.1-V.1‖ :=
        hRtame (incl U) (incl V)
      _ ≤ K*(r+r)*‖U.1-V.1‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (add_le_add U.2 V.2) hK) (norm_nonneg _)
      _ = (2*K*r)*‖U.1-V.1‖ := by ring
  have hRvalue (U : Ball) : ‖R (incl U)‖ ≤ (2*K*r)*‖U.1‖ := by
    simpa only [hRzero,z,sub_zero] using hRdiff U z
  have hdata : M*‖u0‖ ≤ r/2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*M+1)).mp hu0
    change ‖u0‖*(2*M+1) ≤ r at h
    linear_combination (1/2:ℝ)*h+(1/2:ℝ)*(norm_nonneg u0)
  let phi : Ball → X := fun U => E (u0,R (incl U))
  have hself (U : Ball) : ‖phi U‖ ≤ r := by
    have hnonlinear : M*‖R (incl U)‖ ≤ (1/2:ℝ)*r := by
      calc
        M*‖R (incl U)‖ ≤ M*((2*K*r)*‖U.1‖) := mul_le_mul_of_nonneg_left (hRvalue U) hM
        _ = (2*K*M*r)*‖U.1‖ := by ring
        _ ≤ (1/2:ℝ)*‖U.1‖ := mul_le_mul_of_nonneg_right hproduct (norm_nonneg _)
        _ ≤ (1/2:ℝ)*r := mul_le_mul_of_nonneg_left U.2 (by norm_num)
    calc
      ‖phi U‖ ≤ M*‖(u0,R (incl U))‖ := hEbound _
      _ = M*max ‖u0‖ ‖R (incl U)‖ := by rw [Prod.norm_def]
      _ ≤ M*(‖u0‖+‖R (incl U)‖) :=
        mul_le_mul_of_nonneg_left (max_le
          (le_add_of_nonneg_right (norm_nonneg _))
          (le_add_of_nonneg_left (norm_nonneg _))) hM
      _ = M*‖u0‖+M*‖R (incl U)‖ := by ring
      _ ≤ r/2+(1/2:ℝ)*r := add_le_add hdata hnonlinear
      _ = r := by ring
  have hphiDiff (U V : Ball) :
      ‖phi U-phi V‖ ≤ (1/2:ℝ)*‖U.1-V.1‖ := by
    have hpair : (u0,R (incl U))-(u0,R (incl V)) =
        (0,R (incl U)-R (incl V)) := by
      apply Prod.ext <;> simp only [Prod.fst_sub,Prod.snd_sub,sub_self]
    calc
      ‖phi U-phi V‖ = ‖E (0,R (incl U)-R (incl V))‖ := by
        dsimp only [phi]
        rw [← map_sub,hpair]
      _ ≤ M*‖(0,R (incl U)-R (incl V))‖ := hEbound _
      _ = M*‖R (incl U)-R (incl V)‖ := by rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
      _ ≤ M*((2*K*r)*‖U.1-V.1‖) := mul_le_mul_of_nonneg_left (hRdiff U V) hM
      _ = (2*K*M*r)*‖U.1-V.1‖ := by ring
      _ ≤ (1/2:ℝ)*‖U.1-V.1‖ := mul_le_mul_of_nonneg_right hproduct (norm_nonneg _)
  let f : Ball → Ball := fun U => ⟨phi U,hself U⟩
  have hf : ContractingWith (1/2 : ℝ≥0) f := by
    refine ⟨by norm_num,LipschitzWith.of_dist_le_mul ?_⟩
    intro U V
    change dist (phi U) (phi V) ≤ (1/2:ℝ)*dist U.1 V.1
    simpa only [dist_eq_norm] using hphiDiff U V
  let U : Ball := hf.fixedPoint f
  have hfixed : phi U = U.1 := congrArg Subtype.val hf.fixedPoint_isFixedPt
  have hdataU : e U.1 = (u0,R (incl U)) := by
    calc
      e U.1 = e (E (u0,R (incl U))) := congrArg e hfixed.symm
      _ = (u0,R (incl U)) := e.apply_symm_apply _
  have hInitialU : (e U.1).1 = u0 := congrArg Prod.fst hdataU
  have hPDEU : (e U.1).2 = R (incl U) := congrArg Prod.snd hdataU
  refine ⟨incl U,⟨U.2,hInitialU,hPDEU⟩,?_⟩
  intro V hV
  let Vb : Ball := ⟨V.1,hV.1⟩
  have hincl : incl Vb = V := Subtype.ext rfl
  have hdataV : e V.1 = (u0,R V) := Prod.ext hV.2.1 hV.2.2
  have hfixedV : f Vb = Vb := by
    apply Subtype.ext
    change E (u0,R (incl Vb)) = V.1
    rw [hincl]
    change e.symm (u0,R V) = V.1
    rw [← hdataV,e.symm_apply_apply]
  have hVU : Vb = U := hf.fixedPoint_unique' hfixedV hf.fixedPoint_isFixedPt
  exact Subtype.ext (congrArg (fun W : Ball => (W.1 : X)) hVU)

private theorem banach_picard_constraint
    {X F G : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (p : X → Prop) (hp : ∀ u : X, ‖u‖ < δ → p u)
    (R : {u : X | p u} → G)
    (hR0 : ∀ u : {u : X | p u}, u.1 = 0 → R u = 0)
    (hRtame : ∀ u v : {u : X | p u},
      ‖R u-R v‖ ≤ K*(‖u.1‖+‖v.1‖)*‖u.1-v.1‖)
    (initial : X → F) (L : X → G) (e : X ≃L[ℂ] (F × G))
    (heInitial : ∀ u, (e u).1 = initial u) (hePDE : ∀ u, (e u).2 = L u) :
    ∃ ε > 0, ∃ r > 0, r < δ ∧
      ∀ u0 : F, ‖u0‖ ≤ ε →
        ∃! U : {u : X | p u}, ‖U.1‖ ≤ r ∧ initial U.1 = u0 ∧ L U.1 = R U := by
  let incl : {u : X | ‖u‖ < δ} → {u : X | p u} := fun u => ⟨u.1,hp u.1 u.2⟩
  let Q : {u : X | ‖u‖ < δ} → G := fun u => R (incl u)
  have hQ0 (u : {u : X | ‖u‖ < δ}) (hu : u.1 = 0) : Q u = 0 := hR0 (incl u) hu
  have hQtame (u v : {u : X | ‖u‖ < δ}) :
      ‖Q u-Q v‖ ≤ K*(‖u.1‖+‖v.1‖)*‖u.1-v.1‖ := hRtame (incl u) (incl v)
  obtain ⟨ε,hε,r,hr,hrδ,hsolve⟩ := banach_picard hδ hK Q hQ0 hQtame e
  refine ⟨ε,hε,r,hr,hrδ,?_⟩
  intro u0 hu0
  obtain ⟨U,hU,hunique⟩ := hsolve u0 hu0
  refine ⟨incl U,⟨hU.1,(heInitial U.1).symm.trans hU.2.1,
    (hePDE U.1).symm.trans hU.2.2⟩,?_⟩
  intro V hV
  let Vn : {u : X | ‖u‖ < δ} := ⟨V.1,hV.1.trans_lt hrδ⟩
  have hincl : incl Vn = V := Subtype.ext rfl
  have hVn : ‖Vn.1‖ ≤ r ∧ (e Vn.1).1 = u0 ∧ (e Vn.1).2 = Q Vn := by
    refine ⟨hV.1,(heInitial V.1).trans hV.2.1,?_⟩
    calc
      (e Vn.1).2 = L V.1 := hePDE V.1
      _ = R V := hV.2.2
      _ = Q Vn := congrArg R hincl.symm
  exact hincl.symm.trans (congrArg incl (hunique Vn hVn))

private theorem picard_lp_comp_zero {H G : Type*}
    [NormedAddCommGroup H] [NormedAddCommGroup G]
    (N : H → G) (hN0 : N 0 = 0)
    (w : Lp H 2 (volume : Measure unitInterval))
    (f : Lp G 2 (volume : Measure unitInterval)) (hw : w = 0)
    (hf : (f : unitInterval → G) =ᵐ[volume] fun t => N (w t)) : f = 0 := by
  apply Lp.ext
  filter_upwards [hf,Lp.coeFn_zero H 2 (volume : Measure unitInterval),
    Lp.coeFn_zero G 2 (volume : Measure unitInterval)] with t ht hw0 hf0
  have hwt : w t = (0 : H) :=
    (congrArg (fun z : Lp H 2 (volume : Measure unitInterval) => z t) hw).trans hw0
  calc
    f t = N (w t) := ht
    _ = N 0 := congrArg N hwt
    _ = 0 := hN0
    _ = (0 : Lp G 2 (volume : Measure unitInterval)) t := hf0.symm

set_option maxHeartbeats 800000 in
private theorem picard_time_tame_norm {δ C : ℝ} (hC : 0 ≤ C)
    (R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} →
      CircleTimeL2 T)
    (hTime : ∀ U V, ‖R U-R V‖ ≤ C*
      ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
          ‖circleParabolicH4 T τ (U.1-V.1)‖+
        (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
          ‖circleParabolicCurve T τ (U.1-V.1)‖))
    (U V : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ}) :
    ‖R U-R V‖ ≤ (2*C)*(‖U.1‖+‖V.1‖)*‖U.1-V.1‖ := by
  have hcsum : ‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖ ≤
      ‖U.1‖+‖V.1‖ := add_le_add (picard_curve_norm_le T τ U.1) (picard_curve_norm_le T τ V.1)
  have hhsum : ‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖ ≤
      ‖U.1‖+‖V.1‖ := add_le_add (picard_h4_norm_le T τ U.1) (picard_h4_norm_le T τ V.1)
  have hHdiff : ‖circleParabolicH4 T τ (U.1-V.1)‖ ≤ ‖U.1-V.1‖ := by
    simpa only using! picard_h4_norm_le T τ (U.1-V.1)
  have hCdiff : ‖circleParabolicCurve T τ (U.1-V.1)‖ ≤ ‖U.1-V.1‖ := by
    simpa only using! picard_curve_norm_le T τ (U.1-V.1)
  calc
    ‖R U-R V‖ ≤ C*
        ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
            ‖circleParabolicH4 T τ (U.1-V.1)‖+
          (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
            ‖circleParabolicCurve T τ (U.1-V.1)‖) := hTime U V
    _ ≤ C*((‖U.1‖+‖V.1‖)*‖U.1-V.1‖+(‖U.1‖+‖V.1‖)*‖U.1-V.1‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact add_le_add
        (mul_le_mul hcsum hHdiff
          (norm_nonneg (circleParabolicH4 T τ (U.1-V.1)))
          (add_nonneg (norm_nonneg U.1) (norm_nonneg V.1)))
        (mul_le_mul hhsum hCdiff
          (norm_nonneg (circleParabolicCurve T τ (U.1-V.1)))
          (add_nonneg (norm_nonneg U.1) (norm_nonneg V.1)))
    _ = (2*C)*(‖U.1‖+‖V.1‖)*‖U.1-V.1‖ := by ring

private theorem parabolic_picard_time {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (R : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ} → CircleTimeL2 T)
    (hR0 : ∀ U, U.1 = 0 → R U = 0)
    (hTime : ∀ U V, ‖R U-R V‖ ≤ C*
      ((‖circleParabolicCurve T τ U.1‖+‖circleParabolicCurve T τ V.1‖)*
          ‖circleParabolicH4 T τ (U.1-V.1)‖+
        (‖circleParabolicH4 T τ U.1‖+‖circleParabolicH4 T τ V.1‖)*
          ‖circleParabolicCurve T τ (U.1-V.1)‖))
    (L : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T)
    (e : CircleParabolicSpace T τ ≃L[ℂ] (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInitial : ∀ U, (e U).1 = circleParabolicInitialValue T τ U)
    (hePDE : ∀ U, (e U).2 = L U) :
    ∃ ε > 0, ∃ r > 0, r < δ ∧
      ∀ u0 : CircleSobolevSpace T 2, ‖u0‖ ≤ ε →
        ∃! U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ},
          ‖U.1‖ ≤ r ∧ circleParabolicInitialValue T τ U.1 = u0 ∧ L U.1 = R U := by
  simpa only using! (banach_picard_constraint
    (X := CircleParabolicSpace T τ) (F := CircleSobolevSpace T 2) (G := CircleTimeL2 T)
    hδ (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC)
    (fun U => ‖circleParabolicCurve T τ U‖ < δ)
    (fun U hU => (picard_curve_norm_le T τ U).trans_lt hU) R hR0
    (picard_time_tame_norm T τ hC R hTime)
    (circleParabolicInitialValue T τ) L e heInitial hePDE)

private theorem parabolic_nemytskii_zero
    {δ C : ℝ} {N : CircleSobolevSpace T 4 → CircleL2 T}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hN0 : N 0 = 0)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖)) :
    ∀ U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ},
      U.1 = 0 → circleParabolicNemytskii T τ hδ hC hN0 htame U = 0 := by
  intro U hU
  have hH : circleParabolicH4 T τ U.1 = 0 :=
    (congrArg (circleParabolicH4 T τ) hU).trans (map_zero (circleParabolicH4 T τ))
  exact picard_lp_comp_zero N hN0 (circleParabolicH4 T τ U.1)
    (circleParabolicNemytskii T τ hδ hC hN0 htame U) hH
    ((circle_parabolic_nemytskii_tame T τ hδ hC hN0 htame).1 U)

set_option maxHeartbeats 800000 in
/-- Sufficiently small H2 initial data have a unique solution in a fixed
small closed ball of the actual parabolic space. The equation uses the
actual time-L2 Nemytskii term and the supplied actual linear PDE map. -/
theorem circle_parabolic_picard
    {δ C : ℝ} {N : CircleSobolevSpace T 4 → CircleL2 T}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hN0 : N 0 = 0)
    (htame : ∀ f g : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
      ‖N f-N g‖ ≤ C*
        ((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*
            ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖))
    (L : CircleParabolicSpace T τ →L[ℂ] CircleTimeL2 T)
    (e : CircleParabolicSpace T τ ≃L[ℂ]
      (CircleSobolevSpace T 2 × CircleTimeL2 T))
    (heInitial : ∀ U, (e U).1 = circleParabolicInitialValue T τ U)
    (hePDE : ∀ U, (e U).2 = L U) :
    let R := circleParabolicNemytskii T τ hδ hC hN0 htame
    ∃ ε > 0, ∃ r > 0, r < δ ∧
      ∀ u0 : CircleSobolevSpace T 2, ‖u0‖ ≤ ε →
        ∃! U : {U : CircleParabolicSpace T τ | ‖circleParabolicCurve T τ U‖ < δ},
          ‖U.1‖ ≤ r ∧ circleParabolicInitialValue T τ U.1 = u0 ∧ L U.1 = R U := by
  exact parabolic_picard_time T τ hδ hC
    (circleParabolicNemytskii T τ hδ hC hN0 htame)
    (parabolic_nemytskii_zero T τ hδ hC hN0 htame)
    (circle_parabolic_nemytskii_tame T τ hδ hC hN0 htame).2 L e heInitial hePDE

end Lemniscate
