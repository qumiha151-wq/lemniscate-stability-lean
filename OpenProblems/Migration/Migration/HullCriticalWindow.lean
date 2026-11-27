import Migration.CenterInterior
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter
open scoped Topology
namespace MigrationGeometry.HullGap

abbrev State := Fin 8 → ℝ
def A := Real.sqrt (Real.sqrt 2)
def weight (z : State) := (A^2+(z 2)^2+(z 3)^2)/2
def density (z : State) := A^2+(z 0)^2/2+2*(z 3)^2+z 0*z 2*weight z
def velocity (z : State) : State :=
  ![z 1,-(z 0)^3/2-z 2,-z 0*z 3,1+z 0*z 2,z 5,z 0*z 6,-z 0*z 5,density z*z 4]

theorem A_sq : A^2=Real.sqrt 2 := Real.sq_sqrt (Real.sqrt_nonneg _)
theorem A_four : A^4=2 := by rw [show A^4=(A^2)^2 by ring,A_sq,Real.sq_sqrt (by norm_num)]
theorem A_lt : A<2 := by
  have h := A_four
  by_contra! g
  have p := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) g 4
  linarith

theorem density_nonnegative (z : State) (r : (z 2)^2+(z 3)^2≤A^2) :
    2*(z 3)^2 ≤ density z := by
  have w0 : 0≤weight z := by unfold weight; positivity
  have w1 : weight z≤A^2 := by unfold weight; linarith
  have h := mul_le_mul (show (z 2)^2≤A^2 by linarith [sq_nonneg (z 3)])
    (pow_le_pow_left₀ w0 w1 2) (sq_nonneg _) (sq_nonneg _)
  have B : A^2*(A^2)^2=2*A^2 := by rw [show (A^2)^2=A^4 by ring,A_four]; ring
  rw [B] at h
  unfold density
  nlinarith only [h,sq_nonneg (z 0+z 2*weight z)]

theorem velocity_continuous : Continuous velocity := by
  apply continuous_pi
  intro i
  fin_cases i <;> simp [velocity,density,weight] <;> fun_prop

/-- No critical-radius arc can stay in a closed half-plane during a six-unit
    forward window through a global maximum of its projected primitive. -/
theorem critical_window_impossible (z : ℝ → State) (cz : ContinuousOn z (Icc 0 6))
    (dz : ∀ s∈Ioo 0 6, ∀ i, HasDerivAt (fun t => z t i) (velocity (z s) i) s)
    (rad : ∀ s∈Icc 0 6, (z s 2)^2+(z s 3)^2≤A^2)
    (unit : ∀ s∈Icc 0 6, (z s 5)^2+(z s 6)^2=1)
    (height : ∀ s∈Icc 0 6, 0≤z s 4)
    (maximal : ∀ s∈Icc 0 6, z s 7≤z 0 7) : False := by
  let I := Icc (0:ℝ) 6
  let U := Ioo (0:ℝ) 6
  have inc (i : Fin 8) : ContinuousOn (fun s => z s i) I := (continuous_apply i).comp_continuousOn cz
  have sd (s : ℝ) (hs : s∈U) (i : Fin 8) := dz s hs i
  have mon : MonotoneOn (fun s => z s 7) I := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc ..) (inc 7)
    · intro t ht
      change t∈interior (Icc (0:ℝ) 6) at ht
      rw [interior_Icc] at ht
      exact (sd t ht 7).differentiableAt.differentiableWithinAt
    · intro t ht
      change t∈interior (Icc (0:ℝ) 6) at ht
      rw [interior_Icc] at ht
      rw [(sd t ht 7).deriv]
      change 0≤density (z t)*z t 4
      have hmem := Ioo_subset_Icc_self ht
      exact mul_nonneg ((by positivity : 0≤2*(z t 3)^2).trans (density_nonnegative _ (rad t hmem)))
        (height t hmem)
  have f7 (s : ℝ) (hs : s∈I) : z s 7=z 0 7 :=
    (maximal s hs).antisymm (mon (show (0:ℝ)∈I from ⟨le_rfl,by norm_num⟩) hs hs.1)
  have zero_near {i : Fin 8} {s c : ℝ} (hs : s∈U)
      (eq : (fun t => z t i) =ᶠ[𝓝 s] fun _ => c) : velocity (z s) i=0 :=
    (sd s hs i).unique ((hasDerivAt_const s _).congr_of_eventuallyEq eq)
  have prod (s : ℝ) (hs : s∈U) : density (z s)*z s 4=0 := by
    apply zero_near (i:=7) (c:=z 0 7) hs
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht using f7 t (Ioo_subset_Icc_self ht)
  have vanish (s : ℝ) (hs : s∈U) : z s 4=0 := by
    have hm := Ioo_subset_Icc_self hs
    by_contra ne
    have hp := (height s hm).lt_of_ne' ne
    have hu : U∈𝓝 s := Ioo_mem_nhds hs.1 hs.2
    have near := (sd s hs 4).continuousAt.eventually (lt_mem_nhds hp)
    have qnear : (fun t => z t 3) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [hu,near] with t ht hp'
      have d0 := (mul_eq_zero.mp (prod t ht)).resolve_right hp'.ne'
      have cap := density_nonnegative _ (rad t (Ioo_subset_Icc_self ht))
      rw [d0] at cap
      nlinarith [sq_nonneg (z t 3)]
    have kp : 1+z s 0*z s 2=0 := zero_near hs qnear
    have kn : z s 0≠0 := by intro eq; simp [eq] at kp
    have wz : weight (z s)≤A^2 := by unfold weight; linarith only [rad s hm]
    have d0 := (mul_eq_zero.mp (prod s hs)).resolve_right ne
    unfold density at d0
    rw [qnear.eq_of_nhds,show z s 0*z s 2= -1 by linarith only [kp]] at d0
    nlinarith only [d0,wz,sq_pos_of_ne_zero kn]
  have uy (s : ℝ) (hs : s∈U) : z s 5=0 := by
    apply zero_near (i:=4) (c:=0) hs
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht using vanish t ht
  have slope (s : ℝ) (hs : s∈U) : HasDerivAt (fun t => z t 3) 1 s := by
    have kn : z s 0*z s 6=0 := zero_near (i:=5) (c:=0) hs (by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht using uy t ht)
    have un := unit s (Ioo_subset_Icc_self hs)
    rw [uy s hs] at un
    have k0 := (mul_eq_zero.mp kn).resolve_right (fun hn => by simp [hn] at un)
    simpa [velocity,k0] using sd s hs 3
  have ints := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(1:ℝ)) (b:=5)
    (fun t (ht : t∈uIcc (1:ℝ) 5) => slope t (by
      rw [uIcc_of_le (by norm_num)] at ht
      exact ⟨by linarith only [ht.1],by linarith only [ht.2]⟩))
    (continuous_const.intervalIntegrable _ _)
  norm_num at ints
  have bounds (s : ℝ) (hs : s∈I) : |z s 3|≤A := by
    have h := rad s hs
    have nonneg : 0≤A := Real.sqrt_nonneg _
    rw [← abs_of_nonneg nonneg]
    apply (sq_le_sq).mp
    linarith [sq_nonneg (z s 2)]
  have one := (abs_le.mp (bounds 1 (by constructor <;> norm_num))).1
  have five := (abs_le.mp (bounds 5 (by constructor <;> norm_num))).2
  linarith only [one,five,ints,A_lt]

end MigrationGeometry.HullGap
#print axioms MigrationGeometry.HullGap.critical_window_impossible
