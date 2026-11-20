import LengthGrowth.ActualFlow.ArclengthCoercivity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Order.Interval.Set.Disjoint

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The integral of the actual Frenet curvature rotates the initial
unit tangent to the tangent at the other endpoint. -/
theorem tangent_eq_exp_integral_curvature (a b : ℝ) :
    c.tangent b=Complex.exp (((∫s in a..b,c.curvature s):ℝ)*Complex.I)*c.tangent a := by
  let θ:ℝ→ℝ := fun s=>∫z in a..s,c.curvature z
  have dθ (s:ℝ) : HasDerivAt θ (c.curvature s) s :=
    intervalIntegral.integral_hasDerivAt_right (c.curvature_continuous.intervalIntegrable a s)
      c.curvature_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter c.curvature_continuous.continuousAt
  let H:=fun s=>Complex.exp (-((θ s:ℂ)*Complex.I))*c.tangent s
  have hd (s:ℝ) : HasDerivAt H 0 s := by
    change HasDerivAt (fun x=>Complex.exp (-((θ x:ℂ)*Complex.I))*c.tangent x) 0 s
    convert! ((((dθ s).ofReal_comp.mul_const Complex.I).neg.cexp).mul (c.tangent_deriv s)) using 1
    ring
  have eq:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b) (fun s _=>hd s)
    (intervalIntegrable_const (c:=(0:ℂ)))
  have θa : θ a=0:=by simp [θ]
  simp only [intervalIntegral.integral_zero,H,θa,Complex.ofReal_zero,zero_mul,neg_zero,
    Complex.exp_zero,one_mul] at eq
  have hh:=eq_sub_iff_add_eq.mp eq
  simp only [zero_add] at hh
  change c.tangent b=Complex.exp ((θ b:ℂ)*Complex.I)*c.tangent a
  rw [hh,←mul_assoc,←Complex.exp_add,add_neg_cancel,Complex.exp_zero,one_mul]

/-- A macroscopic net turn contains two tangents a fixed chord apart,
regardless of extra small oscillations and full rotations in the arc. -/
theorem tangent_chord_of_net_turn {a b δ:ℝ} (ab:a≤b) (hp:0<δ) (hπ:δ<Real.pi)
    (turn : δ≤|∫s in a..b,c.curvature s|) :
    ∃x∈Icc a b, Real.sin δ≤‖c.tangent x-c.tangent a‖ := by
  let θ:ℝ→ℝ:= fun s=>∫z in a..s,c.curvature z
  have dθ (s:ℝ) : HasDerivAt θ (c.curvature s) s :=
    intervalIntegral.integral_hasDerivAt_right (c.curvature_continuous.intervalIntegrable a s)
      c.curvature_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter c.curvature_continuous.continuousAt
  have cont:Continuous θ:=continuous_iff_continuousAt.mpr (fun s=>(dθ s).continuousAt)
  have hδ : δ∈Icc |θ a| |θ b| := ⟨by simpa [θ] using hp.le,turn⟩
  obtain ⟨x,hx,hval⟩:=intermediate_value_Icc ab cont.abs.continuousOn hδ
  have eq:=c.tangent_eq_exp_integral_curvature a x
  change c.tangent x=Complex.exp ((θ x:ℂ)*Complex.I)*c.tangent a at eq
  have chord : c.tangent x-c.tangent a = (Complex.exp ((θ x:ℂ)*Complex.I)-1)*c.tangent a := by
    rw [eq]; ring
  refine ⟨x,hx,?_⟩
  rw [chord,norm_mul,c.tangent_unit,mul_one]
  have im:=Complex.abs_im_le_norm (Complex.exp ((θ x:ℂ)*Complex.I)-1)
  rw [Complex.sub_im,Complex.exp_ofReal_mul_I_im,Complex.one_im,sub_zero] at im
  rcases (abs_eq hp.le).mp hval with h|h
  · simpa [h,abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hp hπ)] using im
  · simpa [h,abs_of_pos (Real.sin_pos_of_pos_of_lt_pi hp hπ)] using im

/-- One common modulus at the fixed chord amplitude controls the total
arc count. The increasing coordinate can be different on every slice. -/
theorem packing_le_inverse_modulus {a δ η : ℝ} (dp : 0<δ) (dπ : δ<Real.pi)
    (hp : 0<η) {φ : ℝ→ℝ} (mon : StrictMono φ)
    (period : ∀x,φ (x+c.period)=φ x+1)
    (modulus : ∀x y : ℝ,x≤y → φ y-φ x≤η → ‖c.tangent y-c.tangent x‖<Real.sin δ)
    (S : Finset (ℝ×ℝ))
    (arc : ∀I∈S,a≤I.1 ∧ I.1<I.2 ∧ I.2≤a+c.period ∧ δ≤|∫s in I.1..I.2,c.curvature s|)
    (sep : ∀I∈S,∀J∈S,I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2)) :
    (S.card:ℝ)≤1/η := by
  classical
  let U:=fun I:ℝ×ℝ=>Ioo (φ I.1) (φ I.2)
  have dis : (S:Set (ℝ×ℝ)).PairwiseDisjoint U := by
    intro I hi J hj ne
    apply Ioo_disjoint_Ioo.mpr
    have ord:=Ioo_disjoint_Ioo.mp (sep I hi J hj ne)
    simpa only [mon.monotone.map_min,mon.monotone.map_max] using mon.monotone ord
  have size:=measureReal_biUnion_finset (μ:=volume) dis (fun _ _=>measurableSet_Ioo)
    (fun _ _=>measure_Ioo_lt_top.ne)
  have sub : (⋃I∈S,U I)⊆Ioo (φ a) (φ a+1) := by
    intro x hx
    obtain ⟨I,hi⟩:=mem_iUnion.mp hx
    obtain ⟨hit,hx⟩:=mem_iUnion.mp hi
    have ar:=arc I hit
    refine ⟨(mon.monotone ar.1).trans_lt hx.1,?_⟩
    rw [←period a]
    exact hx.2.trans_le (mon.monotone ar.2.2.1)
  have budget:=measureReal_mono (μ:=volume) sub (measure_Ioo_lt_top.ne)
  rw [Real.volume_real_Ioo_of_le (by linarith),size] at budget
  have widths (I : ℝ×ℝ) (hi : I∈S) : η≤volume.real (U I) := by
    obtain ⟨_,lr,_,turn⟩:=arc I hi
    obtain ⟨x,hx,ch⟩:=c.tangent_chord_of_net_turn lr.le dp dπ turn
    change η≤volume.real (Ioo (φ I.1) (φ I.2))
    rw [Real.volume_real_Ioo_of_le (mon.monotone lr.le)]
    by_contra! small
    exact (not_lt_of_ge ch) (modulus I.1 x hx.1 (by linarith [mon.monotone hx.2]))
  have sum:=Finset.sum_le_sum widths
  exact (le_div_iff₀ hp).mpr (by simpa using sum.trans budget)

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.tangent_chord_of_net_turn
#print axioms LengthGrowth.ClosedFrenetCurve.packing_le_inverse_modulus
