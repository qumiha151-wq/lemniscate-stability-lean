import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
namespace ClosedSimilarity.FrozenStress.Incoming
open Set

/-- A compact two-parameter seam family carries one bounded real lift of its
    oscillator phase even if it crosses the same branch cut many times. -/
theorem rectangle_angle_lift {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (f : Icc a b × Icc c d → Circle) (hf : Continuous f) :
    ∃ θ : Icc a b × Icc c d → ℝ, Continuous θ ∧ (∀ z, Circle.exp (θ z) = f z) ∧
      ∃ M : ℝ, ∀ z, |θ z| ≤ M := by
  let X := Icc a b × Icc c d
  let Y := Icc (0:ℝ) 1
  let grid : ℝ × ℝ → X := fun p => (projIcc a b hab p.1,projIcc c d hcd p.2)
  have cg : Continuous grid := (continuous_projIcc.comp continuous_fst).prodMk (continuous_projIcc.comp continuous_snd)
  let H := fun y : Y × X => f (grid ((y.1:ℝ)*(y.2.1:ℝ),(y.1:ℝ)*(y.2.2:ℝ)))
  have cH : Continuous H := by
    have c1 : Continuous (fun y : Y × X => (y.1:ℝ)) := continuous_subtype_val.comp continuous_fst
    have c2 : Continuous (fun y : Y × X => (y.2.1:ℝ)) := continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have c3 : Continuous (fun y : Y × X => (y.2.2:ℝ)) := continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact hf.comp (cg.comp ((c1.mul c2).prodMk (c1.mul c3)))
  let G := fun w : (Y × Y) × X => ((H (w.1.1,w.2)/H (w.1.2,w.2) : Circle):ℂ).re
  have cG : Continuous G := by
    apply Complex.continuous_re.comp
    apply continuous_subtype_val.comp
    exact (cH.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).div'
      (cH.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨δ,hδ,modulus⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous cG) 1 zero_lt_one
  obtain ⟨m,hm⟩ := exists_nat_one_div_lt hδ
  let N := m+1
  have np : (0:ℝ)<N := by dsimp [N]; positivity
  let tick := fun (i : ℕ) => (⟨(min i N : ℕ)/(N:ℝ),div_nonneg (Nat.cast_nonneg _) np.le,
    (div_le_one np).mpr (by exact_mod_cast min_le_right i N)⟩ : Y)
  let F := fun (i : ℕ) (z : X) => H (tick i,z)
  have cF (i : ℕ) : Continuous (F i) := cH.comp (continuous_const.prodMk continuous_id)
  let inc := fun (i : ℕ) (z : X) => F (i+1) z/F i z
  have cI (i : ℕ) : Continuous (inc i) := (cF _).div' (cF _)
  have positive (i : ℕ) (hi : i<N) (z : X) : 0<((inc i z:Circle):ℂ).re := by
    have step : dist (tick (i+1)) (tick i) < δ := by
      change |(min (i+1) N:ℕ)/(N:ℝ)-(min i N:ℕ)/(N:ℝ)|<δ
      rw [min_eq_left (Nat.succ_le_of_lt hi),min_eq_left hi.le,Nat.cast_succ,add_div,add_sub_cancel_left,
        abs_of_pos (by positivity)]
      simpa [N] using hm
    have near : dist (((tick (i+1),tick i),z) : (Y×Y)×X) ((tick i,tick i),z) < δ :=
      max_lt (max_lt step (by simpa using hδ)) (by simpa using hδ)
    have n := modulus near
    change |G ((tick (i+1),tick i),z)-G ((tick i,tick i),z)|<1 at n
    have one : G ((tick i,tick i),z)=1 := by simp [G]
    rw [one] at n
    exact sub_pos.mp (by have h := (abs_lt.mp n).1; change 0 < G ((tick (i+1),tick i),z)-0; linarith)
  have lift (i : ℕ) (hi : i≤N) : ∃ p : X→ℝ, Continuous p ∧ ∀z,Circle.exp (p z)=F i z := by
    induction i with
    | zero =>
      let q := f (grid (0,0))
      refine ⟨fun _ => (q:ℂ).arg,continuous_const,?_⟩
      intro z
      simp [q,F,H,tick]
    | succ i ih =>
      obtain ⟨p,cp,ep⟩ := ih (Nat.le_of_succ_le hi)
      have carg : Continuous (fun z => ((inc i z:Circle):ℂ).arg) := by
        apply continuous_iff_continuousAt.mpr
        intro z
        exact ContinuousAt.comp (f:=fun x : X => (inc i x:ℂ)) (x:=z)
          (Complex.continuousAt_arg (Or.inl (positive i hi z)))
          (continuous_subtype_val.comp (cI i)).continuousAt
      refine ⟨fun z => p z + ((inc i z:Circle):ℂ).arg,cp.add carg,?_⟩
      intro z
      rw [Circle.exp_add,ep,Circle.exp_arg]
      dsimp only [inc]
      rw [mul_comm,div_mul_cancel]
  obtain ⟨θ,co,hθ⟩ := lift N le_rfl
  refine ⟨θ,co,?_,?_⟩
  · intro z
    simpa [F,H,grid,tick,np.ne',projIcc_of_mem] using hθ z
  · obtain ⟨M,hM⟩ := isCompact_univ.bddAbove_image co.abs.continuousOn
    exact ⟨M,fun z => hM ⟨z,mem_univ _,rfl⟩⟩

theorem oscillator_angle_lift {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (U w : Icc a b × Icc c d → ℝ) (hU : Continuous U) (hw : Continuous w)
    (oval : ∀ z, ((U z)^2/2)^2+(w z)^2=1) :
    ∃ θ : Icc a b × Icc c d → ℝ, Continuous θ ∧
      (∀ z, Real.sin (θ z)=U z/Real.sqrt 2 ∧
        Real.cos (θ z)=w z/Real.sqrt (1+(U z)^2/2)) ∧ ∃ M : ℝ, ∀ z, |θ z| ≤ M := by
  let sn := fun z => U z/Real.sqrt 2
  let cs := fun z => w z/Real.sqrt (1+(U z)^2/2)
  have unit (z) : (cs z)^2+(sn z)^2=1 := by
    dsimp [cs,sn]
    rw [div_pow,div_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt (by norm_num)]
    field_simp
    nlinarith only [oval z]
  let f (z) : Circle := ⟨⟨cs z,sn z⟩,mem_sphere_zero_iff_norm.mpr (by
    rw [Complex.norm_def]
    change Real.sqrt (cs z*cs z+sn z*sn z) = 1
    rw [show cs z*cs z+sn z*sn z=1 by simpa [pow_two] using unit z,Real.sqrt_one])⟩
  have hcs : Continuous cs :=
    hw.div ((continuous_const.add ((hU.pow 2).div_const 2)).sqrt) (fun _ => by positivity)
  have hsn : Continuous sn := hU.div_const _
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    have id (z) : (⟨cs z,sn z⟩ : ℂ) = (cs z:ℂ)+(sn z:ℂ)*Complex.I := by apply Complex.ext <;> simp
    simp only [id]
    exact (Complex.continuous_ofReal.comp hcs).add ((Complex.continuous_ofReal.comp hsn).mul
      (continuous_const (y:=Complex.I)))
  obtain ⟨θ,co,ph,bound⟩ := rectangle_angle_lift hab hcd f hc
  refine ⟨θ,co,?_,bound⟩
  intro z
  have e := congrArg (fun t : Circle => (t:ℂ)) (ph z)
  rw [Circle.coe_exp,Complex.exp_mul_I] at e
  exact ⟨by simpa [f,sn,←Complex.ofReal_sin,←Complex.ofReal_cos] using congrArg Complex.im e,
    by simpa [f,cs,←Complex.ofReal_sin,←Complex.ofReal_cos] using congrArg Complex.re e⟩

end ClosedSimilarity.FrozenStress.Incoming
#print axioms ClosedSimilarity.FrozenStress.Incoming.oscillator_angle_lift
