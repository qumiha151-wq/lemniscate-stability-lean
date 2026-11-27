import Migration.LowDefectPositionTail

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.LowDefect.Tangent

theorem fourier_recovery {G : ℝ→ℂ} (hg : Continuous G) (per : G 1=G 0)
    (hs : Summable (coeff G)) {x : ℝ} (hx : x∈Ico 0 1) :
    HasSum (fun n : ℤ=>coeff G n * fourier n (x : AddCircle (1:ℝ))) (G x) := by
  let F : C(AddCircle (1:ℝ),ℂ) :=
    ⟨AddCircle.liftIco 1 0 G,AddCircle.liftIco_zero_continuous per.symm hg.continuousOn⟩
  have id (n : ℤ) : fourierCoeff F n=coeff G n := by
    change fourierCoeff (AddCircle.liftIco 1 0 G) n=_
    simpa only [zero_add,coeff] using fourierCoeff_liftIco_eq (T:=1) (a:=0) G n
  have sm : Summable (fourierCoeff F) := by simpa only [funext id] using hs
  have h := has_pointwise_sum_fourier_series_of_summable sm (x : AddCircle (1:ℝ))
  have eql : F (x : AddCircle (1:ℝ))=G x := AddCircle.liftIco_coe_apply (by simpa using hx)
  simpa only [id,eql,smul_eq_mul] using h

/-- The actual position differs pointwise from its first position harmonic
by at most the square-root tail plus the quadratic second-mode contribution. -/
theorem position_harmonic_error {G T : ℝ→ℂ} {D : ℝ} (ct : Continuous T)
    (dg : ∀x,HasDerivAt G ((2*Real.pi:ℂ)*T x) x)
    (per : G 1=G 0) (zero : coeff G 0=0)
    (hd : HasSum (fun n : ℤ => ((n:ℝ)-1)^2*energy T n) D)
    (small : ‖coeff T 2‖≤(266/1000)*D) {x : ℝ} (hx : x∈Ico 0 1) :
    ‖G x-coeff G 1*fourier 1 (x : AddCircle (1:ℝ))‖≤
      (575/1000)*Real.sqrt D+(133/1000)*D := by
  have cg : Continuous G := continuous_iff_continuousAt.mpr fun s=>(dg s).continuousAt
  obtain ⟨tail,bt⟩ := far_position_bound ct dg per hd
  have v2 : ‖coeff G 2‖≤(133/1000)*D := by
    rw [position_coefficient ct dg per (by decide : (2:ℤ)≠0)]
    norm_num [norm_mul,norm_div]
    linarith
  let e := fun n : ℤ=>fourier n (x : AddCircle (1:ℝ))
  have en (n : ℤ) : ‖e n‖=1 := Circle.norm_coe _
  let r := fun n : ℤ=>if n=1 then (0:ℂ) else coeff G n*e n
  have s2 : HasSum (fun n : ℤ=>if n=2 then ‖coeff G 2‖ else 0) ‖coeff G 2‖ := by
    simpa [eq_comm] using hasSum_ite_eq (2:ℤ) ‖coeff G 2‖
  have eq (n : ℤ) : ‖r n‖=farSize G n+(if n=2 then ‖coeff G 2‖ else 0) := by
    by_cases h0 : n=0
    · simp [r,farSize,h0,zero]
    by_cases h1 : n=1
    · simp [r,farSize,h1]
    by_cases h2 : n=2
    · simp [r,farSize,h2,en]
    simp [r,farSize,h0,h1,h2,en]
  have normsum : HasSum (fun n=>‖r n‖) ((∑'n,farSize G n)+‖coeff G 2‖) := by
    simpa only [eq] using tail.hasSum.add s2
  have s1 : HasSum (fun n : ℤ=>if n=1 then ‖coeff G 1‖ else 0) ‖coeff G 1‖ := by
    simpa [eq_comm] using hasSum_ite_eq (1:ℤ) ‖coeff G 1‖
  have normcoeff : Summable (fun n=>‖coeff G n‖) := by
    apply (normsum.summable.add s1.summable).congr
    intro n
    by_cases h : n=1 <;> simp [r,h,en]
  have recovery := fourier_recovery cg per normcoeff.of_norm hx
  have z : HasSum (fun n : ℤ=>if n=1 then coeff G 1*e 1 else 0) (coeff G 1*e 1) := by
    simpa [eq_comm] using hasSum_ite_eq (1:ℤ) (coeff G 1*e 1)
  have sum : HasSum r (G x-coeff G 1*e 1) := by
    apply (recovery.sub z).congr_fun
    intro n
    change (if n=1 then 0 else coeff G n*e n)=coeff G n*e n-(if n=1 then coeff G 1*e 1 else 0)
    by_cases h : n=1 <;> simp only [h,if_true,if_false,sub_self,sub_zero]
  have b := norm_tsum_le_tsum_norm normsum.summable
  rw [sum.tsum_eq,normsum.tsum_eq] at b
  exact b.trans (by linarith)

end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.position_harmonic_error
