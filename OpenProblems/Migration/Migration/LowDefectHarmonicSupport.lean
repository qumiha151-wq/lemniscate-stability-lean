import Migration.LowDefectMaterialCorrection

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.LowDefect.Tangent

theorem extremal_harmonic_phase {A e : ℂ} (unit : ‖e‖=1) :
    ∃x∈Ico (0:ℝ) 1, A*fourier 1 (x:AddCircle (1:ℝ))=‖A‖ • e := by
  by_cases nz : A=0
  · refine ⟨0,⟨le_rfl,by norm_num⟩,?_⟩
    simp [nz]
  let w : ℂ := ((‖A‖:ℝ):ℂ)*e/A
  have hw : ‖w‖=1 := by
    simp [w,unit,norm_ne_zero_iff.mpr nz]
  let W : Circle := ⟨w,by change w∈Metric.sphere 0 1; simpa [Metric.mem_sphere] using hw⟩
  let u := (AddCircle.homeomorphCircle (T:=1) (by norm_num)).symm W
  let v := AddCircle.equivIco (1:ℝ) 0 u
  refine ⟨v.val,by simpa using v.property,?_⟩
  have h : ((v.val:ℝ):AddCircle (1:ℝ))=u := AddCircle.coe_equivIco
  rw [h,fourier_one,←AddCircle.homeomorphCircle_apply (T:=1) (by norm_num)]
  simp only [u,Homeomorph.apply_symm_apply]
  change A*w=‖A‖ • e
  rw [Complex.real_smul]
  dsimp only [w]
  field_simp

theorem harmonic_support {G : ℝ→ℂ} {A : ℂ} {H : ℝ}
    (err : ∀x∈Ico (0:ℝ) 1, ‖G x-A*fourier 1 (x:AddCircle (1:ℝ))‖≤H)
    (e : ℂ) (unit : ‖e‖=1) :
    ∃x∈Ico (0:ℝ) 1, ‖A‖-H ≤ inner ℝ e (G x) := by
  obtain ⟨x,hx,hit⟩ := extremal_harmonic_phase (A:=A) unit
  have h := err x hx
  rw [hit] at h
  have CS := abs_real_inner_le_norm e (G x - ‖A‖ • e)
  rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,unit,one_pow,mul_one,one_mul] at CS
  exact ⟨x,hx,by linarith [(abs_le.mp (CS.trans h)).1]⟩

theorem harmonic_outer {G : ℝ→ℂ} {A : ℂ} {H : ℝ}
    (err : ∀x∈Ico (0:ℝ) 1, ‖G x-A*fourier 1 (x:AddCircle (1:ℝ))‖≤H) :
    ∀x∈Ico (0:ℝ) 1, ‖G x‖≤‖A‖+H := by
  intro x hx
  let h := A*fourier 1 (x:AddCircle (1:ℝ))
  have b := norm_sub_le_norm_sub_add_norm_sub (G x) h 0
  have en : ‖fourier 1 (x:AddCircle (1:ℝ))‖=1 := Circle.norm_coe _
  have hn : ‖h‖=‖A‖ := by dsimp only [h];rw [norm_mul,en,mul_one]
  simp only [sub_zero,hn] at b
  linarith [err x hx]

end MigrationGeometry.Flow.LowDefect.Tangent
#print axioms MigrationGeometry.Flow.LowDefect.Tangent.harmonic_support
