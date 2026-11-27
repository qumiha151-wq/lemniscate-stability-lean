import Migration.NormTransport

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

/-- An explicit disk contained in the convex hull. Here r is measured
in physical coordinates and D in units of the canonical expander length. -/
theorem disk_mem_hull_of_pitch {a b R r : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (rp : 0≤r) (Rp : 0≤R)
    (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤R^2)
    (D : ℝ) (scale : r*Real.sqrt (Real.sqrt (2*a))≤D) (small : D<1)
    (pitch : (R+r)^2*(Real.pi/2)*Real.sqrt (2*a)*(1+2*(abs b)*D)<2*(abs b)*(1-D)^2) :
    Metric.closedBall (0:ℂ) r ⊆ convexHull ℝ c.traceSet := by
  intro u hu
  by_contra outside
  let d := coords u
  have df : d 0^2+d 1^2≤r^2 := by
    have n : ‖u‖≤r := by simpa only [Metric.mem_closedBall,dist_zero_right] using hu
    have h := u.sq_norm
    rw [Complex.normSq_apply] at h
    change u.re^2+u.im^2≤r^2
    nlinarith only [h,pow_le_pow_left₀ (norm_nonneg u) n 2]
  let z := size (L:=L) (c.mixed b)
  let p := size (L:=L) (c.p 0)
  let q := size (L:=L) (c.q 0)
  let k := size (L:=L) c.k
  let t := Real.sqrt (2*a)
  let pd := size (L:=L) (c.p d)
  let qd := size (L:=L) (c.q d)
  let M := (R+r)^2
  have ts : t^2=2*a := Real.sq_sqrt (by linarith only [ap])
  have tp : 0≤t := Real.sqrt_nonneg _
  have pn : 0≤p := Real.sqrt_nonneg _
  have qn : 0≤q := Real.sqrt_nonneg _
  have zn : 0≤z := Real.sqrt_nonneg _
  have bn := abs_nonneg b
  have qdn : 0≤qd := Real.sqrt_nonneg _
  have mn : 0≤M := sq_nonneg _
  obtain ⟨fk,fp,cs,zpos⟩ := c.balances ap lp sol
  have hks : k^2=t^2*z^2 := by
    change size (L:=L) c.k^2=t^2*size (L:=L) (c.mixed b)^2
    rw [size_sq lp.le,size_sq lp.le,ts,fk]
  have ke : k=t*z := by
    have he : k^2=(t*z)^2 := by rw [mul_pow,hks]
    exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg tp zn)).mp he
  have ps : p^2=z^2+b^2*q^2 := by
    change size (L:=L) (c.p 0)^2=size (L:=L) (c.mixed b)^2+b^2*size (L:=L) (c.q 0)^2
    rw [size_sq lp.le,size_sq lp.le,size_sq lp.le,fp]
  have zp : 0<z := Real.sqrt_pos.mpr zpos
  have zle : z≤p := le_of_sq_le_sq (by nlinarith only [ps,mul_nonneg (sq_nonneg b) (sq_nonneg q)]) pn
  have pp := lt_of_lt_of_le zp zle
  have am : 2*(abs b)*(z*q)≤p^2 := by
    have h := sq_nonneg (z-(abs b)*q)
    nlinarith only [h,ps,show (abs b)^2*q^2=b^2*q^2 by rw [sq_abs]]
  have lbound : Real.sqrt L≤Real.sqrt t*z := by
    have cs' : L^2≤k^2*z^2 := by
      change L^2≤size (L:=L) c.k^2*size (L:=L) (c.mixed b)^2
      rw [size_sq lp.le,size_sq lp.le]; exact cs
    have bound : L≤t*z^2 := by
      apply le_of_sq_le_sq _ (mul_nonneg tp (sq_nonneg _))
      nlinarith only [cs',hks,show k^2*z^2=t^2*z^2*z^2 by rw [hks]]
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) zn)
    rw [Real.sq_sqrt lp.le,mul_pow,Real.sq_sqrt tp]; exact bound
  have shift : r*Real.sqrt L≤D*z := calc
    _ ≤ r*(Real.sqrt t*z) := mul_le_mul_of_nonneg_left lbound rp
    _ = (r*Real.sqrt t)*z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right scale zn
  have Dn : 0≤D := (mul_nonneg rp (Real.sqrt_nonneg _)).trans scale
  obtain ⟨sp,sq⟩ := c.moved_support_bounds lp.le rp df
  change p≤pd+r*Real.sqrt L at sp
  change qd≤q+r*Real.sqrt L at sq
  have pdlo : (1-D)*p≤pd := by linarith only [sp,shift,mul_le_mul_of_nonneg_left zle Dn]
  have qdhi : qd≤q+D*z := by linarith only [sq,shift]
  obtain ⟨A,B,unit,sep⟩ := c.exterior_separator lp outside
  obtain ⟨m,h,hn,ht,osc⟩ := c.half_aperture lp unit sep
  have pol := c.polar_mass_bound lp unit sep (c.moved_radius_bound rp Rp df cap) osc
  have bd : pd^2≤M*h*k*qd := by
    apply le_of_sq_le_sq _ (mul_nonneg (mul_nonneg (mul_nonneg mn hn) (Real.sqrt_nonneg _)) qdn)
    change (size (L:=L) (c.p d)^2)^2≤(M*h*size (L:=L) c.k*size (L:=L) (c.q d))^2
    rw [mul_pow,mul_pow,mul_pow,size_sq lp.le,size_sq lp.le,size_sq lp.le]
    exact pol
  have one : (1-D)^2*p^2≤M*(Real.pi/2)*t*(z*(q+D*z)) := calc
    _ ≤ pd^2 := by rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr small.le) pn) pdlo 2
    _ ≤ M*h*k*qd := bd
    _ ≤ M*(Real.pi/2)*k*qd := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht.le mn) (Real.sqrt_nonneg _)) qdn
    _ ≤ M*(Real.pi/2)*k*(q+D*z) := mul_le_mul_of_nonneg_left qdhi
      (mul_nonneg (mul_nonneg mn (by positivity)) (Real.sqrt_nonneg _))
    _ = _ := by rw [ke]; ring
  have zz := pow_le_pow_left₀ zn zle 2
  have sqterm : 2*(abs b)*(z*(q+D*z)) ≤ (1+2*(abs b)*D)*p^2 := by
    have cmp := mul_le_mul_of_nonneg_left zz (mul_nonneg (mul_nonneg (by norm_num : 0≤(2:ℝ)) bn) Dn)
    nlinarith only [am,cmp]
  have final : (2*(abs b)*(1-D)^2)*p^2 ≤ (M*(Real.pi/2)*t*(1+2*(abs b)*D))*p^2 := calc
    _ ≤ 2*(abs b)*(M*(Real.pi/2)*t*(z*(q+D*z))) := by
      rw [mul_assoc (2*(abs b))]; exact mul_le_mul_of_nonneg_left one (by positivity)
    _ = (M*(Real.pi/2)*t)*(2*(abs b)*(z*(q+D*z))) := by ring
    _ ≤ (M*(Real.pi/2)*t)*((1+2*(abs b)*D)*p^2) := mul_le_mul_of_nonneg_left sqterm
      (mul_nonneg (mul_nonneg mn (by positivity)) tp)
    _ = _ := by ring
  exact (not_le_of_gt pitch) (le_of_mul_le_mul_right final (sq_pos_of_pos pp))

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.disk_mem_hull_of_pitch
