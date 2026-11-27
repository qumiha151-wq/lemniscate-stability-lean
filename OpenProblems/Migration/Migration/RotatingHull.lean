import Migration.PolarOscillation
import Migration.EscapingHulls

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Rotating.UnitLoop
variable {L : ℝ} (c : UnitLoop L)

def traceSet := (fun s => (c.x s:ℂ)+(c.y s:ℂ)*Complex.I) '' Icc 0 L
def coords (z : ℂ) : Fin 2 → ℝ := ![z.re,z.im]

theorem exterior_separator {z : ℂ} (lp : 0<L) (out : z ∉ convexHull ℝ c.traceSet) :
    ∃ A B : ℝ,A^2+B^2=1 ∧ ∀s,0<c.forward (coords z) A B s := by
  have cc : IsCompact c.traceSet :=
    isCompact_Icc.image ((Complex.continuous_ofReal.comp c.hx.continuous).add
      ((Complex.continuous_ofReal.comp c.hy.continuous).mul continuous_const))
  obtain ⟨f,l,low,hi⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ c.traceSet)
    (SimilarityHull.compact_convexHull cc).isClosed out
  have both : SimilarityHull.separated {z} c.traceSet :=
    ⟨f,l,fun u hu => by simpa only [Set.mem_singleton_iff.mp hu] using low,
      fun u hu => hi u (subset_convexHull ℝ _ hu)⟩
  have ne : c.traceSet.Nonempty := ⟨_,0,⟨le_rfl,lp.le⟩,rfl⟩
  obtain ⟨e,en,r,one,many⟩ := (SimilarityHull.separated_iff_unit_height (singleton_nonempty _) ne).mp both
  have norm := e.sq_norm
  rw [en,Complex.normSq_apply] at norm
  refine ⟨e.re,e.im,by nlinarith only [norm],?_⟩
  have per : Function.Periodic (c.forward (coords z) e.re e.im) L := by
    intro s; simp only [forward,c.px s,c.py s]
  intro s
  obtain ⟨t,ht,eq⟩ := per.exists_mem_Ico₀ lp s
  rw [eq]
  have gt := (one z (mem_singleton _)).trans (many _ ⟨t,Ico_subset_Icc_self ht,rfl⟩)
  simp only [Complex.inner,Complex.add_re,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,sub_zero,add_zero,zero_add] at gt
  change 0<e.re*(c.x t-z.re)+e.im*(c.y t-z.im)
  linarith only [gt]

theorem half_aperture {d : Fin 2 → ℝ} {A B : ℝ} (lp : 0<L)
    (unit : A^2+B^2=1) (sep : ∀s,0<c.forward d A B s) :
    ∃ m h : ℝ, 0≤h ∧ h<Real.pi/2 ∧
      (∀s∈Icc 0 L, |c.angle d A B s-m|≤h) := by
  let θ := c.angle d A B
  have ct : Continuous θ := continuous_iff_continuousAt.mpr fun s =>
    (c.angleD unit (sep s)).continuousAt
  obtain ⟨lo,hlo,mn⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr lp.le) ct.continuousOn
  obtain ⟨hi,hhi,mx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr lp.le) ct.continuousOn
  refine ⟨(θ hi+θ lo)/2,(θ hi-θ lo)/2,div_nonneg (sub_nonneg.mpr (mn hhi)) (by norm_num),?_,?_⟩
  · have left : -(Real.pi/2)<θ lo := Real.neg_pi_div_two_lt_arctan _
    have right : θ hi<Real.pi/2 := Real.arctan_lt_pi_div_two _
    linarith only [left,right]
  · intro s hs
    change |θ s-(θ hi+θ lo)/2|≤_
    rw [abs_le]
    have l : θ lo ≤ θ s := mn hs
    have h : θ s ≤ θ hi := mx hs
    exact ⟨by linarith only [l],by linarith only [h]⟩

/-- Under strict separation, the angular velocity relative to dilation
is bounded by the enclosing squared radius and the actual angle bound. -/
theorem exterior_pitch_bound {a b A B m h M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (unit : A^2+B^2=1) (sep : ∀s,0<c.forward 0 A B s)
    (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (osc : ∀s∈Icc 0 L,|c.angle 0 A B s-m|≤h) :
    4*b^2≤M^2*h^2*(2*a) ∧ M≠0 := by
  let Z := mass (L:=L) (c.mixed b)
  let Q := mass (L:=L) (c.q 0)
  obtain ⟨fk,fp,_,zp⟩ := c.balances ap lp sol
  have pol := c.polar_mass_bound lp unit sep cap osc
  rw [fk,fp] at pol
  change (Z+b^2*Q)^2≤M^2*h^2*(2*a*Z)*Q at pol
  change 0<Z at zp
  have qn : 0≤Q := intervalIntegral.integral_nonneg lp.le (fun _ _ => sq_nonneg _)
  have pp : 0<Z+b^2*Q := add_pos_of_pos_of_nonneg zp (mul_nonneg (sq_nonneg b) qn)
  have qp : 0<Q := lt_of_le_of_ne qn (by
    intro bad
    rw [← bad] at pol
    simp only [mul_zero,add_zero,not_le.mpr (sq_pos_of_pos zp)] at pol)
  constructor
  · apply le_of_mul_le_mul_right (a:=Z*Q) _ (mul_pos zp qp)
    nlinarith only [pol,sq_nonneg (Z-b^2*Q)]
  · intro bad
    rw [bad] at pol
    simp only [zero_pow (by decide : 2≠0),zero_mul] at pol
    exact (not_le_of_gt (sq_pos_of_pos pp)) pol

/-- A high rotation-to-dilation ratio forces the expansion centre into
the actual convex hull of every profile within the given radius. -/
theorem center_mem_hull_of_pitch {a b M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (pitch : Real.pi^2*M^2*(2*a)≤16*b^2) : (0:ℂ) ∈ convexHull ℝ c.traceSet := by
  by_contra outside
  obtain ⟨A,B,unit,sep'⟩ := c.exterior_separator lp outside
  have co : coords 0=0 := by funext i; fin_cases i <;> rfl
  rw [co] at sep'
  obtain ⟨m,h,hn,hp,osc⟩ := c.half_aperture lp unit sep'
  obtain ⟨ineq,Mne⟩ := c.exterior_pitch_bound ap lp sol unit sep' cap osc
  have addp := add_pos_of_pos_of_nonneg (div_pos Real.pi_pos (by norm_num : (0:ℝ)<2)) hn
  have hs : h^2<(Real.pi/2)^2 := by nlinarith only [mul_pos (sub_pos.mpr hp) addp]
  have strict := mul_lt_mul_of_pos_left hs (mul_pos (sq_pos_of_ne_zero Mne) (by linarith only [ap] : 0<2*a))
  nlinarith only [ineq,strict,pitch]

/-- No two time slices can occupy opposite open half-planes. -/
theorem no_migration_of_pitch {a b M : ℝ} (ap : 0<a) (lp : 0<L)
    (sol : c.IsRotating a b) (cap : ∀s∈Icc 0 L,c.radialSq 0 s≤M)
    (pitch : Real.pi^2*M^2*(2*a)≤16*b^2) (v w : ℂ) :
    ¬SimilarityHull.separated (SimilarityHull.directSimilarity 0 v '' c.traceSet)
      (SimilarityHull.directSimilarity 0 w '' c.traceSet) := by
  have origin := c.center_mem_hull_of_pitch ap lp sol cap pitch
  exact SimilarityHull.not_separated_of_common_hull (SimilarityHull.center_mem_direct_hull origin v)
    (SimilarityHull.center_mem_direct_hull origin w)

end MigrationGeometry.Rotating.UnitLoop
#print axioms MigrationGeometry.Rotating.UnitLoop.center_mem_hull_of_pitch
#print axioms MigrationGeometry.Rotating.UnitLoop.no_migration_of_pitch
