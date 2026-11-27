import Migration.VirialPhysicalCorrelation
import Migration.DirectionalWidth

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem virial_common_disk_on_slab (hf : c.IsNormalFEF) {s t : ℝ} (st : s≤t) (slab : Icc s t⊆I)
    (turn : ∀v∈Icc s t,c.signedCurvatureIntegral v=2*Real.pi)
    (energy : ∀v∈Icc s t,2*c.bending v*c.coreLength v≤5*Real.pi^2) :
    Metric.closedBall (c.arclengthCentroid s)
      ((80/100)*Real.pi/c.bending s+(2/1000)*Real.pi/c.bending t) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  let a:=2*Real.pi
  let D:=fun v=>c.curvatureOscillation (2*Real.pi) v/(2*Real.pi)^2
  let x:=fun v=>Real.sqrt (D v)
  have ap : 0<a := by dsimp [a];positivity
  have dp v (hv : v∈Icc s t) : 0≤D v := div_nonneg (c.curvatureOscillation_nonneg (slab hv) _) (sq_nonneg _)
  have small v (hv : v∈Icc s t) : D v≤1/4 := by
    have eq:=c.oscillation_energy_identity (slab hv) (turn v hv)
    change _/(2*Real.pi)^2≤_
    rw [div_le_iff₀ (by positivity)]
    nlinarith only [eq,energy v hv]
  have xs v (hv : v∈Icc s t) : x v^2=D v := Real.sq_sqrt (dp v hv)
  have xhi v (hv : v∈Icc s t) : x v≤1/2 := by nlinarith only [xs v hv,small v hv,sq_nonneg (x v-1/2)]
  have prod v (hv : v∈Icc s t) : c.bending v*c.coreLength v=2*Real.pi^2*(1+(x v)^2) := by
    rw [xs v hv]
    have eq:=c.oscillation_energy_identity (slab hv) (turn v hv)
    dsimp only [D];field_simp [Real.pi_ne_zero];nlinarith only [eq]
  have pos v (hv : v∈Icc s t) : 0<c.bending v := c.bending_pos_of_width (slab hv)
  have rate (e : ℂ) (he : ‖e‖=1) (v : ℝ) (hv : v∈Icc s t) :
      |c.centroidRate (innerSL ℝ e) v|≤(80/100*Real.pi)*c.localDissipation (innerSL ℝ e) (fun _=>1) v/c.bending v^2 := by
    let H:=innerSL ℝ e
    let L:=c.coreLength v
    let E:=c.bending v
    let J:=c.centeredSupportMoment v
    let M:=c.centroidFluxMoment H v
    let C:=c.supportFluxCorrelation H v
    let Y:=c.localDissipation H (fun _=>1) v
    let q:=x v*(1755/1000+575/1000*x v+140/1000*(x v)^2)
    let z:=95/100*(D v)
    have lp : 0<L := c.coreLength_pos (slab hv)
    have ep : 0<E := pos v hv
    have yp : 0≤Y := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u=>mul_nonneg (sq_nonneg _) (speed_pos (c.immersion v (slab hv)) u).le)
    have jp : 0≤J := intervalIntegral.integral_nonneg_of_forall c.period_pos.le
      (fun u=>mul_nonneg (sq_nonneg _) (speed_pos (c.immersion v (slab hv)) u).le)
    have j : a*Real.sqrt J≤L*Real.sqrt L := by
      apply le_of_sq_le_sq _ (by positivity)
      rw [mul_pow a,mul_pow L,Real.sq_sqrt jp,Real.sq_sqrt lp.le]
      have W:=c.centered_support_wirtinger (slab hv)
      change a^2*J≤L^3 at W
      linarith only [W,show L^2*L=L^3 by ring]
    have qb : 0≤q := by dsimp [q,x];positivity
    have zbound:=c.quarter_physical_correlation (slab hv) (turn v hv) (small v hv) e he
    change |C|≤L^2/a*z at zbound
    have corr : a*|C|≤L^2*z := by
      have h:=mul_le_mul_of_nonneg_left zbound ap.le
      rwa [show a*(L^2/a*z)=L^2*z by field_simp [ap.ne']] at h
    have ph:=c.quarter_directional_flux_bound (slab hv) (turn v hv) (small v hv) e he
    change Real.sqrt M≤q*Real.sqrt L at ph
    have jm:=mul_le_mul j ph (Real.sqrt_nonneg _) (by positivity)
    have both : a*(Real.sqrt J*Real.sqrt M+|C|)≤L^2*(q+z) := by
      have eq : L*Real.sqrt L*(q*Real.sqrt L)=L^2*q := by
        rw [show L*Real.sqrt L*(q*Real.sqrt L)=L*q*(Real.sqrt L)^2 by ring,Real.sq_sqrt lp.le];ring
      rw [eq] at jm
      linarith only [show a*(Real.sqrt J*Real.sqrt M+|C|)=a*Real.sqrt J*Real.sqrt M+a*|C| by ring,
        jm,corr,show L^2*(q+z)=L^2*q+L^2*z by ring]
    have margin:= (LowDefect.quarter_physical_margins (Real.sqrt_nonneg _) (xhi v hv)).1.le
    have margin' : (1+(x v)^2)*(q+z)≤2*(80/100) := by
      dsimp only [q,z];rw [←xs v hv];linarith only [margin]
    have budget : E*(Real.sqrt J*Real.sqrt M+|C|)≤2*(80/100)*Real.pi*L := by
      apply (mul_le_mul_iff_right₀ ap).mp
      calc a*(E*(Real.sqrt J*Real.sqrt M+|C|)) = E*(a*(Real.sqrt J*Real.sqrt M+|C|)) := by ring
           _ ≤ E*(L^2*(q+z)) := mul_le_mul_of_nonneg_left both ep.le
           _ = (2*Real.pi^2*L)*((1+(x v)^2)*(q+z)) := by
             rw [show E*(L^2*(q+z))=(E*L)*L*(q+z) by ring,show E*L=_ from prod v hv];ring
           _ ≤ (2*Real.pi^2*L)*(2*(80/100)) := mul_le_mul_of_nonneg_left margin' (by positivity)
           _ = a*(2*(80/100)*Real.pi*L) := by dsimp [a];ring
    have raw:=c.centroidRate_virial_product H (slab hv)
    change 2*E*L*|c.centroidRate H v|≤Y*(Real.sqrt J*Real.sqrt M+|C|) at raw
    change |c.centroidRate H v|≤(80/100*Real.pi)*Y/E^2
    apply (le_div_iff₀ (sq_pos_of_pos ep)).mpr
    apply (mul_le_mul_iff_right₀ (show 0<2*L by positivity)).mp
    calc 2*L*(|c.centroidRate H v| *E^2)=E*(2*E*L*|c.centroidRate H v|) := by ring
         _ ≤ E*(Y*(Real.sqrt J*Real.sqrt M+|C|)) := mul_le_mul_of_nonneg_left raw ep.le
         _ = Y*(E*(Real.sqrt J*Real.sqrt M+|C|)) := by ring
         _ ≤ Y*(2*(80/100)*Real.pi*L) := mul_le_mul_of_nonneg_left budget yp
         _ = 2*L*((80/100*Real.pi)*Y) := by ring
  have ht : t∈Icc s t := ⟨st,le_rfl⟩
  have sup (e : ℂ) (he : ‖e‖=1) : ∃u∈Icc 0 c.period, inner ℝ e (c.arclengthCentroid t)+
        (803/1000)*Real.pi/c.bending t ≤ inner ℝ e (c.position t u) := by
    obtain ⟨u,hu,val⟩:=c.quarter_directional_support (slab ht) (turn t ht) (small t ht) e he
    refine ⟨u,hu,le_trans (add_le_add_right ?_ _) val⟩
    change (803/1000)*Real.pi/c.bending t≤c.coreLength t/a*(1-575/1000*x t-279/1000*D t)
    rw [←xs t ht]
    apply (div_le_iff₀ (pos t ht)).mpr
    apply (mul_le_mul_iff_left₀ ap).mp
    have lower:=(LowDefect.quarter_physical_margins (Real.sqrt_nonneg _) (xhi t ht)).2.le
    have hh:=mul_le_mul_of_nonneg_right lower (sq_nonneg Real.pi)
    have ep:=prod t ht
    rw [show c.coreLength t/a*(1-575/1000*x t-279/1000*(x t)^2)*c.bending t*a=
      (c.bending t*c.coreLength t)*(1-575/1000*x t-279/1000*(x t)^2) by field_simp [ap.ne'],ep]
    dsimp only [a];nlinarith only [hh]
  apply closedBall_subset_convexHull_of_directional_margin (R:=(80/100)*Real.pi/c.bending s+
    ((803/1000)*Real.pi-(80/100)*Real.pi)/c.bending t) ?_
  · intro e he
    let H:=innerSL ℝ e
    have drift:=c.centroid_displacement_of_force_bound hf H st slab pos (rate e he)
    rw [←c.map_arclengthCentroid H (slab ht),←c.map_arclengthCentroid H (slab ⟨le_rfl,st⟩)] at drift
    change |inner ℝ e (c.arclengthCentroid t)-inner ℝ e (c.arclengthCentroid s)|≤_ at drift
    obtain ⟨u,hu,hh⟩:=sup e he
    refine ⟨c.position t u,⟨u,hu,rfl⟩,?_⟩
    rw [sub_div];linarith [(abs_le.mp drift).1]
  · have gap : (2/1000)*Real.pi<(803/1000)*Real.pi-(80/100)*Real.pi := by linarith [Real.pi_pos]
    exact add_lt_add_right ((div_lt_div_iff_of_pos_right (pos t ht)).mpr gap) _

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.virial_common_disk_on_slab

