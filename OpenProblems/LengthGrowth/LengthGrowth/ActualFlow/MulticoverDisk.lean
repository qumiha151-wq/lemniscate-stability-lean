import LengthGrowth.ActualFlow.EnclosingDisk
import LengthGrowth.ActualFlow.MulticoverIntegral

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

/-- The center is the initial point plus the initial normal times the inverse
signed mean curvature. Both orientations are included. -/
theorem winding_disk {S:ℝ} (hsum : (∫s in 0..c.period,c.curvature s)=S) (nz : S≠0)
    (nn : 0≤2*c.energy*c.period-S^2) :
    ∃z:ℂ,∀s∈Icc 0 c.period,‖c.curve s-z‖≤c.period/|S| *(1+Real.sqrt (2*c.energy*c.period-S^2)) := by
  let L:=c.period
  let d:=2*c.energy*L-S^2
  let a:=L/S
  let g:=fun s=>1-a*c.curvature s
  let Z:=fun s=>c.curve s+(a:ℂ)*c.normal s
  have lp : 0<L:=c.period_pos
  have ap : |a|=L/|S|:=by rw [abs_div,abs_of_pos lp]
  have cg : Continuous g:=continuous_const.sub (continuous_const.mul c.curvature_continuous)
  have ek : (∫s in 0..L,c.curvature s^2)=2*c.energy:=by unfold energy;ring
  have gg : (∫s in 0..L,g s^2)=L*d/S^2:=by
    have expand : (fun s=>g s^2)=(fun s=>1+(-2*a)*c.curvature s+a^2*c.curvature s^2):=by funext s;dsimp [g];ring
    rw [expand,intervalIntegral.integral_add,intervalIntegral.integral_add,intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,ek,hsum]
    · simp only [sub_zero,smul_eq_mul,mul_one]
      dsimp only [d,a]
      field_simp [nz];ring
    · exact continuous_const.intervalIntegrable _ _
    · exact (continuous_const.mul c.curvature_continuous).intervalIntegrable _ _
    · exact (continuous_const.add (continuous_const.mul c.curvature_continuous)).intervalIntegrable _ _
    · exact (continuous_const.mul (c.curvature_continuous.pow 2)).intervalIntegrable _ _
  have estimate : (∫s in 0..L,|g s|)≤L/|S| *Real.sqrt d:=by
    have cs:=LengthGrowth.interval_integral_mul_sq_le cg.abs (continuous_const (y:=(1:ℝ))) lp.le
    change (∫s in 0..L,|g s| *1)^2≤(∫s in 0..L,|g s|^2)*(∫_ in 0..L,(1:ℝ)^2) at cs
    simp only [mul_one,sq_abs,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,gg] at cs
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow,div_pow,sq_abs,Real.sq_sqrt nn]
    change _≤L^2/S^2*d
    exact cs.trans_eq (by ring)
  have dz (s:ℝ) : HasDerivAt Z ((g s:ℂ)*c.tangent s) s:=by
    apply ((c.curve_deriv s).add ((c.normal_deriv s).const_mul (a:ℂ))).congr_deriv
    simp only [g,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
    ring
  refine ⟨Z 0,fun s hs=>?_⟩
  have bound : ‖Z s-Z 0‖≤L/|S| *Real.sqrt d:=by
    have ft:=intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=s) (fun t _=>dz t)
      (((Complex.continuous_ofReal.comp cg).mul c.tangent_continuous).intervalIntegrable 0 s)
    rw [←ft]
    calc
      _≤∫t in 0..s,‖(g t:ℂ)*c.tangent t‖:= intervalIntegral.norm_integral_le_integral_norm hs.1
      _=∫t in 0..s,|g t|:=by congr 1;funext t;simp [c.tangent_unit]
      _≤∫t in 0..L,|g t|:=intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
        (Filter.Eventually.of_forall (fun t=>abs_nonneg _)) (cg.abs.intervalIntegrable _ _)
      _≤_:=estimate
  have tri:=norm_sub_le (Z s-Z 0) ((a:ℂ)*c.normal s)
  have eq : Z s-Z 0-(a:ℂ)*c.normal s=c.curve s-Z 0:=by dsimp [Z];ring
  rw [eq,norm_mul,c.normal_unit,mul_one,Complex.norm_real,Real.norm_eq_abs,ap] at tri
  change ‖c.curve s-Z 0‖≤L/|S| *(1+Real.sqrt d)
  linarith only [tri,bound]

theorem winding_dissipation {S:ℝ} (hsum : (∫s in 0..c.period,c.curvature s)=S) (nz : S≠0)
    (nn : 0≤2*c.energy*c.period-S^2) :
    S^4*c.energy≤2*c.dissipation*c.period^4*(1+Real.sqrt (2*c.energy*c.period-S^2))^4 := by
  obtain ⟨z,cover⟩:=c.winding_disk hsum nz nn
  have h:=(c.disk_controls z cover).1
  rw [mul_pow,div_pow,show |S|^4=S^4 by rw [show |S|^4=(|S|^2)^2 by ring,sq_abs];ring] at h
  have pos : 0<S^4:=by positivity
  let g:=1+Real.sqrt (2*c.energy*c.period-S^2)
  change c.energy≤2*c.dissipation*(c.period^4/S^4*g^4) at h
  rw [show 2*c.dissipation*(c.period^4/S^4*g^4)=2*c.dissipation*c.period^4*g^4/S^4 by ring] at h
  linarith only [(le_div_iff₀ pos).mp h]
end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.winding_dissipation
