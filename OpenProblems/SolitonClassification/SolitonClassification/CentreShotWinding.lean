import SolitonClassification.OuterStressOrbit
import SolitonClassification.OuterPhase
import SolitonClassification.SupportFlowContinuity

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace ClosedSimilarity.OuterStress.Data
variable {δ : ℝ} (z : Data δ)

/-- On the actual marker scale, all centre shots start inside the same
    nondegenerate layer, for a fixed slow-time interval independently of δ. -/
theorem centre_bounds (hd : 0<δ) (hk : z.K 0=0) (hv : z.V 0=1) (hp : z.p 0=0) (hq : z.q 0=0)
    {s : ℝ} (hs : 0≤s) :
    (z.p s)^2+(z.q s)^2 ≤ s^2 ∧ 1-s^2/2 ≤ z.amplitude s := by
  let P (e t : ℝ) := Real.sqrt (e+(z.p t)^2+(z.q t)^2)
  let A (e t : ℝ) := Real.sqrt (e+((z.K t)^2/2)^2+(z.V t)^2)
  have dP (e : ℝ) (he : 0<e) (t : ℝ) : HasDerivAt (P e) (z.q t/P e t) t := by
    have der : HasDerivAt (fun u => e+(z.p u)^2+(z.q u)^2) (2*z.q t) t := by
      convert! (((z.dp t).pow 2).const_add e).add ((z.dq t).pow 2) using 1
      field_simp [hd.ne']; ring
    convert! der.sqrt (by positivity) using 1
    dsimp [P]; ring
  have dA (e : ℝ) (he : 0<e) (t : ℝ) : HasDerivAt (A e) (-z.V t*z.p t/A e t) t := by
    have der : HasDerivAt (fun u => e+((z.K u)^2/2)^2+(z.V u)^2) (-2*z.V t*z.p t) t := by
      convert! (((((z.dK t).pow 2).div_const 2).pow 2).const_add e).add ((z.dV t).pow 2) using 1
      simp only [Pi.pow_apply]
      field_simp [hd.ne']; ring
    convert! der.sqrt (by positivity) using 1
    dsimp [A]; ring
  have width (t : ℝ) (ht : 0≤t) : Real.sqrt ((z.p t)^2+(z.q t)^2) ≤ t := by
    have est (e : ℝ) (he : 0<e) : P e t ≤ Real.sqrt e+t := by
      have bd (x : ℝ) (_ : x ∈ Icc 0 t) : ‖deriv (P e) x‖ ≤ 1 := by
        rw [(dP e he x).deriv,Real.norm_eq_abs,abs_div,abs_of_pos (show 0<P e x from Real.sqrt_pos.mpr (by positivity))]
        apply (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr
        exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (z.p x)])
      have H := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_deriv_le
        (fun x _ => (dP e he x).differentiableAt) bd (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht)
      simp only [Real.norm_eq_abs,sub_zero,one_mul,abs_of_nonneg ht] at H
      have h0 : P e 0=Real.sqrt e := by simp [P,hp,hq]
      linarith [(le_abs_self (P e t-P e 0)).trans H]
    have h : ∀ᶠ e : ℝ in 𝓝[>] 0, P e t ≤ Real.sqrt e+t :=
      (show ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Ioi 0 from self_mem_nhdsWithin).mono fun e he => est e he
    have cl : Continuous (fun e : ℝ => P e t) := by unfold P; fun_prop
    have cr : Continuous (fun e : ℝ => Real.sqrt e+t) := by fun_prop
    simpa [P] using le_of_tendsto_of_tendsto (cl.continuousWithinAt (x:=0)).tendsto
      (cr.continuousWithinAt (x:=0)).tendsto h
  have pq (t : ℝ) (ht : 0≤t) : (z.p t)^2+(z.q t)^2≤t^2 := by
    simpa only [Real.sq_sqrt (show 0≤(z.p t)^2+(z.q t)^2 by positivity)] using
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (width t ht) 2
  refine ⟨pq s hs,?_⟩
  have est (e : ℝ) (he : 0<e) : A e 0 ≤ A e s + s^2/2 := by
    let f := fun x : ℝ => A e x+x^2/2
    have df (x : ℝ) : HasDerivAt f (-z.V x*z.p x/A e x+x) x := by
      convert! (dA e he x).add (((hasDerivAt_id x).pow 2).div_const 2) using 1
      simp only [id_eq]
      ring
    have mono : MonotoneOn f (Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun x _ => (df x).continuousAt.continuousWithinAt)
        (fun x _ => (df x).differentiableAt.differentiableWithinAt)
      rw [interior_Ici]
      intro x hx
      have ap : 0<A e x := Real.sqrt_pos.mpr (by positivity)
      have Vbound : |z.V x|≤A e x := Real.abs_le_sqrt (by nlinarith [sq_nonneg ((z.K x)^2/2)])
      have pbound : |z.p x|≤x := le_of_sq_le_sq (by rw [sq_abs]; nlinarith [pq x hx.le,sq_nonneg (z.q x)]) hx.le
      have H := mul_le_mul Vbound pbound (abs_nonneg _) ap.le
      rw [←abs_mul] at H
      have vb := (le_abs_self _).trans H
      rw [(df x).deriv,neg_mul,neg_div]
      have := (div_le_iff₀ ap).mpr (by linarith : z.V x*z.p x ≤ x*A e x)
      linarith
    simpa [f] using mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
  have h : ∀ᶠ e : ℝ in 𝓝[>] 0, A e 0 ≤ A e s +s^2/2 :=
    (show ∀ᶠ e : ℝ in 𝓝[>] 0, e ∈ Ioi 0 from self_mem_nhdsWithin).mono fun e he => est e he
  have cl : Continuous (fun e : ℝ => A e 0) := by unfold A; fun_prop
  have cr : Continuous (fun e : ℝ => A e s+s^2/2) := by unfold A; fun_prop
  have out := le_of_tendsto_of_tendsto (cl.continuousWithinAt (x:=0)).tendsto
    (cr.continuousWithinAt (x:=0)).tendsto h
  simp [A,hk,hv] at out
  unfold amplitude
  linarith

theorem centre_winding (hd : 0<δ) (small : δ≤1/32)
    (hk : z.K 0=0) (hv : z.V 0=1) (hp : z.p 0=0) (hq : z.q 0=0) :
    let θ := fun x => ∫ t in (0:ℝ)..x, Angle.spin δ z.root z.shape z.slope z.along z.across t
    (∀ x ∈ Icc (0:ℝ) 1, 1/2≤z.root x ∧ Angle.sn z.shape x=Real.sin (θ x) ∧
      Angle.cs z.shape z.slope x=Real.cos (θ x)) ∧ 1/(8*δ)≤θ 1 := by
  have bounds (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      Rates δ x z.root z.shape z.slope z.along z.across ∧ |z.along x|≤1 ∧ |z.across x|≤1 ∧
      4*1*δ≤z.root x^3 ∧ 1/2≤z.root x := by
    obtain ⟨pq,amp⟩ := z.centre_bounds hd hk hv hp hq hx.1
    have x2 := pow_le_pow_left₀ hx.1 hx.2 2
    have lower : 1/2≤z.amplitude x := by nlinarith
    have apos : 0<z.amplitude x := by linarith
    have rsq : z.root x^2=z.amplitude x := Real.sq_sqrt apos.le
    have pos : 0≤z.root x := Real.sqrt_nonneg _
    have rlo : 1/2≤z.root x := le_of_sq_le_sq (by nlinarith) pos
    have r3 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/2) rlo 3
    have frame := z.radius_sq x apos
    refine ⟨z.normalized_rates x apos hd,?_,?_,by linarith,rlo⟩
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.across x)]
    · apply le_of_sq_le_sq _ zero_le_one
      rw [sq_abs]; nlinarith [sq_nonneg (z.along x)]
  have az : z.amplitude 0=1 := by norm_num [amplitude,hk,hv]
  have lift := Angle.physical_phase_lift (by norm_num : (0:ℝ)≤1) (fun x hx => (bounds x hx).1)
    (by simp [Angle.sn,shape,hk]) (by simp [Angle.cs,shape,slope,hk,hv,az])
  refine ⟨fun x hx => ⟨(bounds x hx).2.2.2.2,lift x hx⟩,?_⟩
  have wind := Angle.winding_on_interval (by norm_num : (0:ℝ)≤1) bounds
  convert wind using 1
  ring

end ClosedSimilarity.OuterStress.Data

namespace ClosedSimilarity.GlobalSupport
open OuterStress

def centreData (b : ℝ) (hb : 0<b) : OuterStress.Data b⁻¹ :=
  ofSupport (inv_pos.mpr hb) (solution 1 ![0,b,0,0]) (solution_derivative 1 _)

/-- Starting only with a curvature slope b, the globally existing physical
    centre shot winds through an angle at least b/8 by s=√b. -/
theorem physical_centre_winding {b : ℝ} (hb : 32≤b) :
    let z := centreData b (by linarith)
    let θ := fun x => ∫ t in (0:ℝ)..x, Angle.spin b⁻¹ z.root z.shape z.slope z.along z.across t
    (∀ x ∈ Icc (0:ℝ) 1, 1/2≤z.root x ∧ Angle.sn z.shape x=Real.sin (θ x) ∧
      Angle.cs z.shape z.slope x=Real.cos (θ x)) ∧ b/8 ≤ θ 1 := by
  have p : 0<b := by linarith
  let z := centreData b p
  have dp := inv_pos.mpr p
  have small : b⁻¹≤1/32 := by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) hb
  have start := z.centre_winding dp small
    (by simp [z,centreData,ofSupport,solution_zero])
    (by simp [z,centreData,ofSupport,solution_zero,p.ne'])
    (by simp [z,centreData,ofSupport,solution_zero])
    (by simp [z,centreData,ofSupport,solution_zero])
  simpa only [one_div,mul_inv_rev,inv_inv,div_eq_mul_inv,mul_comm,one_mul] using start

end ClosedSimilarity.GlobalSupport
#print axioms ClosedSimilarity.GlobalSupport.physical_centre_winding
