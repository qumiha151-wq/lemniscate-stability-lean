import Migration.ForceIdentities
import Migration.BendingDissipation
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Exact endpoint stress and the dissipation cost of closing a transverse
translating body. The vertical direction is fixed by the coordinate frame.
The body is any measurable part of the arclength period. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.TranslatorCaps

def mass (G : Set ℝ) (f : ℝ → ℝ) := ∫ s in G, f s^2
def pairing (G : Set ℝ) (f g : ℝ → ℝ) := ∫ s in G, f s*g s

private theorem mass_nonneg (G : Set ℝ) (f : ℝ → ℝ) : 0≤mass G f :=
  integral_nonneg (fun _ => sq_nonneg _)

private theorem integrated_cs {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} {G : Set ℝ} (hG : G ⊆ Icc a b) :
    pairing G f g ^ 2 ≤ mass G f * mass G g := by
  have hI {q : ℝ → ℝ} (hq : Continuous q) : IntegrableOn q G volume :=
    (hq.continuousOn.integrableOn_compact isCompact_Icc).mono_set hG
  have hpoly (t : ℝ) : 0 ≤ mass G g*(t*t) + (2*pairing G f g)*t + mass G f := by
    have hpos := mass_nonneg G (fun s => f s+t*g s)
    unfold mass at hpos ⊢
    unfold pairing
    rw [show (fun s => (f s+t*g s)^2)=(fun s => f s^2+(2*t)*(f s*g s)+(t*t)*g s^2)
      by funext s; ring,integral_add (f:=fun s => f s^2+(2*t)*(f s*g s)) (g:=fun s=> (t*t)*g s^2)
        (hI ((hf.pow 2).add ((hf.mul hg).const_mul _)))
        (hI ((hg.pow 2).const_mul _)),integral_add (f:=fun s=>f s^2) (g:=fun s => (2*t)*(f s*g s))
        (hI (hf.pow 2)) (hI ((hf.mul hg).const_mul _)),
        integral_const_mul,integral_const_mul] at hpos
    linarith
  have h := discrim_le_zero hpoly
  dsimp [discrim] at h
  nlinarith

theorem stress_chord_of_translating_arc {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) {a b v : ℝ} (hab : a<b) (hv : 0≤v)
    (htr : ∀ s ∈ Icc a b, elasticForce x y s = -v*deriv x s) :
    v*(x b-x a)^2 ≤ (b-a)*(stressY x y a-stressY x y b) := by
  have hn := (contDiff_infty_iff_deriv.mp hx).2.continuous
  have hf := (elasticForce_smooth hx hy).continuous
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a:=a) (b:=b) (fun s _ => stressY_hasDerivAt hx hy hu s) ((hf.mul hn).intervalIntegrable _ _)
  have he : (∫ s in a..b, elasticForce x y s*deriv x s)= -v*(∫s in a..b,deriv x s^2) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [htr s (by simpa [uIcc_of_le hab.le] using hs)]
    ring
  have hdx := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => (hx.differentiable (by simp) s).hasDerivAt) (hn.intervalIntegrable a b)
  have hcs := integrated_cs (f:=fun _ : ℝ => (1:ℝ)) continuous_const hn
    (G:=Ioc a b) Ioc_subset_Icc_self
  unfold pairing mass at hcs
  simp only [one_mul,one_pow,← intervalIntegral.integral_of_le hab.le,hdx,
    intervalIntegral.integral_const,smul_eq_mul,mul_one] at hcs
  have hforce : stressY x y a-stressY x y b=v*(∫ s in a..b, deriv x s^2) := by linarith
  rw [hforce]
  nlinarith only [mul_le_mul_of_nonneg_left hcs hv]

/-- Fourth-moment identity with both endpoint terms retained. It is
valid on any smooth unit-speed arc, irrespective of closure or translation. -/
theorem arc_stress_energy_identity {x y : ℝ → ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1) (a b : ℝ) :
    let k := signedCurvature x y
    (∫ s in a..b, stressX x y s^2+stressY x y s^2) =
      k b*deriv k b-k a*deriv k a+(3/4:ℝ)*(∫ s in a..b,k s^4)-
        ∫ s in a..b,k s*elasticForce x y s := by
  let k := signedCurvature x y
  have hk : ContDiff ℝ ∞ k := signedCurvature_smooth hx hy
  have hk' := (contDiff_infty_iff_deriv.mp hk).2
  have hk'' := (contDiff_infty_iff_deriv.mp hk').2
  have hd (s : ℝ) : HasDerivAt (fun z => k z*deriv k z)
      ((deriv k s)^2+k s*deriv (deriv k) s) s := by
    apply (((hk.differentiable (by simp) s).hasDerivAt).mul
      (hk'.differentiable (by simp) s).hasDerivAt).congr_deriv
    ring
  have hder : Continuous (fun s => (deriv k s)^2+k s*deriv (deriv k) s) :=
    (hk'.continuous.pow 2).add (hk.continuous.mul hk''.continuous)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=a) (b:=b)
    (fun s _ => hd s) (hder.intervalIntegrable a b)
  have he (s : ℝ) : stressX x y s^2+stressY x y s^2 =
      ((deriv k s)^2+k s*deriv (deriv k) s)+(3/4:ℝ)*k s^4-k s*elasticForce x y s := by
    dsimp [stressX,stressY,elasticForce,k]
    linear_combination ((deriv (signedCurvature x y) s)^2+(signedCurvature x y s)^4/4)*hu s
  dsimp only
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (f:=fun s=>(deriv k s)^2+k s*deriv (deriv k) s+(3/4)*k s^4)
    (g:=fun s=>k s*elasticForce x y s)
    ((hder.add ((hk.continuous.pow 4).const_mul (3/4))).intervalIntegrable a b)
    ((hk.continuous.mul (elasticForce_smooth hx hy).continuous).intervalIntegrable a b),
    intervalIntegral.integral_add
      (f:=fun s=>(deriv k s)^2+k s*deriv (deriv k) s) (g:=fun s=>(3/4)*k s^4)
      (hder.intervalIntegrable a b)
      (((hk.continuous.pow 4).const_mul (3/4)).intervalIntegrable a b),
    intervalIntegral.integral_const_mul,hFTC]

private theorem compensation {f n : ℝ → ℝ} (hf : Continuous f) (hn : Continuous n)
    {L v η : ℝ} (_hL : 0≤L) (hv : 0<v) (hη : 0≤η) (hη' : η<1)
    {G : Set ℝ} (hG : MeasurableSet G) (hsub : G⊆Ioc 0 L)
    (hbalance : pairing (Ioc 0 L) f n=0) (hA : 0<mass G n)
    (happrox : mass G (fun s => f s+v*n s) ≤ η^2*v^2*mass G n) :
    let H := Ioc 0 L \ G
    0<mass H n ∧ (1-η)*v*mass G n ≤ pairing H f n ∧
      ((1-η)*v*mass G n)^2 / mass H n ≤ mass H f ∧
      (1-η)^2*v^2*mass G n*(1+mass G n/mass H n) ≤ mass (Ioc 0 L) f := by
  let H := Ioc 0 L \ G
  let A := mass G n
  let B := mass H n
  let J := pairing H f n
  let α := (1-η)*v
  have hα : 0<α := mul_pos (sub_pos.mpr hη') hv
  have hGc : G⊆Icc 0 L := hsub.trans Ioc_subset_Icc_self
  have hHc : H⊆Icc 0 L := sdiff_subset.trans Ioc_subset_Icc_self
  have hI {q : ℝ → ℝ} (hq : Continuous q) : IntegrableOn q (Ioc 0 L) volume :=
    (hq.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hJ : J= -pairing G f n := by
    dsimp [J,H,pairing]
    rw [setIntegral_sdiff (f:=fun s=>f s*n s) hG (hI (hf.mul hn)) hsub]
    simpa [pairing] using congrArg (fun z:ℝ => z-pairing G f n) hbalance
  have hpair : pairing G (fun s => f s+v*n s) n=pairing G f n+v*A := by
    dsimp [A,pairing,mass]
    rw [show (fun s => (f s+v*n s)*n s)=(fun s => f s*n s+v*n s^2) by funext s; ring,
      integral_add (f:=fun s=>f s*n s) (g:=fun s=>v*n s^2)
        ((hI (q:=fun s=>f s*n s) (hf.mul hn)).mono_set hsub)
        ((hI (q:=fun s=>v*n s^2) ((hn.pow 2).const_mul v)).mono_set hsub),
      integral_const_mul]
  have hcs := integrated_cs (hf.add (hn.const_mul v)) hn hGc
  change pairing G (fun s => f s+v*n s) n^2 ≤ mass G (fun s => f s+v*n s)*A at hcs
  rw [hpair, ← neg_eq_iff_eq_neg.mpr hJ] at hcs
  have hsmall : (-J+v*A)^2 ≤ (η*v*A)^2 := by
    nlinarith only [hcs,mul_le_mul_of_nonneg_right happrox hA.le]
  have htarget : α*A≤J := by
    have := (abs_le.mp (abs_le_of_sq_le_sq hsmall
      (mul_nonneg (mul_nonneg hη hv.le) hA.le))).2
    dsimp [α]
    linarith
  have hcaps : J^2 ≤ mass H f*B := integrated_cs hf hn hHc
  have hbody := integrated_cs hf hn hGc
  rw [← neg_eq_iff_eq_neg.mpr hJ,neg_sq] at hbody
  have hsq := pow_le_pow_left₀ (mul_pos hα hA).le htarget 2
  have hB : 0<B := by
    by_contra! hh
    have := mul_nonpos_of_nonneg_of_nonpos (mass_nonneg H f) hh
    nlinarith only [hsq,hcaps,this,sq_pos_of_pos (mul_pos hα hA)]
  have hcap' : (α*A)^2/B ≤ mass H f := (div_le_iff₀ hB).mpr (hsq.trans hcaps)
  have hg' : α^2*A ≤ mass G f := by
    apply le_of_mul_le_mul_right _ hA
    nlinarith only [hsq,hbody]
  have hdiff : mass H f = mass (Ioc 0 L) f-mass G f := by
    exact setIntegral_sdiff hG (hI (hf.pow 2)) hsub
  refine ⟨hB,htarget,hcap',?_⟩
  change (1-η)^2*v^2*A*(1+A/B) ≤ mass (Ioc 0 L) f
  have halg : (1-η)^2*v^2*A*(1+A/B)=α^2*A+(α*A)^2/B := by dsimp [α]; ring
  rw [halg]
  linarith

/-- For the actual vertical normal component n=x', closing an approximately
vertical-translating body forces opposite projected velocity on the caps
and the stated dissipation on the caps and entire closed period. -/
theorem closed_caps_dissipation {x y : ℝ → ℝ} {L v η : ℝ}
    (hx : ContDiff ℝ ∞ x) (hy : ContDiff ℝ ∞ y)
    (hpx : Function.Periodic x L) (hpy : Function.Periodic y L)
    (hu : ∀ s, (deriv x s)^2+(deriv y s)^2=1)
    (hL : 0≤L) (hv : 0<v) (hη : 0≤η) (hη' : η<1)
    {G : Set ℝ} (hG : MeasurableSet G) (hsub : G⊆Ioc 0 L) (hA : 0<mass G (deriv x))
    (happrox : mass G (fun s => elasticForce x y s + v*deriv x s) ≤ η^2*v^2*mass G (deriv x)) :
    let A := mass G (deriv x)
    let H := Ioc 0 L \ G
    let B := mass H (deriv x)
    0<B ∧ (1-η)*v*A ≤ pairing H (elasticForce x y) (deriv x) ∧
      ((1-η)*v*A)^2/B ≤ mass H (elasticForce x y) ∧
      (1-η)^2*v^2*A*(1+A/B) ≤ dissipation x y L := by
  have bal := (elasticForce_balance hx hy hpx hpy hu).2
  rw [intervalIntegral.integral_of_le hL] at bal
  simpa only [dissipation,intervalIntegral.integral_of_le hL,mass] using
    compensation (elasticForce_smooth hx hy).continuous (contDiff_infty_iff_deriv.mp hx).2.continuous
      hL hv hη hη' hG hsub bal hA happrox

open MigrationGeometry.Flow

/-- Multiplying both factors by the square root of the material speed
makes Lebesgue integrals over arbitrary parameter subsets arclength integrals. -/
def materialForce (γ : ℝ → ℂ) (u : ℝ) := force γ u * Real.sqrt (speed γ u)
def materialProjection (γ : ℝ → ℂ) (H : ℂ →L[ℝ] ℝ) (u : ℝ) :=
  H (normal γ u)*Real.sqrt (speed γ u)

theorem material_force_balance {γ : ℝ → ℂ} {P : ℝ} (hP : 0≤P)
    (hγ : ContDiff ℝ ∞ γ) (hreg : ∀ u, deriv γ u≠0) (hp : Function.Periodic γ P)
    (H : ℂ →L[ℝ] ℝ) :
    pairing (Ioc 0 P) (materialForce γ) (materialProjection γ H)=0 := by
  have hs := (speed_smooth hγ hreg).continuous
  have hf := (force_smooth hγ hreg).continuous
  have hn := H.continuous.comp (normal_smooth hγ hreg).continuous
  have hd (u : ℝ) : HasDerivAt (fun s => H (stress γ s))
      (speed γ u*force γ u*H (normal γ u)) u := by
    have h := H.hasFDerivAt.comp_hasDerivAt u (stress_hasDerivAt hγ hreg u)
    simpa [←Complex.real_smul,mul_assoc,Function.comp_def] using h
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=P)
    (fun u _ => hd u) (((hs.mul hf).mul hn).intervalIntegrable 0 P)
  rw [show stress γ P=stress γ 0 by simpa using stress_periodic hγ hreg hp 0,sub_self] at hft
  unfold pairing
  rw [← intervalIntegral.integral_of_le hP]
  calc
    _ = ∫ u in 0..P, speed γ u*force γ u*H (normal γ u) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp [materialForce,materialProjection]
      linear_combination (force γ u*H (normal γ u))*Real.sq_sqrt (speed_pos hreg u).le
    _ = 0 := hft

/-- The full dissipation term is the negative derivative of the bending
energy of the same arbitrary-speed normal flow at the given time. -/
theorem true_flow_cap_energy_rate {I : Set ℝ} (c : SmoothPeriodicImmersion I)
    (hflow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) (H : ℂ →L[ℝ] ℝ)
    {v η : ℝ} (hv : 0<v) (hη : 0≤η) (hη' : η<1)
    {G : Set ℝ} (hG : MeasurableSet G) (hsub : G⊆Ioc 0 c.period)
    (hA : 0<mass G (materialProjection (c.position t) H))
    (happrox : mass G (fun u => materialForce (c.position t) u+
      v*materialProjection (c.position t) H u) ≤ η^2*v^2*mass G (materialProjection (c.position t) H)) :
    let F := materialForce (c.position t)
    let n := materialProjection (c.position t) H
    let J := Ioc 0 c.period \ G
    let A := mass G n
    let B := mass J n
    0<B ∧ (1-η)*v*A ≤ pairing J F n ∧ ((1-η)*v*A)^2/B ≤ mass J F ∧
      (1-η)^2*v^2*A*(1+A/B) ≤ -deriv c.bending t := by
  let γ := c.position t
  have hγ := c.position_slice_smooth ht
  have hr := c.immersion t ht
  have hs := (speed_smooth hγ hr).continuous.sqrt
  have hF : Continuous (materialForce γ) := (force_smooth hγ hr).continuous.mul hs
  have hn : Continuous (materialProjection γ H) :=
    (H.continuous.comp (normal_smooth hγ hr).continuous).mul hs
  have h := compensation hF hn c.period_pos.le hv hη hη' hG hsub
    (material_force_balance c.period_pos.le hγ hr (c.periodic t ht) H) hA happrox
  have he : mass (Ioc 0 c.period) (materialForce γ) = -deriv c.bending t := by
    rw [(c.bending_hasDerivAt_dissipation hflow H ht).deriv,neg_neg]
    unfold mass SmoothPeriodicImmersion.localDissipation
    rw [← intervalIntegral.integral_of_le c.period_pos.le]
    apply intervalIntegral.integral_congr
    intro u _
    simp [materialForce,mul_pow,Real.sq_sqrt (speed_pos hr u).le,γ]
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans_eq he⟩

/-- A time-varying measurable body with uniformly thin caps must pay
this bending-energy loss over the whole time interval. No differentiability
or continuity of the chosen subsets in time is needed. -/
theorem sustained_translator_body_cost {I : Set ℝ} (c : SmoothPeriodicImmersion I)
    (hflow : c.IsNormalFEF) {a b : ℝ} (hab : a<b) (htimes : Icc a b ⊆ I)
    (H : ℂ →L[ℝ] ℝ) {v η A₀ B₀ : ℝ} (hv : 0<v) (hη : 0≤η) (hη' : η<1)
    (hA₀ : 0<A₀) (hB₀ : 0<B₀) (G : ℝ → Set ℝ)
    (hG : ∀ t ∈ Ioo a b, MeasurableSet (G t) ∧ G t⊆Ioc 0 c.period)
    (hsize : ∀ t ∈ Ioo a b, let n := materialProjection (c.position t) H
      A₀≤mass (G t) n ∧ mass (Ioc 0 c.period \ G t) n≤B₀)
    (happrox : ∀ t ∈ Ioo a b, mass (G t) (fun u => materialForce (c.position t) u+
      v*materialProjection (c.position t) H u) ≤ η^2*v^2*mass (G t) (materialProjection (c.position t) H)) :
    (1-η)^2*v^2*A₀*(1+A₀/B₀)*(b-a) ≤ c.bending a-c.bending b := by
  have hc : ContinuousOn c.bending (Icc a b) := fun t ht =>
    (c.bending_hasDerivAt_dissipation hflow H (htimes ht)).continuousAt.continuousWithinAt
  obtain ⟨t,ht,hder⟩ := exists_deriv_eq_slope c.bending hab hc
    (fun s hs => (c.bending_hasDerivAt_dissipation hflow H (htimes ⟨hs.1.le,hs.2.le⟩)).differentiableAt.differentiableWithinAt)
  let A := mass (G t) (materialProjection (c.position t) H)
  let B := mass (Ioc 0 c.period \ G t) (materialProjection (c.position t) H)
  obtain ⟨ha,hb⟩ := hsize t ht
  have hr := true_flow_cap_energy_rate c hflow (htimes ⟨ht.1.le,ht.2.le⟩) H hv hη hη'
    (hG t ht).1 (hG t ht).2 (hA₀.trans_le ha) (happrox t ht)
  have hB : 0<B := hr.1
  have hg : A₀/B₀≤A/B := div_le_div₀ (hA₀.le.trans ha) ha hB hb
  have h1 : (1-η)^2*v^2*A₀*(1+A₀/B₀) ≤ (1-η)^2*v^2*A*(1+A/B) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left ha (by positivity)) (by linarith only [hg])
      (by positivity) (by have := hA₀.trans_le ha; positivity)
  have h := h1.trans hr.2.2.2
  rw [hder,←neg_div] at h
  have hcst := (le_div_iff₀ (sub_pos.mpr hab)).mp h
  linarith

end MigrationGeometry.TranslatorCaps
open Lean Elab Command in
run_cmd do
  for n in #[`MigrationGeometry.TranslatorCaps.closed_caps_dissipation,
      `MigrationGeometry.TranslatorCaps.true_flow_cap_energy_rate,
      `MigrationGeometry.TranslatorCaps.sustained_translator_body_cost,
      `MigrationGeometry.TranslatorCaps.arc_stress_energy_identity,
      `MigrationGeometry.TranslatorCaps.stress_chord_of_translating_arc] do
    for a in (← collectAxioms n) do
      unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains a do
        throwError "Unexpected axiom {a} in {n}"
  logInfo "TRANSLATOR_CAP_AUDIT actual stress chord, arc energy, cap dissipation, true FEF rate, and finite-time cost"
