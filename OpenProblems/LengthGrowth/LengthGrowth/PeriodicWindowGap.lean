import LengthGrowth.ActualFlow.SpatialPeriodicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Finite-window averages of scalar periodic functions on the real line. -/
noncomputable section
open Set MeasureTheory Function
open scoped ContDiff
namespace LengthGrowth.PeriodicWindowGap

/-- Mean over one period, based at zero. -/
def mean (P : ℝ) (f : ℝ → ℝ) := (∫ x in 0..P, f x) / P

/-- Integral over a window of arbitrary length, using the real-line extension. -/
def mass (T : ℝ) (f : ℝ → ℝ) (x : ℝ) := ∫ t in 0..T, f (x+t)

def window (T : ℝ) (f : ℝ → ℝ) (x : ℝ) := mass T f x / T

theorem mass_eq_interval (T : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    mass T f x = ∫ t in x..x+T, f t := by
  simp [mass,intervalIntegral.integral_comp_add_left,add_comm]

theorem continuous_mass {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) : Continuous (mass T f) := by
  have hprim := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hf.intervalIntegrable (a := a) (b := b)) 0
  have he : mass T f = fun x =>
      (∫ y in 0..x+T, f y) - ∫ y in 0..x, f y := by
    funext x
    rw [mass_eq_interval]
    linarith [intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) 0 x) (hf.intervalIntegrable (μ := volume) x (x+T))]
  rw [he]
  exact (hprim.comp (continuous_id.add continuous_const)).sub hprim

theorem continuous_window {f : ℝ → ℝ} (hf : Continuous f) (T : ℝ) : Continuous (window T f) :=
  (continuous_mass hf T).div_const T

/-- Periodicity of the integrand and Fubini give this for every positive window length,
including windows longer than the period. -/
theorem mean_mass {P T : ℝ} (hP : 0<P) (hT : 0<T) {f : ℝ → ℝ}
    (hc : Continuous f) (hp : Periodic f P) : mean P (mass T f) = T * mean P f := by
  have hc2 : Continuous (fun p : ℝ × ℝ => f (p.1+p.2)) :=
    hc.comp (continuous_fst.add continuous_snd)
  have hint : IntegrableOn (uncurry (fun x t : ℝ => f (x+t)))
      (uIoc 0 P ×ˢ uIoc 0 T) := by
    rw [uIoc_of_le hP.le,uIoc_of_le hT.le]
    exact (hc2.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have he (t : ℝ) : (∫ x in 0..P, f (x+t)) = ∫ x in 0..P, f x := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [add_comm] using hp.intervalIntegral_add_eq t 0
  unfold mean mass
  rw [intervalIntegral_intervalIntegral_swap hint]
  simp_rw [he]
  simp [intervalIntegral.integral_const]
  ring

theorem mean_window {P T : ℝ} (hP : 0<P) (hT : 0<T) {f : ℝ → ℝ}
    (hc : Continuous f) (hp : Periodic f P) : mean P (window T f) = mean P f := by
  have h := mean_mass hP hT hc hp
  unfold mean window at *
  rw [intervalIntegral.integral_div]
  field_simp at h ⊢
  nlinarith

private theorem avg_mono {P : ℝ} (hP : 0<P) {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 P) (hg : IntervalIntegrable g volume 0 P)
    (hfg : ∀ x, f x ≤ g x) : mean P f ≤ mean P g :=
  div_le_div_of_nonneg_right (intervalIntegral.integral_mono_on hP.le hf hg (fun x _ => hfg x)) hP.le

private theorem avg_const {P : ℝ} (hP : 0<P) (a : ℝ) : mean P (fun _ => a) = a := by
  simp [mean,intervalIntegral.integral_const,hP.ne']

private theorem avg_add {P : ℝ} {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 P)
    (hg : IntervalIntegrable g volume 0 P) :
    mean P (fun x => f x+g x) = mean P f+mean P g := by
  simp [mean,intervalIntegral.integral_add hf hg,add_div]

private theorem avg_sub {P : ℝ} {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 P)
    (hg : IntervalIntegrable g volume 0 P) :
    mean P (fun x => f x-g x) = mean P f-mean P g := by
  simp [mean,intervalIntegral.integral_sub hf hg,sub_div]

private theorem avg_scale (P d : ℝ) (f : ℝ → ℝ) :
    mean P (fun x => d*f x) = d*mean P f := by
  simp [mean,intervalIntegral.integral_const_mul]
  ring

/-- Nonnegative variance on each translated window. -/
theorem window_square_le {T : ℝ} (hT : 0<T) {f : ℝ → ℝ} (hc : Continuous f) (x : ℝ) :
    (window T f x)^2 ≤ window T (fun y => (f y)^2) x := by
  let g : ℝ → ℝ := fun t => f (x+t)
  have hg : Continuous g := hc.comp (continuous_const.add continuous_id)
  let a := mean T g
  have hi : IntervalIntegrable (fun t => 2*a*g t) volume 0 T := (hg.const_mul (2*a)).intervalIntegrable 0 T
  have hs := avg_mono hT (hi.sub
    (intervalIntegrable_const (c := a^2))) ((hg.pow 2).intervalIntegrable 0 T)
    (fun t => show 2*a*g t-a^2 ≤ (g t)^2 by nlinarith [sq_nonneg (g t-a)])
  rw [avg_sub hi intervalIntegrable_const,
    avg_scale,avg_const hT] at hs
  change a^2 ≤ mean T (fun t => (g t)^2)
  change 2*a*a-a^2 ≤ mean T (fun t => (g t)^2) at hs
  linarith

theorem mean_window_square_le {P T : ℝ} (hP : 0<P) (hT : 0<T) {f : ℝ → ℝ}
    (hc : Continuous f) (hp : Periodic f P) :
    mean P (fun x => (window T f x)^2) ≤ mean P (fun x => (f x)^2) := by
  have h := avg_mono hP (((continuous_window hc T).pow 2).intervalIntegrable 0 P)
    ((continuous_window (hc.pow 2) T).intervalIntegrable 0 P) (window_square_le hT hc)
  exact h.trans_eq (mean_window (f := fun x => (f x)^2) hP hT (hc.pow 2)
    (fun x => congrArg (fun z : ℝ => z^2) (hp x)))

/-- Fraction of uniformly sampled period origins in a measurable set. -/
def fraction (P : ℝ) (S : Set ℝ) := mean P (S.indicator (fun _ => (1:ℝ)))

theorem fraction_eq {P : ℝ} (hP : 0<P) {S : Set ℝ} (hS : MeasurableSet S) :
    fraction P S = (volume.restrict (Ioc 0 P)).real S / P := by
  unfold fraction mean
  rw [intervalIntegral.integral_of_le hP.le, integral_indicator hS,setIntegral_const]
  simp

private theorem int_mask {P : ℝ} (hP : 0<P) {S : Set ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 P) :
    IntervalIntegrable (S.indicator f) volume 0 P := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hP.le] at *
  exact hf.indicator hS

private theorem int_flag {P : ℝ} (hP : 0<P) {S : Set ℝ} (hS : MeasurableSet S) :
    IntervalIntegrable (S.indicator (fun _ => (1:ℝ))) volume 0 P :=
  int_mask hP hS intervalIntegrable_const

theorem fraction_markov {P b : ℝ} (hP : 0<P) (hb : 0<b) {f : ℝ → ℝ}
    (hc : Continuous f) (hn : ∀ x, 0≤f x) :
    fraction P {x | b<f x} ≤ mean P f / b := by
  let S := {x | b<f x}
  have hS : MeasurableSet S := (isOpen_lt continuous_const hc).measurableSet
  have h := avg_mono hP ((int_flag hP hS).const_mul b) (hc.intervalIntegrable 0 P)
    (fun x => show b*S.indicator (fun _ => (1:ℝ)) x ≤ f x by
      by_cases hx : x∈S
      · simpa [hx] using (show b≤f x from le_of_lt hx)
      · simpa [hx] using hn x)
  rw [avg_scale] at h
  exact (le_div_iff₀ hb).2 (by simpa [fraction,mul_comm] using h)

theorem fraction_union_le {P : ℝ} (hP : 0<P) {S D : Set ℝ}
    (hS : MeasurableSet S) (hD : MeasurableSet D) :
    fraction P (S ∪ D) ≤ fraction P S + fraction P D := by
  let one := fun _ : ℝ => (1:ℝ)
  have h := avg_mono hP (int_flag hP (hS.union hD))
    ((int_flag hP hS).add (int_flag hP hD)) (fun x =>
      show (S∪D).indicator one x ≤ S.indicator one x + D.indicator one x by
        by_cases hs : x∈S <;> by_cases hd : x∈D <;> simp [hs,hd,one])
  exact h.trans_eq (avg_add (int_flag hP hS) (int_flag hP hD))

theorem fraction_compl {P : ℝ} (hP : 0<P) {S : Set ℝ} (hS : MeasurableSet S) :
    fraction P Sᶜ = 1-fraction P S := by
  have he : Sᶜ.indicator (fun _ => (1:ℝ)) = fun x => 1-S.indicator (fun _ => (1:ℝ)) x := by
    funext x
    by_cases hx : x∈S <;> simp [hx]
  unfold fraction
  rw [he,avg_sub intervalIntegrable_const (int_flag hP hS),avg_const hP]

/-- The contribution on a small set to a mean with bounded second moment.
Completing the square is the quadratic form of Cauchy–Schwarz. -/
theorem small_set_contribution {P m : ℝ} (hP : 0<P) (hm : 0<m) {S : Set ℝ}
    (hS : MeasurableSet S) (hp : fraction P S ≤ m^2/64) {a : ℝ → ℝ}
    (hc : Continuous a) (hsq : mean P (fun x => (a x)^2) ≤ 1) :
    -(m/8) ≤ mean P (S.indicator a) := by
  let q := fun x => (a x)^2
  let i := S.indicator (fun _ => (1:ℝ))
  have hq : IntervalIntegrable q volume 0 P := (hc.pow 2).intervalIntegrable 0 P
  have hi := int_flag hP hS
  have h := avg_mono hP ((hq.const_mul (-(m/16))).sub (hi.const_mul (4/m)))
    (int_mask hP hS (hc.intervalIntegrable 0 P)) (fun x =>
      show -(m/16)*q x-(4/m)*i x ≤ S.indicator a x by
        by_cases hx : x∈S
        · simp [i,hx,q]
          apply (mul_le_mul_iff_of_pos_right hm).mp
          field_simp
          nlinarith [sq_nonneg (m*a x+8)]
        · simp [i,hx,q]
          positivity)
  rw [avg_sub (hq.const_mul (-(m/16))) (hi.const_mul (4/m)),avg_scale,avg_scale] at h
  have h1 := mul_le_mul_of_nonneg_left hsq (show 0≤m/16 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hp (show 0≤4/m by positivity)
  have he : (4/m)*(m^2/64)=m/16 := by field_simp; ring
  rw [he] at h2
  change -(m/16)*mean P (fun x => (a x)^2) - (4/m)*fraction P S ≤ _ at h
  linarith

/-- The only local comparison needed by the global integral argument. The two
conclusions concern one deterministic starting point at a time. -/
def OneWindowComparison (m T cut : ℝ) (u R : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, mass 1 (fun y => (u y)^2+(R y)^2) x ≤ 512/m^2 →
    mass T (fun y => (R y)^2) x ≤ cut →
    -(m/8) ≤ window T u x ∧
      (mass 1 (fun y => (u y)^2+(R y)^2) x ≤ 8 → 7*m/8 ≤ window T u x)

/-- Integrate the two deterministic single-window bounds over all starting
points. Fractions, local-mass bounds and the bad contribution are derived
from the two global second moments. -/
theorem quarter_mean_of_comparison {P m T cut : ℝ} (hP : 0<P) (hm : 0<m) (hm1 : m≤1)
    (hT : 0<T) (hcut : 0<cut) {u R : ℝ → ℝ} (hu : Continuous u) (hR : Continuous R)
    (hup : Periodic u P) (hRp : Periodic R P) (hu2 : mean P (fun x => (u x)^2)=1)
    (hR2 : mean P (fun x => (R x)^2) ≤ 1)
    (hsmall : T*mean P (fun x => (R x)^2) ≤ cut*(m^2/512))
    (cmp : OneWindowComparison m T cut u R) : m/4 ≤ mean P u := by
  let L := mass 1 (fun y => (u y)^2+(R y)^2)
  let B := mass T (fun y => (R y)^2)
  let a := window T u
  let E := {x | 512/m^2<L x}
  let F := {x | cut<B x}
  let D := E∪F
  let H := {x | 8<L x}
  let S := (H∪D)ᶜ
  have hcL : Continuous L := continuous_mass ((hu.pow 2).add (hR.pow 2)) _
  have hcB : Continuous B := continuous_mass (hR.pow 2) _
  have hca : Continuous a := continuous_window hu _
  have hmE : MeasurableSet E := (isOpen_lt continuous_const hcL).measurableSet
  have hmF : MeasurableSet F := (isOpen_lt continuous_const hcB).measurableSet
  have hmH : MeasurableSet H := (isOpen_lt continuous_const hcL).measurableSet
  have hmD : MeasurableSet D := hmE.union hmF
  have hmS : MeasurableSet S := (hmH.union hmD).compl
  have hnL (x : ℝ) : 0≤L x := intervalIntegral.integral_nonneg (by norm_num)
    (fun t _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hnB (x : ℝ) : 0≤B x := intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
  have hLm : mean P L ≤ 2 := by
    dsimp only [L]
    rw [mean_mass hP (by norm_num : (0:ℝ)<1) (f := fun y => (u y)^2+(R y)^2)
      ((hu.pow 2).add (hR.pow 2)) (fun x => by dsimp; rw [hup x,hRp x]),one_mul,
      avg_add (f := fun x => (u x)^2) (g := fun x => (R x)^2)
        ((hu.pow 2).intervalIntegrable 0 P) ((hR.pow 2).intervalIntegrable 0 P),hu2]
    linarith
  have hBm : mean P B = T * mean P (fun x => (R x)^2) :=
    mean_mass hP hT (hR.pow 2) (fun x => congrArg (fun z : ℝ => z^2) (hRp x))
  have hm2 : 0<m^2 := sq_pos_of_pos hm
  have hE : fraction P E ≤ m^2/256 := by
    have hb : 0<512/m^2 := by positivity
    have h := (fraction_markov hP hb hcL hnL).trans
      (div_le_div_of_nonneg_right hLm hb.le)
    exact h.trans_eq (by field_simp; ring)
  have hF : fraction P F ≤ m^2/512 := by
    apply (fraction_markov hP hcut hcB hnB).trans
    apply (div_le_iff₀ hcut).mpr
    rw [hBm]
    linarith
  have hH : fraction P H ≤ 1/4 := by
    have h := (fraction_markov hP (by norm_num : (0:ℝ)<8) hcL hnL).trans
      (div_le_div_of_nonneg_right hLm (by norm_num))
    exact h.trans_eq (by norm_num)
  have hD : fraction P D ≤ m^2/64 := by
    have h := fraction_union_le hP hmE hmF
    dsimp only [D]
    linarith [sq_nonneg m]
  have hS : 1/2≤fraction P S := by
    dsimp only [S]
    rw [fraction_compl hP (hmH.union hmD)]
    have h := fraction_union_le hP hmH hmD
    nlinarith [mul_nonneg hm.le (sub_nonneg.mpr hm1)]
  have hsq : mean P (fun x => (a x)^2) ≤ 1 := (mean_window_square_le hP hT hu hup).trans_eq hu2
  have hbad := small_set_contribution hP hm hmD hD hca hsq
  let i := S.indicator (fun _ => (1:ℝ))
  have hi := int_flag hP hmS
  have hb := int_mask hP hmD (hca.intervalIntegrable 0 P)
  have hpoint (x : ℝ) : -(m/8)+m*i x+D.indicator a x ≤ a x := by
    by_cases hd : x∈D
    · have hs : x∉S := fun hs => hs (Or.inr hd)
      simp [i,hs,hd]
      linarith
    · have hLx : L x ≤ 512/m^2 := le_of_not_gt (fun hx => hd (Or.inl hx))
      have hBx : B x ≤ cut := le_of_not_gt (fun hx => hd (Or.inr hx))
      have h := cmp x hLx hBx
      by_cases hs : x∈S
      · have hL0 : L x ≤ 8 := le_of_not_gt (fun hx => hs (Or.inl hx))
        simp [i,hs,hd]
        have hh : 7*m/8 ≤ a x := h.2 hL0
        linarith
      · simpa [i,hs,hd] using h.1
  have hav := avg_mono hP ((intervalIntegrable_const.add (hi.const_mul m)).add hb)
    (hca.intervalIntegrable 0 P) hpoint
  rw [avg_add (intervalIntegrable_const.add (hi.const_mul m)) hb,
    avg_add intervalIntegrable_const (hi.const_mul m),avg_const hP,avg_scale] at hav
  change -(m/8)+m*fraction P S+mean P (D.indicator a) ≤ mean P (window T u) at hav
  rw [mean_window hP hT hu hup] at hav
  linarith [mul_le_mul_of_nonneg_left hS hm.le]

/-- Normalised elastic force and the residual for the oscillator of positive tilt. -/
def force (u : ℝ → ℝ) (x : ℝ) := deriv (deriv u) x + (1/2:ℝ)*(u x)^3

def residual (u : ℝ → ℝ) (x : ℝ) := force u x-u x/4-1/4

def cubic (P : ℝ) (u : ℝ → ℝ) := mean P (fun x => (u x)^3)

def loss (P : ℝ) (u : ℝ → ℝ) :=
  mean P (fun x => (force u x)^2) - (1/2:ℝ)*mean P (fun x => u x*force u x)

private theorem force_cont {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) : Continuous (force u) :=
  (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu).2).2.continuous.add
    ((hu.continuous.pow 3).const_mul _)

private theorem residual_cont {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) : Continuous (residual u) :=
  ((force_cont hu).sub (hu.continuous.div_const _)).sub continuous_const

private theorem deriv2_periodic {u : ℝ → ℝ} {P : ℝ} (hu : ContDiff ℝ ∞ u)
    (hp : Periodic u P) : Periodic (deriv (deriv u)) P :=
  ActualFlow.actual_deriv_periodic (ActualFlow.actual_deriv_periodic hp (hu.differentiable (by simp)))
    ((contDiff_infty_iff_deriv.mp hu).2.differentiable (by simp))

private theorem residual_per {u : ℝ → ℝ} {P : ℝ} (hu : ContDiff ℝ ∞ u) (hp : Periodic u P) :
    Periodic (residual u) P := by
  intro x
  simp only [residual,force,deriv2_periodic hu hp x,hp x]

private theorem mean_force {u : ℝ → ℝ} {P : ℝ} (hu : ContDiff ℝ ∞ u) (hp : Periodic u P) :
    mean P (force u) = cubic P u / 2 := by
  have hd := (contDiff_infty_iff_deriv.mp hu).2
  have hd2 := (contDiff_infty_iff_deriv.mp hd).2.continuous
  have hp' := ActualFlow.actual_deriv_periodic hp (hu.differentiable (by simp))
  have hend : deriv u P = deriv u 0 := by simpa using hp' 0
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := P)
    (fun x _ => (hd.differentiable (by simp) x).hasDerivAt) (hd2.intervalIntegrable 0 P)
  have hz : mean P (deriv (deriv u))=0 := by simp [mean,hi,hend]
  unfold force cubic
  rw [avg_add (f := deriv (deriv u)) (g := fun x => (1/2:ℝ)*(u x)^3)
    (hd2.intervalIntegrable 0 P)
    (((hu.continuous.pow 3).const_mul (1/2 : ℝ)).intervalIntegrable 0 P),avg_scale,hz]
  ring

/-- This fixed-tilt identity eliminates the auxiliary spatial force mean using
periodicity of the derivative. -/
theorem residual_square_identity {P : ℝ} (hP : 0<P) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hp : Periodic u P) (hu2 : mean P (fun x => (u x)^2)=1) :
    mean P (fun x => (residual u x)^2) = loss P u + (1-2*cubic P u+mean P u)/8 := by
  let v := force u
  have hv : Continuous v := force_cont hu
  have hc := hu.continuous
  let f1 := fun x => (v x)^2-(1/2:ℝ)*(u x*v x)
  let f2 := fun x => f1 x-(1/2:ℝ)*v x
  let f3 := fun x => f2 x+(1/16:ℝ)*(u x)^2
  let f4 := fun x => f3 x+(1/8:ℝ)*u x
  have c1 : Continuous f1 := (hv.pow 2).sub ((hc.mul hv).const_mul _)
  have c2 : Continuous f2 := c1.sub (hv.const_mul _)
  have c3 : Continuous f3 := c2.add ((hc.pow 2).const_mul _)
  have c4 : Continuous f4 := c3.add (hc.const_mul _)
  have he : (fun x => (residual u x)^2) = fun x => f4 x+1/16 := by
    funext x
    dsimp [f4,f3,f2,f1,v,residual]
    ring
  have j1 : mean P f1 = loss P u := by
    dsimp only [f1,loss]
    rw [avg_sub (f := fun x => (v x)^2) (g := fun x => (1/2:ℝ)*(u x*v x))
      ((hv.pow 2).intervalIntegrable 0 P) (((hc.mul hv).const_mul _).intervalIntegrable 0 P),avg_scale]
  have j2 : mean P f2 = mean P f1 - (1/2:ℝ)*mean P v := by
    dsimp only [f2]
    rw [avg_sub (f := f1) (g := fun x => (1/2:ℝ)*v x) (c1.intervalIntegrable 0 P)
      ((hv.const_mul _).intervalIntegrable 0 P),avg_scale]
  have j3 : mean P f3 = mean P f2 + (1/16:ℝ)*mean P (fun x => (u x)^2) := by
    dsimp only [f3]
    rw [avg_add (f := f2) (g := fun x => (1/16:ℝ)*(u x)^2) (c2.intervalIntegrable 0 P)
      (((hc.pow 2).const_mul _).intervalIntegrable 0 P),avg_scale]
  have j4 : mean P f4 = mean P f3 + (1/8:ℝ)*mean P u := by
    dsimp only [f4]
    rw [avg_add (f := f3) (g := fun x => (1/8:ℝ)*u x) (c3.intervalIntegrable 0 P)
      ((hc.const_mul _).intervalIntegrable 0 P),avg_scale]
  have jv : mean P v = cubic P u/2 := mean_force hu hp
  rw [he,avg_add (f := f4) (g := fun _ => (1/16:ℝ)) (c4.intervalIntegrable 0 P)
    intervalIntegrable_const,avg_const hP,j4,j3,j2,j1,hu2,jv]
  ring

/-- The explicit value used by the window argument, before fixing the
deterministic comparison constants. -/
def gapEpsilon (m T τ : ℝ) :=
  min (1/8:ℝ) (min (m/16) (m^2*τ^2/(1024*T^2)))

theorem gapEpsilon_pos {m T τ : ℝ} (hm : 0<m) (hT : 0<T) (hτ : 0<τ) :
    0<gapEpsilon m T τ := by
  unfold gapEpsilon
  positivity

theorem gapEpsilon_lt_half (m T τ : ℝ) : gapEpsilon m T τ < 1/2 :=
  (min_le_left _ _).trans_lt (by norm_num)

private theorem cubic_upper {P m T τ : ℝ} (hP : 0<P) (hm : 0<m) (hm1 : m≤1)
    (hT : 0<T) (hτ : 0<τ) {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hp : Periodic u P)
    (hu2 : mean P (fun x => (u x)^2)=1) (hs : |mean P u| ≤ gapEpsilon m T τ)
    (he : loss P u ≤ gapEpsilon m T τ)
    (cmp : OneWindowComparison m T (τ^2/T) u (residual u)) :
    cubic P u ≤ 1/2-gapEpsilon m T τ := by
  let ε := gapEpsilon m T τ
  have h8 : ε≤1/8 := min_le_left _ _
  have h16 : ε≤m/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hε : ε≤m^2*τ^2/(1024*T^2) := (min_le_right _ _).trans (min_le_right _ _)
  have hεpos : 0<ε := gapEpsilon_pos hm hT hτ
  have hmean : mean P u ≤ ε := (le_abs_self _).trans hs
  by_contra! h
  have hid := residual_square_identity hP hu hp hu2
  have hR : mean P (fun x => (residual u x)^2) ≤ 2*ε := by
    change 1/2-ε < cubic P u at h
    change loss P u ≤ ε at he
    linarith
  have hnum := (le_div_iff₀ (show 0<1024*T^2 by positivity)).mp hε
  have hsize : T*mean P (fun x => (residual u x)^2) ≤ (τ^2/T)*(m^2/512) := by
    apply (mul_le_mul_iff_of_pos_right hT).mp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hR (sq_nonneg T)]
  have hi := quarter_mean_of_comparison hP hm hm1 hT (by positivity : 0<τ^2/T)
    hu.continuous (residual_cont hu) hp (residual_per hu hp) hu2 (by linarith) hsize cmp
  linarith

/-- Uniform deterministic one-window estimate for the positive-tilt equation.
It only asks about a smooth scalar function at a point, given the two local
mass bounds in OneWindowComparison. -/
def OscillatorWindowComparison (m T cut : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → OneWindowComparison m T cut u (residual u)

private theorem force_neg (u : ℝ → ℝ) (x : ℝ) : force (-u) x = -force u x := by
  simp [force,deriv.fun_neg]
  ring

private theorem loss_neg (u : ℝ → ℝ) (P : ℝ) : loss P (-u) = loss P u := by
  simp [loss,force_neg]

private theorem cubic_neg (u : ℝ → ℝ) (P : ℝ) : cubic P (-u) = -cubic P u := by
  have h : (fun x => ((-u) x)^3) = fun x => -((u x)^3) := by
    funext x
    change (-u x)^3 = -((u x)^3)
    ring
  unfold cubic mean
  rw [h,intervalIntegral.integral_neg,neg_div]

/-- Scalar strict half-gap with the fixed explicit epsilon. The only remaining
analytic input is deterministic comparison over a single good window.
The signed reversal in the cubic moment is carried out here. -/
theorem scalar_strict_half_gap {m T τ : ℝ} (hm : 0<m) (hm1 : m≤1) (hT : 0<T) (hτ : 0<τ)
    (cmp : OscillatorWindowComparison m T (τ^2/T)) {u : ℝ → ℝ} {P : ℝ}
    (hP : 0<P) (hu : ContDiff ℝ ∞ u) (hp : Periodic u P) (hu2 : mean P (fun x => (u x)^2)=1)
    (hs : |mean P u| ≤ gapEpsilon m T τ) (he : loss P u ≤ gapEpsilon m T τ) :
    |cubic P u| ≤ 1/2-gapEpsilon m T τ := by
  apply abs_le.mpr
  have hneg := cubic_upper (u := -u) hP hm hm1 hT hτ hu.neg
    (fun x => congrArg Neg.neg (hp x)) (by simpa using hu2)
    (by simpa [mean,neg_div] using hs) (by simpa [loss_neg] using he) (cmp _ hu.neg)
  rw [cubic_neg] at hneg
  exact ⟨by linarith,cubic_upper hP hm hm1 hT hτ hu hp hu2 hs he (cmp _ hu)⟩

end LengthGrowth.PeriodicWindowGap

open Lean Elab Command in
run_cmd do
  let names := #[`LengthGrowth.PeriodicWindowGap.mass_eq_interval,
    `LengthGrowth.PeriodicWindowGap.mean_mass,
    `LengthGrowth.PeriodicWindowGap.mean_window,
    `LengthGrowth.PeriodicWindowGap.mean_window_square_le,
    `LengthGrowth.PeriodicWindowGap.fraction_eq,
    `LengthGrowth.PeriodicWindowGap.fraction_markov,
    `LengthGrowth.PeriodicWindowGap.fraction_union_le,
    `LengthGrowth.PeriodicWindowGap.fraction_compl,
    `LengthGrowth.PeriodicWindowGap.small_set_contribution,
    `LengthGrowth.PeriodicWindowGap.quarter_mean_of_comparison,
    `LengthGrowth.PeriodicWindowGap.residual_square_identity,
    `LengthGrowth.PeriodicWindowGap.gapEpsilon_pos,
    `LengthGrowth.PeriodicWindowGap.gapEpsilon_lt_half,
    `LengthGrowth.PeriodicWindowGap.scalar_strict_half_gap]
  for name in names do
    for ax in (← collectAxioms name) do
      unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo "PERIODIC_WINDOW_GAP: exact periodic averaging, Jensen, bad origins, residual square, signed static gap."
