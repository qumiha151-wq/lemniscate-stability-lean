import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Util.CollectAxioms

/-! Finite-order Taylor limits for continuation across curvature zeros.
This module does not assume or claim global reconstruction. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace ClosedSimilarity.ScalarReconstruction

theorem zero_jets_isLittleO (f : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ j≤m, iteratedDeriv j f z=0) :
    f =o[𝓝 z] (fun x => (x-z)^m) := by
  induction m generalizing f with
  | zero =>
    have hz : f z=0 := hzero 0 le_rfl
    simpa only [pow_zero] using
      ((Asymptotics.isLittleO_one_iff ℝ).mpr (hz ▸ hf.continuous.continuousAt))
  | succ m ih =>
    have hfd := (contDiff_infty_iff_deriv.mp hf).2
    have hj : ∀ j≤m, iteratedDeriv j (deriv f) z=0 := by
      intro j hj
      rw [← iteratedDeriv_succ']
      exact hzero (j+1) (Nat.succ_le_succ hj)
    have hh := Convex.isLittleO_pow_succ_real convex_univ (mem_univ z)
      (fun x _ => (hf.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt)
      (by simpa only [nhdsWithin_univ] using ih _ hfd hj)
    have hz : f z=0 := hzero 0 (Nat.zero_le _)
    simpa only [nhdsWithin_univ,hz,sub_zero] using hh

theorem normalized_curvature_tendsto (f : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hf : ContDiff ℝ ∞ f) (hzero : ∀ j<m, iteratedDeriv j f z=0) :
    Tendsto (fun x => f x/(x-z)^m) (𝓝[≠] z)
      (𝓝 (iteratedDeriv m f z/(Nat.factorial m : ℝ))) := by
  let c := iteratedDeriv m f z/(Nat.factorial m : ℝ)
  have hp : ContDiff ℝ ∞ (fun x : ℝ => c*(x-z)^m) :=
    contDiff_const.mul ((contDiff_id.sub contDiff_const).pow m)
  have hj : ∀ j≤m, iteratedDeriv j (fun x => f x-c*(x-z)^m) z=0 := by
    intro j hj
    rw [iteratedDeriv_fun_sub (n := j)
      ((hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt)
      ((hp.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffAt),
      iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_sub_const j (fun x : ℝ => x^m) z]
    simp only [sub_self,iteratedDeriv_fun_pow_zero]
    by_cases he : j=m
    · subst j
      simp only [ite_true,c]
      rw [div_mul_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero m)]
      ring
    · simp only [if_neg he,hzero j (lt_of_le_of_ne hj he),Nat.cast_zero,mul_zero,sub_zero]
  have ho := (zero_jets_isLittleO _ z m (hf.sub hp) hj).tendsto_div_nhds_zero
  have ht : Tendsto (fun x => (f x-c*(x-z)^m)/(x-z)^m) (𝓝[≠] z) (𝓝 0) := by
    exact ho.mono_left nhdsWithin_le_nhds
  have he : (fun x => (f x-c*(x-z)^m)/(x-z)^m+c) =ᶠ[𝓝[≠] z]
      (fun x => f x/(x-z)^m) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxz : x-z ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have hh := ht.add_const c
  simpa only [zero_add] using hh.congr' he

theorem vanishing_quotient_tendsto_zero (f g : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfzero : ∀ j≤m, iteratedDeriv j f z=0)
    (hgzero : ∀ j<m, iteratedDeriv j g z=0)
    (hglead : iteratedDeriv m g z ≠ 0) :
    Tendsto (fun x => f x/g x) (𝓝[≠] z) (𝓝 0) := by
  have hft := normalized_curvature_tendsto f z m hf (fun j hj => hfzero j hj.le)
  rw [hfzero m le_rfl,zero_div] at hft
  have hgt := normalized_curvature_tendsto g z m hg hgzero
  have hc : iteratedDeriv m g z/(Nat.factorial m : ℝ) ≠ 0 :=
    div_ne_zero hglead (by exact_mod_cast Nat.factorial_ne_zero m)
  have ht := hft.div hgt hc
  have he : (fun x => (f x/(x-z)^m)/(g x/(x-z)^m)) =ᶠ[𝓝[≠] z]
      (fun x => f x/g x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_div_div_cancel_right₀ (pow_ne_zero _ (sub_ne_zero.mpr hx)) _ _
  simpa only [zero_div] using ht.congr' he

theorem finite_order_eventually_ne_zero (g : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hg : ContDiff ℝ ∞ g) (hzero : ∀ j<m, iteratedDeriv j g z=0)
    (hlead : iteratedDeriv m g z ≠ 0) :
    ∀ᶠ x in 𝓝[≠] z, g x ≠ 0 := by
  have ht := normalized_curvature_tendsto g z m hg hzero
  have hc : iteratedDeriv m g z/(Nat.factorial m : ℝ) ≠ 0 :=
    div_ne_zero hlead (by exact_mod_cast Nat.factorial_ne_zero m)
  filter_upwards [ht.eventually_ne hc] with x hx
  exact fun hgx => hx (by simp only [hgx,zero_div])

theorem zero_jets_at_right_endpoint (f : ℝ → ℝ) (a z : ℝ)
    (hf : ContDiff ℝ ∞ f) (haz : a<z) (hz : ∀ x∈Icc a z, f x=0) :
    ∀ j, iteratedDeriv j f z=0 := by
  intro j
  have he : EqOn f (fun _ => (0:ℝ)) (Ioo a z) :=
    fun x hx => hz x ⟨hx.1.le,hx.2.le⟩
  have hj := he.iteratedDeriv_of_isOpen isOpen_Ioo j
  have hc : IsClosed {x | iteratedDeriv j f x=0} :=
    isClosed_eq (hf.continuous_iteratedDeriv j
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)) continuous_const
  have hs : Ioo a z ⊆ {x | iteratedDeriv j f x=0} := by
    intro x hx
    simpa [iteratedDeriv_const] using hj hx
  have hcl := closure_minimal hs hc
  rw [closure_Ioo haz.ne] at hcl
  exact hcl (right_mem_Icc.mpr haz.le)

/-- A smooth Wronskian-zero pair continues the zero numerator to the right of a
finite-order zero of its denominator. Both the isolation and quotient limit are
derived from the jets, rather than assumed. -/
theorem zero_right_of_finite_order (f g : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hwr : ∀ x, g x*deriv f x-deriv g x*f x=0)
    (hfzero : ∀ j≤m, iteratedDeriv j f z=0)
    (hgzero : ∀ j<m, iteratedDeriv j g z=0)
    (hglead : iteratedDeriv m g z≠0) :
    ∀ᶠ x in 𝓝[>] z, f x=0 := by
  have hfilter : 𝓝[>] z ≤ 𝓝[≠] z :=
    nhdsWithin_mono z (fun x hx => ne_of_gt hx)
  have hne : ∀ᶠ x in 𝓝[>] z, g x≠0 :=
    (finite_order_eventually_ne_zero g z m hg hgzero hglead).filter_mono hfilter
  obtain ⟨e, hze, he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hne
  change z<e at hze
  let q := fun x => f x/g x
  have hd : ∀ x∈Ioo z e, HasDerivAt q 0 x := by
    intro x hx
    have hh := (hf.differentiable (by simp) x).hasDerivAt.fun_div
      (hg.differentiable (by simp) x).hasDerivAt (he hx)
    have hz : deriv f x*g x-f x*deriv g x=0 := by
      convert hwr x using 1; ring
    simpa only [hz,zero_div] using hh
  obtain ⟨y, hzy, hye⟩ := exists_between hze
  have hconst : ∀ x∈Ioo z e, q x=q y := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo z e).isPreconnected
      (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).deriv) hx ⟨hzy,hye⟩
  have ht : Tendsto q (𝓝[>] z) (𝓝 0) :=
    (vanishing_quotient_tendsto_zero f g z m hf hg hfzero hgzero hglead).mono_left hfilter
  have htc : Tendsto q (𝓝[>] z) (𝓝 (q y)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsGT hze] with x hx
    exact (hconst x hx).symm
  have hqy : q y=0 := tendsto_nhds_unique htc ht
  filter_upwards [Ioo_mem_nhdsGT hze] with x hx
  have hqx : q x=0 := (hconst x hx).trans hqy
  exact (div_eq_zero_iff.mp hqx).resolve_right (he hx)

theorem zero_jets_at_left_endpoint (f : ℝ → ℝ) (z b : ℝ)
    (hf : ContDiff ℝ ∞ f) (hzb : z<b) (hz : ∀ x∈Icc z b, f x=0) :
    ∀ j, iteratedDeriv j f z=0 := by
  intro j
  have he : EqOn f (fun _ => (0:ℝ)) (Ioo z b) :=
    fun x hx => hz x ⟨hx.1.le,hx.2.le⟩
  have hj := he.iteratedDeriv_of_isOpen isOpen_Ioo j
  have hc : IsClosed {x | iteratedDeriv j f x=0} :=
    isClosed_eq (hf.continuous_iteratedDeriv j
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)) continuous_const
  have hs : Ioo z b ⊆ {x | iteratedDeriv j f x=0} := by
    intro x hx
    simpa [iteratedDeriv_const] using hj hx
  have hcl := closure_minimal hs hc
  rw [closure_Ioo hzb.ne] at hcl
  exact hcl (left_mem_Icc.mpr hzb.le)

theorem zero_left_of_finite_order (f g : ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hwr : ∀ x, g x*deriv f x-deriv g x*f x=0)
    (hfzero : ∀ j≤m, iteratedDeriv j f z=0)
    (hgzero : ∀ j<m, iteratedDeriv j g z=0)
    (hglead : iteratedDeriv m g z≠0) :
    ∀ᶠ x in 𝓝[<] z, f x=0 := by
  have hfilter : 𝓝[<] z ≤ 𝓝[≠] z :=
    nhdsWithin_mono z (fun x hx => ne_of_lt hx)
  have hne : ∀ᶠ x in 𝓝[<] z, g x≠0 :=
    (finite_order_eventually_ne_zero g z m hg hgzero hglead).filter_mono hfilter
  obtain ⟨e, hez, he⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hne
  change e<z at hez
  change Ioo e z ⊆ {x | g x≠0} at he
  let q := fun x => f x/g x
  have hd : ∀ x∈Ioo e z, HasDerivAt q 0 x := by
    intro x hx
    have hh := (hf.differentiable (by simp) x).hasDerivAt.fun_div
      (hg.differentiable (by simp) x).hasDerivAt (he hx)
    have hz : deriv f x*g x-f x*deriv g x=0 := by
      convert hwr x using 1; ring
    simpa only [hz,zero_div] using hh
  obtain ⟨y, hey, hyz⟩ := exists_between hez
  have hconst : ∀ x∈Ioo e z, q x=q y := by
    intro x hx
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo e z).isPreconnected
      (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).deriv) hx ⟨hey,hyz⟩
  have ht : Tendsto q (𝓝[<] z) (𝓝 0) :=
    (vanishing_quotient_tendsto_zero f g z m hf hg hfzero hgzero hglead).mono_left hfilter
  have htc : Tendsto q (𝓝[<] z) (𝓝 (q y)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Ioo_mem_nhdsLT hez] with x hx
    exact (hconst x hx).symm
  have hqy : q y=0 := tendsto_nhds_unique htc ht
  filter_upwards [Ioo_mem_nhdsLT hez] with x hx
  have hqx : q x=0 := (hconst x hx).trans hqy
  exact (div_eq_zero_iff.mp hqx).resolve_right (he hx)

end ClosedSimilarity.ScalarReconstruction

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (← getEnv).constants do
    if (`ClosedSimilarity.ScalarReconstruction).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless (#[`propext,`Classical.choice,`Quot.sound] : Array Name).contains axiomName do
          throwError "Scalar zeros audit failed: {name} depends on {axiomName}"
      count := count+1
  logInfo m!"Scalar zeros audit passed for {count} declarations."
