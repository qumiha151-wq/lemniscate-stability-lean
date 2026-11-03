import Lemniscate.WeierstrassEquation
import Mathlib.Tactic.FunProp

/-! A real period on a regular horizontal line is a lattice period.
The identity principle and the double pole at zero prove the converse
to lattice periodicity, without a zero-counting argument. -/
namespace Lemniscate
open Complex Filter Set
open scoped Topology

theorem weierstrass_real_line_period_mem (L : PeriodPair) (c : ℂ) (d : ℝ)
    (hc : c ∉ L.lattice) (hcd : c+(d:ℂ) ∉ L.lattice)
    (hperiod : ∀ x : ℝ, L.weierstrassP ((x:ℂ)+c+(d:ℂ)) =
      L.weierstrassP ((x:ℂ)+c)) : (d:ℂ) ∈ L.lattice := by
  classical
  let U : Set ℂ := ((L.lattice : Set ℂ) ∪
    (fun z : ℂ => z+(d:ℂ)) ⁻¹' (L.lattice : Set ℂ))ᶜ
  have hmem (z : ℂ) : z ∈ U ↔ z ∉ L.lattice ∧ z+(d:ℂ) ∉ L.lattice := by
    simp only [U,mem_compl_iff,mem_union,mem_preimage,not_or,SetLike.mem_coe]
  have hcountType : Countable L.lattice :=
    L.latticeEquivProd.toEquiv.countable_iff.mpr inferInstance
  have hcount : (L.lattice : Set ℂ).Countable := Set.countable_coe_iff.mp hcountType
  have hcountU : ((L.lattice : Set ℂ) ∪
      (fun z : ℂ => z+(d:ℂ)) ⁻¹' (L.lattice : Set ℂ)).Countable :=
    hcount.union (hcount.preimage (fun _ _ h => add_right_cancel h))
  have hconn : IsPreconnected U :=
    (hcountU.isPathConnected_compl_of_one_lt_rank
      (by simp only [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => L.weierstrassP (z+(d:ℂ))) U := by
    intro z hz
    have hs : AnalyticAt ℂ (fun w : ℂ => w+(d:ℂ)) z := by fun_prop
    convert! (L.analyticOnNhd_weierstrassP _ ((hmem z).mp hz).2).comp
      (f := fun w : ℂ => w+(d:ℂ)) hs using 1
  have hg : AnalyticOnNhd ℂ L.weierstrassP U :=
    fun z hz => L.analyticOnNhd_weierstrassP z (hmem z |>.mp hz).1
  have hmaps : MapsTo (fun x : ℝ => (x:ℂ)+c) ({0}:Set ℝ)ᶜ ({c}:Set ℂ)ᶜ := by
    intro x hx
    simp only [mem_compl_iff,mem_singleton_iff] at hx ⊢
    intro h
    have hxC : (x:ℂ) = 0 := by linear_combination h
    exact hx (Complex.ofReal_eq_zero.mp hxC)
  have hcont : ContinuousAt (fun x : ℝ => (x:ℂ)+c) 0 :=
    Complex.continuous_ofReal.continuousAt.add_const c
  have ht : Tendsto (fun x : ℝ => (x:ℂ)+c) (𝓝[≠] (0:ℝ)) (𝓝[≠] c) := by
    simpa only [Complex.ofReal_zero,zero_add] using
      hcont.continuousWithinAt.tendsto_nhdsWithin hmaps
  have hfreq : ∃ᶠ z in 𝓝[≠] c, L.weierstrassP (z+(d:ℂ)) = L.weierstrassP z :=
    ht.frequently (Frequently.of_forall hperiod)
  have heq := hf.eqOn_of_preconnected_of_frequently_eq hg hconn
    ((hmem c).mpr ⟨hc,hcd⟩) hfreq
  by_contra hd
  have hnearL : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∉ L.lattice := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds (0:ℂ))]
      with z hz0 hz
    exact fun hzL => hz ⟨hzL,hz0⟩
  have hnearD : ∀ᶠ z in 𝓝[≠] (0:ℂ), z+(d:ℂ) ∉ L.lattice := by
    have htD : Tendsto (fun z : ℂ => z+(d:ℂ)) (𝓝[≠] (0:ℂ)) (𝓝 (d:ℂ)) := by
      have hs : ContinuousAt (fun z : ℂ => z+(d:ℂ)) 0 := by fun_prop
      simpa only [zero_add] using hs.tendsto.mono_left nhdsWithin_le_nhds
    exact htD.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hd)
  have hnear : (fun z : ℂ => L.weierstrassP (z+(d:ℂ))) =ᶠ[𝓝[≠] (0:ℂ)] L.weierstrassP := by
    filter_upwards [hnearL,hnearD] with z hzL hzD
    exact heq ((hmem z).mpr ⟨hzL,hzD⟩)
  have han : AnalyticAt ℂ (fun z : ℂ => L.weierstrassP (z+(d:ℂ))) 0 := by
    have hP : AnalyticAt ℂ L.weierstrassP ((0:ℂ)+(d:ℂ)) := by
      simpa only [zero_add] using L.analyticOnNhd_weierstrassP (d:ℂ) hd
    have hs : AnalyticAt ℂ (fun w : ℂ => w+(d:ℂ)) 0 := by fun_prop
    convert! hP.comp (f := fun w : ℂ => w+(d:ℂ)) hs using 1
  have horder := han.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr hnear,L.order_weierstrassP 0 L.lattice.zero_mem] at horder
  exact (by decide : ¬ (0:WithTop ℤ) ≤ -2) horder

end Lemniscate
