import Lemniscate.SquareWeierstrass
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! The second-order Weierstrass equation, including critical points.
Differentiation of the first integral gives the equation multiplied by P'.
Analyticity and the pole of P' remove this factor without division at zeros. -/
namespace Lemniscate
open Complex Filter Set
open scoped Topology

theorem weierstrass_second_order (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP
      (6*(L.weierstrassP z)^2-L.g₂/2) z := by
  classical
  let U : Set ℂ := (L.lattice : Set ℂ)ᶜ
  let R : ℂ → ℂ := fun w => deriv L.derivWeierstrassP w -
    (6*(L.weierstrassP w)^2-L.g₂/2)
  have hR : AnalyticOnNhd ℂ R U := by
    intro w hw
    have hP := L.analyticOnNhd_weierstrassP w hw
    have hD := L.analyticOnNhd_derivWeierstrassP w hw
    exact hD.deriv.sub ((analyticAt_const.mul (hP.pow 2)).sub analyticAt_const)
  have hprod (w : ℂ) (hw : w ∈ U) : R w*L.derivWeierstrassP w = 0 := by
    have hP := (L.analyticOnNhd_weierstrassP w hw).differentiableAt.hasDerivAt
    rw [L.deriv_weierstrassP] at hP
    have hD := (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt.hasDerivAt
    have heq : (fun t => (L.derivWeierstrassP t)^2) =ᶠ[𝓝 w]
        (fun t => 4*(L.weierstrassP t)^3-L.g₂*L.weierstrassP t-L.g₃) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with t ht
      exact L.derivWeierstrassP_sq t ht
    have hd := heq.deriv_eq
    rw [(hD.fun_pow 2).deriv,
      ((((hP.fun_pow 3).const_mul 4).fun_sub (hP.const_mul L.g₂)).fun_sub
        (hasDerivAt_const w L.g₃)).deriv] at hd
    dsimp only [R]
    norm_num only [Nat.reduceSub,pow_one] at hd
    linear_combination (1/2:ℂ)*hd
  have hcountType : Countable L.lattice :=
    L.latticeEquivProd.toEquiv.countable_iff.mpr inferInstance
  have hcount : (L.lattice : Set ℂ).Countable := Set.countable_coe_iff.mp hcountType
  have hU : IsPreconnected U :=
    (hcount.isPathConnected_compl_of_one_lt_rank
      (by simp only [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hnzero : ¬(∀ w ∈ U, L.derivWeierstrassP w = 0) := by
    intro hall
    have hnear : ∀ᶠ w in 𝓝[≠] (0:ℂ), w ∈ U := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds (0:ℂ))]
        with w hw0 hw
      exact fun hwL => hw ⟨hwL,hw0⟩
    have heq : L.derivWeierstrassP =ᶠ[𝓝[≠] (0:ℂ)] (fun _ => 0) :=
      hnear.mono fun w hw => hall w hw
    have ho : meromorphicOrderAt L.derivWeierstrassP 0 = (-3:WithTop ℤ) := by
      rw [← L.deriv_weierstrassP]
      simpa using meromorphicOrderAt_deriv_eq_sub_one
        (f := L.weierstrassP) (x := (0:ℂ)) (n := (-2:ℤ))
        (by norm_num) (by simpa using L.order_weierstrassP 0 L.lattice.zero_mem)
    have h := meromorphicOrderAt_congr heq
    rw [ho,meromorphicOrderAt_const] at h
    norm_num at h
  obtain hzero | hzero := hR.eq_zero_or_eq_zero_of_mul_eq_zero
    L.analyticOnNhd_derivWeierstrassP hprod hU
  · have hD := (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
    rw [sub_eq_zero.mp (hzero z hz)] at hD
    exact hD
  · exact (hnzero hzero).elim

end Lemniscate
