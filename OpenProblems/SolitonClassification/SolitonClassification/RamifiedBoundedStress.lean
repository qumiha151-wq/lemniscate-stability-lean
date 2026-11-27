import SolitonClassification.RamifiedBoundedFill

noncomputable section
open Complex Set Filter
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded

def speed (m : ℕ) (z : ℂ) := (m:ℂ)*z^(m-1)

theorem speed_analytic (m : ℕ) : AnalyticAt ℂ (speed m) 0 := by
  unfold speed
  fun_prop

theorem speed_ne {m : ℕ} (hm : 0<m) {z : ℂ} (hz : z≠0) : speed m z≠0 :=
  mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (pow_ne_zero _ hz)

/-- Support equations for s=s₀+wᵐ, written in the uniformizer. -/
def Laws (m : ℕ) (a b : ℂ) (k v F h : ℂ→ℂ) (z : ℂ) : Prop :=
  HasDerivAt k (speed m z*v z) z ∧
  HasDerivAt v (speed m z*(F z-k z^3/2)) z ∧
  HasDerivAt F (speed m z*(k z*h z-b)) z ∧
  HasDerivAt h (speed m z*(a-k z*F z)) z

/-- No independent regularity of the slope or support variables at the
puncture is assumed. They are recovered from the continued curvature and
the differential equations. -/
theorem stress_fills {m : ℕ} {a b : ℂ} {k v F h : ℂ→ℂ}
    (hm : 0<m) (fk : Fills k)
    (nk : ∀ᶠ z in 𝓝[≠] (0:ℂ), k z≠0)
    (law : ∀ᶠ z in 𝓝[≠] (0:ℂ), Laws m a b k v F h z) :
    Fills v ∧ Fills F ∧ Fills h := by
  let J := speed m
  have fJ : Fills J := Fills.of_analytic (speed_analytic m)
  have mJ := fJ.meromorphic
  have mk := fk.meromorphic
  have nJ : ∀ᶠ z in 𝓝[≠] (0:ℂ), J z≠0 :=
    eventually_mem_nhdsWithin.mono (fun _ hz=>speed_ne hm hz)
  have mv : MeromorphicAt v 0 := (mk.deriv.div mJ).congr (by
    filter_upwards [nJ,law] with z n l
    change deriv k z / J z=v z
    rw [l.1.deriv]
    change J z*v z/J z=v z
    field_simp)
  have mF : MeromorphicAt F 0 :=
    ((mv.deriv.div mJ).add ((mk.pow 3).div (fills_const 2).meromorphic)).congr (by
      filter_upwards [nJ,law] with z n l
      change deriv v z/J z+k z^3/2=F z
      rw [l.2.1.deriv]
      change J z*(F z-k z^3/2)/J z+k z^3/2=F z
      field_simp
      ring)
  have mh : MeromorphicAt h 0 :=
    (((mF.deriv.div mJ).add (fills_const b).meromorphic).div mk).congr (by
      filter_upwards [nJ,nk,law] with z n nz l
      change (deriv F z/J z+b)/k z=h z
      rw [l.2.2.1.deriv]
      change (J z*(k z*h z-b)/J z+b)/k z=h z
      field_simp
      ring)
  let U (z:ℂ) := F z+I*h z
  let V (z:ℂ) := F z-I*h z
  have mI : MeromorphicAt (fun _:ℂ=>I) 0 := (fills_const I).meromorphic
  have fU : Fills U := linear_fills (mF.add (mI.mul mh))
    ((fJ.mul (fills_const (-I))).mul fk) (fJ.mul (fills_const (-b+I*a))) (by
      filter_upwards [law] with z l
      change deriv (fun w=>F w+I*h w) z=_
      apply ((l.2.2.1.fun_add (l.2.2.2.const_mul I)).deriv).trans
      dsimp [J,U]
      linear_combination (speed m z)*(k z)*(h z)*I_sq)
  have fV : Fills V := linear_fills (mF.sub (mI.mul mh))
    ((fJ.mul (fills_const I)).mul fk) (fJ.mul (fills_const (-b-I*a))) (by
      filter_upwards [law] with z l
      change deriv (fun w=>F w-I*h w) z=_
      apply ((l.2.2.1.fun_sub (l.2.2.2.const_mul I)).deriv).trans
      dsimp [J,V]
      linear_combination (speed m z)*(k z)*(h z)*I_sq)
  have fF : Fills F := ((fU.add fV).mul (fills_const (1/2))).congr (by
    filter_upwards with z
    dsimp [U,V]
    ring)
  have fh : Fills h := ((fU.sub fV).mul (fills_const (-I/2))).congr (by
    filter_upwards with z
    dsimp [U,V]
    linear_combination (h z)*I_sq)
  refine ⟨linear_fills mv (fills_const 0)
    (fJ.mul (fF.sub ((fk.pow 3).mul (fills_const (1/2))))) ?_,fF,fh⟩
  filter_upwards [law] with z l
  rw [l.2.1.deriv]
  dsimp [J]
  ring

#print axioms stress_fills
end ClosedSimilarity.RamifiedBounded
