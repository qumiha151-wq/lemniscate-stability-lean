import LengthGrowth.ActualFlow.FiniteSignFlow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Turn a deficit at high energy-length product into a global physical
time barrier. The exponent q is positive and need not be rational. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

def stressScale (c : ForwardImmersion) (t : ℝ) : ℝ :=
  Real.sqrt (c.dissipation t*c.length t^3/(2*c.energy t^2))

theorem density_stress_control (c : ForwardImmersion) {t : ℝ} (ht : 0≤t) :
    1≤c.stressScale t ∧ c.energy t*c.lengthRate t*c.stressScale t ≤
      c.dissipation t*c.length t*Real.sqrt (c.normalizedProduct t) := by
  let E:=c.energy t
  let L:=c.length t
  let D:=c.dissipation t
  let z:=c.stressScale t
  let x:=Real.sqrt (c.normalizedProduct t)
  have he : 0<E:=c.energy_pos ht
  have hl : 0<L:=c.length_pos ht
  have hd : 0≤D:=c.dissipation_nonneg t
  have hz : 0≤z:=Real.sqrt_nonneg _
  have hx : 0≤x:=Real.sqrt_nonneg _
  have xx : x^2=E*L:=Real.sq_sqrt (mul_pos he hl).le
  have zz : z^2*(2*E^2)=D*L^3 := (eq_div_iff (by positivity : 2*E^2≠0)).mp
    (Real.sq_sqrt (by positivity : 0≤D*L^3/(2*E^2)))
  constructor
  · change 1≤z
    by_contra! hh
    have sq:=mul_self_lt_mul_self hz hh
    have hv : 4*Real.pi^2*E^2≤D*L^3:=c.sharp_virial ht
    nlinarith only [zz,hv,mul_lt_mul_of_pos_right sq (by positivity : 0<2*E^2),
      mul_nonneg (show 0≤4*Real.pi^2-2 by nlinarith [Real.pi_gt_three]) (sq_nonneg E)]
  · change E*c.lengthRate t*z≤D*L*x
    have raw : (c.lengthRate t)^2≤2*E*D := c.lengthRate_sq_le ht
    have sq : (E*c.lengthRate t*z)^2≤(D*L*x)^2 := by
      calc
        _ ≤ (2*E*D)*(E^2*z^2) := by
          nlinarith only [mul_le_mul_of_nonneg_right raw (mul_nonneg (sq_nonneg E) (sq_nonneg z))]
        _ = (z^2*(2*E^2))*(E*D) := by ring
        _ = (D*L*x)^2 := by rw [zz,mul_pow,mul_pow,xx]; ring
    by_contra! hh
    exact (not_lt_of_ge sq) (sq_lt_sq' (by linarith only [hh,show 0≤D*L*x by positivity]) hh)

/-- The hypothesis compares the square-root scales only on large-product
slices; the sharp virial covers all smaller products. -/
theorem density_log_barrier (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T q H U₀ : ℝ} (hT : 0≤T) (hq : 0<q) (hH : 0≤H)
    (high : ∀t>T,U₀≤c.normalizedProduct t →
      c.normalizedProduct t^q*(Real.sqrt (c.normalizedProduct t)-c.stressScale t) ≤
        H*Real.sqrt (c.normalizedProduct t)) :
    ∃ K : ℝ, 0≤K ∧ AntitoneOn
      (fun t => c.normalizedProduct t^q+K*Real.log (c.energy t)) (Ici T) := by
  let M := max (max 1 U₀) ((2*H+1)^(1/q))
  have hM : 1≤M := (le_max_left _ _).trans (le_max_left _ _)
  have Mp : 0<M := zero_lt_one.trans_le hM
  have big : 2*H≤M^q := by
    have raw := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity : 0≤2*H+1) (1/q))
      (show (2*H+1)^(1/q)≤M from le_max_right _ _) hq.le
    rw [←Real.rpow_mul (by positivity : 0≤2*H+1),
      show (1/q)*q=1 by field_simp,Real.rpow_one] at raw
    linarith
  let K := 2*H+M^q*Real.sqrt M
  have kpos : 0≤K := by dsimp [K]; positivity
  refine ⟨q*K,mul_nonneg hq.le kpos,?_⟩
  let W := fun t => c.normalizedProduct t^q+q*K*Real.log (c.energy t)
  have sub : Ici T ⊆ Ici 0 := fun _ hh => hT.trans hh
  have hc : ContinuousOn W (Ici T) :=
    ((c.normalizedProduct_continuousOn.mono sub).rpow_const (fun _ _ => Or.inr hq.le)).add
      (continuousOn_const.mul (c.log_energy_continuousOn.mono sub))
  have dw {t : ℝ} (ht : T<t) : HasDerivAt W
      (q*c.normalizedProduct t^(q-1)*(c.energy t*c.lengthRate t-c.length t*c.dissipation t)
        +q*K*(-c.dissipation t/c.energy t)) t := by
    have h := hT.trans_lt ht
    have pos : 0<c.normalizedProduct t := mul_pos (c.energy_pos h.le) (c.length_pos h.le)
    exact (((Real.hasDerivAt_rpow_const (p:=q) (Or.inl pos.ne')).comp t
      (c.normalizedProduct_hasDerivAt_normal hf h))).add
      (((c.energy_hasDerivAt_normal hf h).log (c.energy_pos h.le).ne').const_mul (q*K))
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) hc
  · rw [interior_Ici]
    intro t ht
    exact (dw ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro t ht
    rw [(dw ht).deriv]
    have ht0:=hT.trans (le_of_lt ht)
    let U:=c.normalizedProduct t
    let z:=c.stressScale t
    let x:=Real.sqrt U
    let g:=U^q
    have up : 0<U := mul_pos (c.energy_pos ht0) (c.length_pos ht0)
    have ep:=c.energy_pos ht0
    have dl:=c.dissipation_nonneg t
    have gn : 0<g:=Real.rpow_pos_of_pos up _
    obtain ⟨zs,vel⟩:=c.density_stress_control ht0
    change 1≤z at zs
    change c.energy t*c.lengthRate t*z≤c.dissipation t*c.length t*x at vel
    have rel : g*(x-z)≤K*z := by
      by_cases low : U≤M
      · have cap:=Real.rpow_le_rpow up.le low hq.le
        have xs:=Real.sqrt_le_sqrt low
        change x≤Real.sqrt M at xs
        have kg : M^q*Real.sqrt M≤K := by dsimp [K]; linarith
        calc
          g*(x-z) ≤ g*x := mul_le_mul_of_nonneg_left (by linarith) gn.le
          _ ≤ M^q*Real.sqrt M := mul_le_mul cap xs (Real.sqrt_nonneg _) (Real.rpow_nonneg Mp.le _)
          _ ≤ K := kg
          _ ≤ K*z := by nlinarith only [mul_nonneg kpos (sub_nonneg.mpr zs)]
      · have mu: M≤U := le_of_not_ge low
        have gu : 2*H≤g := big.trans (Real.rpow_le_rpow Mp.le mu hq.le)
        have hh : g*(x-z)≤H*x := high t ht (((le_max_right 1 U₀).trans (le_max_left _ _)).trans mu)
        have xz : x≤2*z := by
          by_contra! bad
          nlinarith only [mul_pos gn (sub_pos.mpr bad),hh,
            mul_nonneg (sub_nonneg.mpr gu) (Real.sqrt_nonneg U)]
        have hk : 2*H≤K := le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg Mp.le _) (Real.sqrt_nonneg M))
        exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left xz hH,
          mul_le_mul_of_nonneg_right hk (by linarith : 0≤z)])
    have rate : g*c.energy t*(c.energy t*c.lengthRate t-c.length t*c.dissipation t)
        ≤ K*U*c.dissipation t := by
      apply (mul_le_mul_iff_left₀ (show 0<z by linarith)).mp
      have h1:=mul_le_mul_of_nonneg_left vel (mul_nonneg gn.le ep.le)
      have h2:=mul_le_mul_of_nonneg_right rel (mul_nonneg up.le dl)
      dsimp only [U,normalizedProduct] at h2 ⊢
      nlinarith only [h1,h2]
    rw [Real.rpow_sub_one up.ne']
    change q*(g/U)*(c.energy t*c.lengthRate t-c.length t*c.dissipation t)
      +q*K*(-c.dissipation t/c.energy t)≤0
    field_simp [up.ne',ep.ne']
    nlinarith only [mul_le_mul_of_nonneg_left rate hq.le]

end LengthGrowth.ActualFlow.ForwardImmersion
