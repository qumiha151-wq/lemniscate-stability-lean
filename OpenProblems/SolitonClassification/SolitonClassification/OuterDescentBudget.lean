import SolitonClassification.CentreShotEntry
import SolitonClassification.OuterDescent

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress

/-- All needed pointwise estimates on a prescribed bounded region, with
    constants independent of the lower stress threshold. -/
theorem outer_budget (M : ℝ) :
    ∃ D ≥ 1, ∀ {δ t : ℝ} {r U w a b : ℝ → ℝ}, Rates δ t r U w a b →
      r t^2≤2 → |a t|≤M → |b t|≤M →
      |deriv (impact δ r U w a b) t| ≤ D*δ/r t^4 ∧
      |deriv (amplitude δ r U w a b) t+2*a t/3| ≤ D*δ/r t^3 ∧
      |amplitude δ r U w a b t-r t^2| ≤ D*δ/r t ∧
      |r t*b t-impact δ r U w a b t|≤D*δ/r t^2 := by
  obtain ⟨C,hC,bound⟩ := bounded_correctors (max M 2) (by positivity)
  let D := C+4
  have CD : C≤D := by dsimp [D]; linarith
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro δ t r U w a b d cap ha hb
  have osc := d.oscillator
  have hU : |U t|≤2 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg (w t),sq_nonneg ((U t)^2/2-1)]) (by norm_num)
  have hw : |w t|≤2 := le_of_sq_le_sq
    (by rw [sq_abs]; nlinarith [sq_nonneg ((U t)^2/2)]) (by norm_num)
  have poly := bound (r t^2) (U t) (w t) (a t) (b t)
    (by rw [abs_of_nonneg (sq_nonneg _)]; exact cap.trans (le_max_right ..))
    (hU.trans (le_max_right ..)) (hw.trans (le_max_right ..)) (ha.trans (le_max_left ..)) (hb.trans (le_max_left ..))
  have cancel (x v : ℝ) : -x+v+x=v := by ring
  have dd := d.delta_pos
  have rp := d.pos
  constructor
  · rw [(impact_rate d).deriv,abs_div,abs_mul,abs_of_pos dd,abs_of_pos (pow_pos rp _)]
    simpa only [mul_comm D δ] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (poly.1.trans CD) dd.le) (pow_nonneg rp.le 4)
  refine ⟨?_,?_,?_⟩
  · rw [(amplitude_rate d).deriv,cancel,abs_div,abs_mul,abs_of_pos dd,abs_of_pos (pow_pos rp _)]
    simpa only [mul_comm D δ] using div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (poly.2.1.trans CD) dd.le) (pow_nonneg rp.le 3)
  · unfold amplitude
    rw [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_pos dd,abs_div,abs_of_pos rp,
      ←mul_div_assoc,mul_comm D δ]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (poly.2.2.2.trans CD) dd.le) rp.le
  · unfold impact
    rw [sub_sub_cancel,abs_mul,abs_of_pos dd]
    have h := abs_sub_le (FrozenStress.psi (U t) (w t) (a t) (b t)/r t^2) 0 (U t)
    simp only [sub_zero,zero_sub,abs_neg,abs_div,abs_of_nonneg (sq_nonneg (r t))] at h
    apply (le_div_iff₀ (pow_pos rp _)).mpr
    have bnd := (mul_le_mul_of_nonneg_right h (sq_nonneg (r t)))
    rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero _ rp.ne')] at bnd
    have e := mul_le_mul hU cap (sq_nonneg (r t)) (by norm_num : (0:ℝ)≤2)
    dsimp [D]
    nlinarith only [mul_le_mul_of_nonneg_left (bnd.trans (add_le_add poly.2.2.1 e)) dd.le]

end ClosedSimilarity.OuterStress

namespace ClosedSimilarity.OuterStress

theorem critical_descent (M α E : ℝ) (pa : 0<α) (pE : 0≤E) :
    ∃ L≥1, ∃ C≥1, ∀ {δ S T : ℝ} {r U w a b : ℝ → ℝ}, S≤T →
      (∀x ∈ Icc S T, Rates δ x r U w a b ∧ r x^2≤2 ∧ |a x|≤M ∧ |b x|≤M ∧
        α≤a x ∧ L*δ≤r x^3) →
      |impact δ r U w a b S|≤E*δ →
      15*(r T)^2/16 + (α/3)*(T-S) ≤ 17*(r S)^2/16 ∧ |b T| * (r T)^3≤C*δ := by
  obtain ⟨D,hD,bd⟩ := outer_budget M
  have Dpos : 0<D := by linarith
  let L := max (16*D) (3*D/α)
  let C := 1+2*E+D+24*D/α
  have hL : 1≤L := (by linarith : 1≤16*D).trans (le_max_left ..)
  have hC : 1≤C := by dsimp [C]; linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤24) Dpos.le) pa.le]
  refine ⟨L,hL,C,hC,?_⟩
  intro δ S T r U w a b st data start
  let H := amplitude δ r U w a b
  let J := impact δ r U w a b
  have xS : S∈Icc S T := left_mem_Icc.mpr st
  have xT : T∈Icc S T := right_mem_Icc.mpr st
  have δp := (data S xS).1.delta_pos
  have est (x : ℝ) (hx : x∈Icc S T) : 15*r x^2/16≤H x ∧ H x≤17*r x^2/16 ∧
      deriv H x≤-α/3 ∧ |deriv J x|≤D*δ/r x^4 ∧ |r x*b x-J x|≤D*δ/r x^2 := by
    obtain ⟨rates,cap,al,ac,align,above⟩ := data x hx
    obtain ⟨j,h,mag,raw⟩ := bd rates cap al ac
    have p := rates.pos
    have A := (mul_le_mul_of_nonneg_right (le_max_left (16*D) (3*D/α)) δp.le).trans above
    have B := (mul_le_mul_of_nonneg_right (le_max_right (16*D) (3*D/α)) δp.le).trans above
    have by16 : D*δ/r x ≤ r x^2/16 := (div_le_iff₀ p).mpr (by linarith)
    have by3 : D*δ/r x^3 ≤ α/3 := (div_le_iff₀ (pow_pos p _)).mpr (by
      rw [div_mul_eq_mul_div] at B
      linarith [(div_le_iff₀ pa).mp B])
    change |H x-r x^2|≤_ at mag
    change |deriv H x+2*a x/3|≤_ at h
    exact ⟨by linarith [(abs_le.mp mag).1],by linarith [(abs_le.mp mag).2],
      by linarith [(abs_le.mp h).2],j,raw⟩
  let f := fun x => H x + (α/3)*x
  have df (x : ℝ) (hx : x∈Icc S T) : HasDerivAt f (deriv H x+α/3) x := by
    have d := (amplitude_rate (data x hx).1).differentiableAt
    convert! d.hasDerivAt.add ((hasDerivAt_id x).const_mul (α/3)) using 1
    ring
  have dec : AntitoneOn f (Icc S T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (fun x hx => (df x hx).continuousAt.continuousWithinAt)
      (fun x hx => (df x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(df x (interior_subset hx)).deriv]
    linarith [(est x (interior_subset hx)).2.2.1]
  have order := dec xS xT st
  change H T+(α/3)*T ≤ H S+(α/3)*S at order
  refine ⟨by linarith [(est T xT).1,(est S xS).2.1],?_⟩
  have hp (x : ℝ) (hx : x∈Icc S T) : 0<H x := by
    have p := (data x hx).1.pos
    linarith [(est x hx).1,sq_pos_of_pos p]
  have drift := descending_impact (A := fun x => r x^2) (hB := mul_nonneg Dpos.le δp.le) st
    (show 0<α/3 by positivity)
    (fun x hx => (amplitude_rate (data x hx).1).continuousAt.continuousWithinAt)
    (fun x hx => (impact_rate (data x hx).1).continuousAt.continuousWithinAt) hp
    (fun x hx => by
      have inside : x∈Icc S T := ⟨hx.1.le,hx.2.le⟩
      have e := est x inside
      refine ⟨(amplitude_rate (data x inside).1).differentiableAt,
        (impact_rate (data x inside).1).differentiableAt,by simpa only [neg_div] using e.2.2.1,?_,?_⟩
      · convert e.2.2.2.1 using 1; ring
      · linarith [e.2.1,sq_nonneg (r x)])
  have rt := (data T xT).1.pos
  have hratio : (α/3)*(r T^2/2) ≤ (α/3)*H T := mul_le_mul_of_nonneg_left
    (by linarith [(est T xT).1,sq_nonneg (r T)]) (by positivity)
  have dr : |J T-J S| ≤ (24*D/α)*δ/r T^2 := by
    apply drift.trans
    calc
      _ ≤ (4*(D*δ))/((α/3)*(r T^2/2)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hratio
      _ = _ := by ring
  have absJ := abs_sub_le (J T) (J S) 0
  have raw := abs_sub_le (r T*b T) (J T) 0
  simp only [sub_zero] at absJ raw
  rw [abs_mul,abs_of_pos rt] at raw
  have e := (est T xT).2.2.2.2
  have bound := raw.trans (add_le_add e (absJ.trans (add_le_add dr start)))
  have mul := mul_le_mul_of_nonneg_right bound (sq_nonneg (r T))
  have pT := pow_ne_zero 2 rt.ne'
  rw [add_mul,add_mul,div_mul_cancel₀ _ pT,div_mul_cancel₀ _ pT] at mul
  dsimp [C]
  nlinarith only [mul,mul_le_mul_of_nonneg_left (data T xT).2.1 (mul_nonneg pE δp.le),δp]

end ClosedSimilarity.OuterStress
#print axioms ClosedSimilarity.OuterStress.critical_descent
