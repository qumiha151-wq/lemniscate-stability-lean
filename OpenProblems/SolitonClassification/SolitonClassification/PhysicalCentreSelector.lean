import SolitonClassification.PhysicalIncomingCrossing
import SolitonClassification.CentreIncomingTransverse
import SolitonClassification.FirstTransverseCrossing

noncomputable section
set_option maxHeartbeats 240000
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam

private theorem joint_centre_continuity {B : ℝ} (slope : ∀ b : Ici B, 0<(b:ℝ)) :
    Continuous (fun y : Ici B×ℝ => centreAt y.1 y.2) := by
  have cb : Continuous (fun y : (Ici B)×ℝ => (y.1:ℝ)) := continuous_subtype_val.comp continuous_fst
  have time : Continuous (fun y : (Ici B)×ℝ => y.2/Real.sqrt (y.1:ℝ)⁻¹) :=
      continuous_snd.div ((cb.inv₀ (fun y => (slope y.1).ne')).sqrt)
        (fun y => (Real.sqrt_pos.mpr (inv_pos.mpr (slope y.1))).ne')
  have init : Continuous (fun y : (Ici B)×ℝ => (![0,(y.1:ℝ),0,0] : Phase)) := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
  exact continuous_solution.comp (time.prodMk (continuous_const.prodMk init))

private theorem joint_negative_height {B : ℝ} (slope : ∀ b : Ici B, 0<(b:ℝ))
    (b : Ici B) (s : ℝ) (reg : regular (centreAt b s)) :
    ContinuousAt (fun y : Ici B×ℝ => -height (centreAt y.1 y.2)) (b,s) := by
  let shot : Ici B×ℝ → Phase := fun y => centreAt y.1 y.2
  have hc : ContinuousAt shot (b,s) := (joint_centre_continuity slope).continuousAt
  have hh : ContinuousAt height (shot (b,s)) := (height_smooth reg).continuousAt
  exact (hh.comp hc).neg

private theorem endpoints_strict {S T H : ℝ} (g : ℝ→ℝ) (le : S≤T)
    (lo : H<g S) (hi : g T<H) : S<T := by
  apply lt_of_le_of_ne le
  intro eq
  subst T
  exact lo.not_gt hi

private theorem centre_slow_deriv {B : ℝ} (b : Ici B) (s : ℝ) (bp : 0<(b:ℝ))
    (reg : regular (centreAt b s)) (rate : scale (centreAt b s)/8 < heightRate (1,centreAt b s)) :
    ∃d<0, HasDerivAt (fun t => -height (centreAt b t)) d s := by
  have sc : 0<scale (centreAt b s) := Real.rpow_pos_of_pos reg.1 _
  exact centre_has_slow_rate (b:=(b:ℝ)) (u:=s) bp reg ((div_pos sc (by norm_num)).trans rate)

/-- Continuous first hitting time for the *physical centre shots*.
    The same constant K bounds the transverse impact for all sufficiently high
    levels. Thresholds in the marker can be made arbitrarily large. -/
theorem physical_centre_selector :
    ∃ K>0, ∃ H₀≥17, ∀ H≥H₀, ∀ Bmin : ℝ, ∃ B≥max 32 Bmin,
      ∃ T τ : Ici B → ℝ, Continuous τ ∧ ∀ b : Ici B,
        T b≤10000 ∧ τ b∈Ioo 1 (T b) ∧ -height (centreAt b (τ b))=H ∧
        4 ≤ innerRoot (centreAt b (τ b)) ∧ |impact (centreAt b (τ b))|≤K/H ∧
        (∀s∈Icc 1 (T b), regular (centreAt b s) ∧ 1 ≤ innerRoot (centreAt b s) ∧
          1/12000000≤along (centreAt b s) ∧ (1/scale (centreAt b s)^4)^3 ≤ 1200^4*((b:ℝ)⁻¹)^2) ∧
        (∀s∈Icc 1 (T b), -height (centreAt b s)=H → s=τ b) ∧
        (∀s∈Ico 1 (τ b), H < -height (centreAt b s)) := by
  obtain ⟨K,kp,H₁,_,cross⟩ := physical_centre_incoming_crossing
  refine ⟨K,kp,max 17 H₁,le_max_left ..,?_⟩
  intro H high Bmin
  obtain ⟨B₁,_,chooseTime⟩ := cross H ((le_max_right ..).trans high)
  obtain ⟨B₂,_,rate⟩ := large_marker_rate_at_level H (1/12000000) ((le_max_left ..).trans high) (by norm_num)
  let B := max (max 32 Bmin) (max B₁ B₂)
  have ge : max 32 Bmin≤B := le_max_left ..
  have slope (b : Ici B) : 0<(b:ℝ) := lt_of_lt_of_le (by norm_num : (0:ℝ)<32)
    (((le_max_left ..).trans ge).trans b.property)
  have h1 (b : Ici B) : B₁≤(b:ℝ) := ((le_max_left B₁ B₂).trans (le_max_right ..)).trans b.property
  have h2 (b : Ici B) : B₂≤(b:ℝ) := ((le_max_right B₁ B₂).trans (le_max_right ..)).trans b.property
  let T (b : Ici B) := (chooseTime b (h1 b)).choose
  have hT (b : Ici B) : T b ∈ Icc (1:ℝ) 10000 := (chooseTime b (h1 b)).choose_spec.1
  have sides (b : Ici B) : H < -height (centreAt b 1) ∧ -height (centreAt b (T b)) < H :=
    (chooseTime b (h1 b)).choose_spec.2.1
  have strip (b : Ici B) (s : ℝ) (hs : s∈Icc 1 (T b)) :=
    (chooseTime b (h1 b)).choose_spec.2.2.2 s hs
  let F := fun y : Ici B×ℝ => -height (centreAt y.1 y.2)
  have trans (b : Ici B) (s : ℝ) (hs : s∈Icc 1 (T b)) (hit : F (b,s)=H) :=
    let r := strip b s hs
    rate b (h2 b) (centreAt b s) r.1 r.2.1 r.2.2.1 hit r.2.2.2.1
  have bounds (b : Ici B) : 1<T b ∧ H<F (b,1) ∧ F (b,T b)<H :=
    ⟨endpoints_strict (fun s => F (b,s)) (hT b).1 (sides b).1 (sides b).2,sides b⟩
  have ct (b : Ici B) (s : ℝ) (hs : s∈Icc 1 (T b)) : ContinuousAt F (b,s) :=
    joint_negative_height slope b s (strip b s hs).1
  have speed (b : Ici B) (s : ℝ) (hs : s∈Icc 1 (T b)) (hit : F (b,s)=H) :
      ∃d<0, HasDerivAt (fun t => F (b,t)) d s :=
    centre_slow_deriv b s (slope b) (strip b s hs).1 (trans b s hs hit).2
  obtain ⟨τ,cont,selected⟩ := continuous_first_crossing F 1 H T bounds ct speed
  refine ⟨B,ge,T,τ,cont,?_⟩
  intro b
  obtain ⟨ht,hit,unique,before⟩ := selected b
  have inside := Ioo_subset_Icc_self ht
  exact ⟨(hT b).2,ht,hit,(trans b _ inside hit).1,(strip b _ inside).2.2.2.2 hit,
    fun s hs => ⟨(strip b s hs).1,(strip b s hs).2.1,(strip b s hs).2.2.1,(strip b s hs).2.2.2.1⟩,
    unique,before⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.physical_centre_selector
