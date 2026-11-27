import SolitonClassification.CentreDirectionDescent

noncomputable section
open Set
namespace ClosedSimilarity.OuterStress.Data
variable {δ : ℝ}

def CriticalStrip (z : Data δ) (L C T : ℝ) : Prop :=
  ∀ s ∈ Icc (1/2:ℝ) T, 1/1200 < z.along s ∧ z.amplitude s<2 ∧
    L*δ≤z.root s^3 ∧ |z.across s| * z.root s^3≤C*δ

theorem initial_root_lower (z : Data δ) (hd : 0<δ)
    (hk : z.K 0=0) (hv : z.V 0=1) (hp : z.p 0=0) (hq : z.q 0=0)
    {s : ℝ} (hs : s∈Icc (0:ℝ) (1/2)) : 1/2≤z.root s := by
  have low := (z.centre_bounds hd hk hv hp hq hs.1).2
  have cap := pow_le_pow_left₀ hs.1 hs.2 2
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (show 0≤z.amplitude s from Real.sqrt_nonneg _)]
  nlinarith

theorem support_component_bounds (z : Data δ) (hd : 0<δ)
    (hk : z.K 0=0) (hv : z.V 0=1) (hp : z.p 0=0) (hq : z.q 0=0)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 10000) (ap : 0<z.amplitude s) :
    |z.along s|≤10000 ∧ |z.across s|≤10000 := by
  have cap := pow_le_pow_left₀ hs.1 hs.2 2
  have pq := (z.centre_bounds hd hk hv hp hq hs.1).1
  have fr := z.radius_sq s ap
  constructor
  · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.across s)]
  · apply le_of_sq_le_sq _ (by norm_num); rw [sq_abs]; nlinarith [sq_nonneg (z.along s)]

/-- On every prefix of a certified critical flight there is a terminal piece of
length at most 3825 η², preceded entirely by stress radii at least η. -/
theorem split_critical_window :
    ∃ L₀≥1, ∀ {δ L C T η : ℝ} (z : Data δ), 0<δ → L₀≤L →
      z.K 0=0 → z.V 0=1 → z.p 0=0 → z.q 0=0 →
      T∈Icc (1/2:ℝ) 10000 → CriticalStrip z L C T →
      0<η → η≤1/2 →
      ∃ S∈Icc (1/2:ℝ) T, (∀ s∈Icc 0 S, η≤z.root s) ∧ T-S≤3825*η^2 := by
  obtain ⟨L₀,hL₀,drop⟩ := segment_amplitude_drop 10000 (1/1200) (by norm_num)
  refine ⟨L₀,hL₀,?_⟩
  intro δ L C T η z hd hl hk hv hp hq ht strip hη capη
  have init (s : ℝ) (hs : s∈Icc (0:ℝ) (1/2)) := capη.trans (z.initial_root_lower hd hk hv hp hq hs)
  have ini : η≤z.root (1/2) := init _ (by norm_num)
  have cr : Continuous z.root := by
    have K := continuous_iff_continuousAt.mpr (fun x => (z.dK x).continuousAt)
    have V := continuous_iff_continuousAt.mpr (fun x => (z.dV x).continuousAt)
    exact (((((K.pow 2).div_const 2).pow 2).add (V.pow 2)).sqrt).sqrt
  by_cases all : ∀s∈Icc (1/2:ℝ) T, η≤z.root s
  · refine ⟨T,⟨ht.1,le_rfl⟩,?_,by simpa using (show 0≤3825*η^2 by positivity)⟩
    intro s hs
    by_cases e : s≤1/2
    · exact init s ⟨hs.1,e⟩
    · exact all s ⟨le_of_not_ge e,hs.2⟩
  push Not at all
  obtain ⟨t,ht',low⟩ := all
  let hits := {x∈Icc (1/2:ℝ) T | z.root x=η}
  have comp : IsCompact hits := isCompact_Icc.inter_right (isClosed_eq cr continuous_const)
  obtain ⟨y,hy,eq⟩ := intermediate_value_Icc' ht'.1 cr.continuousOn
    (show η∈Icc (z.root t) (z.root (1/2)) from ⟨low.le,ini⟩)
  obtain ⟨S,hS,first⟩ := comp.exists_isMinOn
    (show hits.Nonempty from ⟨y,⟨⟨hy.1,hy.2.trans ht'.2⟩,eq⟩⟩) continuous_id.continuousOn
  refine ⟨S,hS.1,?_,?_⟩
  · intro s hs
    by_cases e : s≤1/2
    · exact init s ⟨hs.1,e⟩
    by_contra! small
    obtain ⟨y,hy,eq⟩ := intermediate_value_Icc' (le_of_not_ge e) cr.continuousOn
      (show η∈Icc (z.root s) (z.root (1/2)) from ⟨small.le,ini⟩)
    have before : S≤y := first (show y∈hits from ⟨⟨hy.1,(hy.2.trans hs.2).trans hS.1.2⟩,eq⟩)
    have same : y=s := le_antisymm hy.2 (hs.2.trans before)
    exact small.ne (same ▸ eq)
  · have est := @drop δ S T z.root z.shape z.slope z.along z.across hS.1.2 (fun x hx => by
      have xi : x∈Icc (1/2:ℝ) T := ⟨hS.1.1.trans hx.1,hx.2⟩
      obtain ⟨ha,cap,above,_⟩ := strip x xi
      have lp : 0<L := by linarith
      have rpos : 0<z.root x := by
        by_contra! nr
        have zr : z.root x=0 := le_antisymm nr (Real.sqrt_nonneg _)
        rw [zr] at above
        nlinarith only [above,mul_pos lp hd]
      have ap := Real.sqrt_pos.mp rpos
      have ab := z.support_component_bounds hd hk hv hp hq ⟨by linarith [xi.1],xi.2.trans ht.2⟩ ap
      exact ⟨z.normalized_rates x ap hd,(Real.sq_sqrt ap.le).trans_le cap.le,
        ab.1,ab.2,ha.le,(mul_le_mul_of_nonneg_right hl hd.le).trans above⟩)
    rw [hS.2] at est
    linarith [sq_nonneg (z.root T)]

end ClosedSimilarity.OuterStress.Data
#print axioms ClosedSimilarity.OuterStress.Data.split_critical_window


