import Lemniscate.PeriodicParabolicGlobalSolution
import Mathlib.Topology.Order.Compact

/-! A small-data exponential estimate for every global small solution
applies after a discrete segment shift to any such solution tending to zero.
Continuity on a positive compact time interval supplies the remaining bound. -/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology NNReal

private theorem square_decay_norm (r A μ t X : ℝ)
    (hr : 0≤r) (hA : 0≤A) (hX : 0≤X)
    (h : r^2≤A*Real.exp (-2*μ*t)*X^2) :
    r≤Real.sqrt A*X*Real.exp (-μ*t) := by
  have he : Real.exp (-2*μ*t)=Real.exp (-μ*t)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hs : r^2≤(Real.sqrt A*X*Real.exp (-μ*t))^2 := h.trans_eq (by
    rw [mul_pow,mul_pow,Real.sq_sqrt hA,he]
    ring)
  exact (sq_le_sq₀ hr (by positivity)).mp hs

/-- One common small-solution neighborhood gives a fixed exponential
rate in every requested higher space, with constants allowed to depend
on the given solution.  The equation is used only through its already
proved estimate and its actual overlapping-segment representation. -/
theorem circle_parabolic_shift_decay
    {H E Z X : Type*} [NormedAddCommGroup H] [NormedAddCommGroup E]
    (τ : ℝ) (hτ : 0<τ) (μ : ℝ) (hμ : 0<μ)
    (curve : X → unitInterval → H) (Small : X → Prop) (Phase : H → Prop)
    (i : H → Z) (j : E → Z) (t₀ : ℝ) (ht₀ : 0<t₀)
    (hquant : ∃ ε>0,∃ A>0,
      ∀ (u : C(ℝ≥0,H)) (U : ℕ → X),
      (∀ m r,u (circleParabolicSegmentTime τ hτ m r)=curve (U m) r) →
      (∀ m,Small (U m)) → Phase (u 0) → ‖u 0‖≤ε →
      ∀ v : C(Ioi (0:ℝ),E),
      (∀ t : Ioi (0:ℝ),j (v t)=i (u ⟨(t:ℝ),t.property.le⟩)) →
      ∀ t : Ioi (0:ℝ),t₀≤(t:ℝ) →
        ‖v t‖^2≤A*Real.exp (-2*μ*(t:ℝ))*‖u 0‖^2)
    (u : C(ℝ≥0,H)) (U : ℕ → X)
    (hrep : ∀ m r,u (circleParabolicSegmentTime τ hτ m r)=curve (U m) r)
    (hsmall : ∀ m,Small (U m)) (hphase : ∀ t,Phase (u t))
    (hu : Tendsto u atTop (𝓝 0))
    (v : C(Ioi (0:ℝ),E))
    (hv : ∀ t : Ioi (0:ℝ),j (v t)=i (u ⟨(t:ℝ),t.property.le⟩)) :
    ∃ C>0,∀ t : Ioi (0:ℝ),t₀≤(t:ℝ) → ‖v t‖≤C*Real.exp (-μ*(t:ℝ)) := by
  obtain ⟨ε,hε,A,hA,hquant⟩ := hquant
  have hzero : ‖(0:H)‖<ε := by simpa only [norm_zero] using hε
  have hevent : ∀ᶠ t : ℝ≥0 in atTop,‖u t‖≤ε :=
    (hu.norm.eventually (gt_mem_nhds hzero)).mono (fun _ h => h.le)
  obtain ⟨b,hb⟩ := eventually_atTop.mp hevent
  obtain ⟨N,hN⟩ := exists_nat_ge (2*(b:ℝ)/τ)
  let start : ℝ≥0 := ⟨τ*(N:ℝ)/2,by positivity⟩
  have hbstart : b≤start := by
    change (b:ℝ)≤τ*(N:ℝ)/2
    have hh := (div_le_iff₀ hτ).mp hN
    nlinarith only [hh]
  let uN : C(ℝ≥0,H) := u.comp ⟨fun t => t+start,continuous_id.add_const start⟩
  let UN : ℕ → X := fun m => U (N+m)
  let vN : C(Ioi (0:ℝ),E) := v.comp
    ⟨fun t => ⟨(t:ℝ)+(start:ℝ),add_pos_of_pos_of_nonneg t.property start.property⟩,
      Continuous.subtype_mk (continuous_subtype_val.add_const (start:ℝ)) _⟩
  have htadd (m : ℕ) (r : unitInterval) :
      circleParabolicSegmentTime τ hτ (N+m) r=
        circleParabolicSegmentTime τ hτ m r+start := by
    apply Subtype.ext
    change τ*(((N+m:ℕ):ℝ)/2+(r:ℝ))=τ*((m:ℝ)/2+(r:ℝ))+τ*(N:ℝ)/2
    push_cast
    ring
  have hrepN (m : ℕ) (r : unitInterval) :
      uN (circleParabolicSegmentTime τ hτ m r)=curve (UN m) r := by
    change u (circleParabolicSegmentTime τ hτ m r+start)=curve (U (N+m)) r
    rw [← htadd]
    exact hrep (N+m) r
  have hvN (t : Ioi (0:ℝ)) : j (vN t)=i (uN ⟨(t:ℝ),t.property.le⟩) :=
    hv ⟨(t:ℝ)+(start:ℝ),add_pos_of_pos_of_nonneg t.property start.property⟩
  have huN0 : uN 0=u start := by
    change u (0+start)=u start
    rw [zero_add]
  have hdecay := hquant uN UN hrepN (fun m => hsmall (N+m))
    (by rw [huN0];exact hphase start)
    (by rw [huN0];exact hb start hbstart) vN hvN
  let B := Real.sqrt A*‖u start‖*Real.exp (μ*(start:ℝ))
  have hB : 0≤B := by dsimp only [B];positivity
  have hlate (t : Ioi (0:ℝ)) (ht : t₀+(start:ℝ)≤(t:ℝ)) :
      ‖v t‖≤B*Real.exp (-μ*(t:ℝ)) := by
    let r : Ioi (0:ℝ) := ⟨(t:ℝ)-(start:ℝ),by change 0<(t:ℝ)-(start:ℝ);linarith only [ht,ht₀]⟩
    have hr : t₀≤(r:ℝ) := by dsimp only [r];linarith only [ht]
    have hd := square_decay_norm _ A μ (r:ℝ) ‖uN 0‖ (norm_nonneg _) hA.le
      (norm_nonneg _) (hdecay r hr)
    have hvr : vN r=v t := by
      change v ⟨(r:ℝ)+(start:ℝ),_⟩=v t
      apply congrArg v
      apply Subtype.ext
      dsimp only [r]
      ring
    rw [hvr,huN0] at hd
    change ‖v t‖≤Real.sqrt A*‖u start‖*Real.exp (-μ*((t:ℝ)-(start:ℝ))) at hd
    have hexp : Real.exp (-μ*((t:ℝ)-(start:ℝ)))=
        Real.exp (μ*(start:ℝ))*Real.exp (-μ*(t:ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    exact hd.trans_eq (by rw [hexp];dsimp only [B];ring)
  let topTime := t₀+(start:ℝ)
  let clamp : ℝ → Ioi (0:ℝ) := fun s => ⟨max t₀ s,ht₀.trans_le (le_max_left _ _)⟩
  have hclamp : Continuous clamp := Continuous.subtype_mk (continuous_const.max continuous_id) _
  obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (v.continuous.comp hclamp).continuousOn
  let L := max K 0+1
  have hL : 0<L := by dsimp only [L];positivity
  let C := L*Real.exp (μ*topTime)+B+1
  have hC : 0<C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro t ht
  by_cases htop : topTime≤(t:ℝ)
  · exact (hlate t htop).trans (mul_le_mul_of_nonneg_right
      (by dsimp only [C];linarith only [mul_nonneg hL.le (Real.exp_pos (μ*topTime)).le])
      (Real.exp_pos _).le)
  · have htTop : (t:ℝ)≤topTime := le_of_not_ge htop
    have hn : ‖v t‖≤L := by
      have hh := hK (t:ℝ) (show (t:ℝ)∈Icc t₀ topTime from ⟨ht,htTop⟩)
      have hc : clamp (t:ℝ)=t := by
        apply Subtype.ext
        exact max_eq_right ht
      change ‖v (clamp (t:ℝ))‖≤K at hh
      rw [hc] at hh
      exact hh.trans (by dsimp only [L];linarith only [le_max_left K 0])
    have hexp : 1≤Real.exp (μ*topTime)*Real.exp (-μ*(t:ℝ)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith only [hμ,htTop])
    calc
      _≤L := hn
      _≤L*(Real.exp (μ*topTime)*Real.exp (-μ*(t:ℝ))) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hL.le
      _≤C*Real.exp (-μ*(t:ℝ)) := by
        rw [← mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp only [C]
        linarith only [hB]

end Lemniscate
