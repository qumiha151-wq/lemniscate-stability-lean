import Lemniscate.PeriodicParabolicRestriction
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Global continuation by overlapping actual local solutions.

Segments have physical duration tau and restart after tau/2.  Their
half restrictions agree by uniqueness.  Only their continuous H2 curves
are assembled; no unproved concatenation in the parabolic space is used.

-/

noncomputable section
namespace Lemniscate
open MeasureTheory Filter Set Function
open scoped ENNReal NNReal Topology

private def globalHalf : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
private def globalLeft (r : unitInterval) : unitInterval :=
  ⟨(r:ℝ)/2,by constructor <;> linarith [r.property.1,r.property.2]⟩
private def globalRight (r : unitInterval) : unitInterval :=
  ⟨(1+(r:ℝ))/2,by constructor <;> linarith [r.property.1,r.property.2]⟩
private def globalChartTime (n : ℕ) (r : unitInterval) : ℝ≥0 :=
  ⟨(n:ℝ)/2+(r:ℝ),add_nonneg (by positivity) r.property.1⟩
private def globalStrip (n : ℕ) : Set ℝ≥0 :=
  {x | (n:ℝ)/2 ≤ (x:ℝ) ∧ (x:ℝ) ≤ (n:ℝ)/2+1}
private def globalStripCoordinate (n : ℕ) (x : globalStrip n) : unitInterval :=
  ⟨((x:ℝ≥0):ℝ)-(n:ℝ)/2,by
    constructor <;> linarith [x.property.1,x.property.2]⟩

private theorem global_strips_nhds (x : ℝ≥0) :
    ∃ n : ℕ, globalStrip n ∈ 𝓝 x ∧
      (0 < x → (n:ℝ)/2 < (x:ℝ) ∧ (x:ℝ) < (n:ℝ)/2+1) := by
  let N := Nat.ceil (2*(x:ℝ))
  by_cases hN : N = 0
  · have hx : (x:ℝ) = 0 := by
      have hh := Nat.le_ceil (2*(x:ℝ))
      change 2*(x:ℝ) ≤ (N:ℝ) at hh
      rw [hN,Nat.cast_zero] at hh
      exact le_antisymm (by linarith only [hh]) (NNReal.coe_nonneg x)
    refine ⟨0,?_,?_⟩
    · have ho : IsOpen {y : ℝ≥0 | (y:ℝ) < 1} := isOpen_lt continuous_subtype_val continuous_const
      have hm : {y : ℝ≥0 | (y:ℝ) < 1} ∈ 𝓝 x := ho.mem_nhds (by
        change (x:ℝ) < 1
        rw [hx]
        norm_num)
      exact mem_of_superset hm (fun y hy => ⟨by simpa [globalStrip] using y.property,by simpa [globalStrip] using hy.le⟩)
    · intro hp
      have hh : (0:ℝ) < x := hp
      linarith only [hh,hx]
  · let n := N-1
    have hnN : n < N := by dsimp only [n]; omega
    have hcast : (n:ℝ)+1 = (N:ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN))
    have hlo : (n:ℝ) < 2*(x:ℝ) := (Nat.lt_ceil).mp hnN
    have hup : 2*(x:ℝ) ≤ (N:ℝ) := Nat.le_ceil _
    have hl : (n:ℝ)/2 < (x:ℝ) := by linarith only [hlo]
    have hu : (x:ℝ) < (n:ℝ)/2+1 := by linarith only [hup,hcast]
    refine ⟨n,?_,fun _ => ⟨hl,hu⟩⟩
    have ho : IsOpen {y : ℝ≥0 | (n:ℝ)/2 < (y:ℝ) ∧ (y:ℝ) < (n:ℝ)/2+1} :=
      (isOpen_lt continuous_const continuous_subtype_val).inter
        (isOpen_lt continuous_subtype_val continuous_const)
    exact mem_of_superset (ho.mem_nhds ⟨hl,hu⟩) (fun _ hy => ⟨hy.1.le,hy.2.le⟩)

private theorem global_chart_agreement
    {H : Type*} [TopologicalSpace H] (c : ℕ → C(unitInterval,H))
    (hoverlap : ∀ n r, c n (globalRight r) = c (n+1) (globalLeft r))
    (n m : ℕ) (r q : unitInterval)
    (ht : (n:ℝ)/2+(r:ℝ) = (m:ℝ)/2+(q:ℝ)) : c n r = c m q := by
  wlog hnm : n ≤ m generalizing n m r q
  · exact (this m n q r ht.symm (Nat.le_of_lt (Nat.lt_of_not_ge hnm))).symm
  have hm2 : m ≤ n+2 := by
    have hh : (m:ℝ) ≤ (n:ℝ)+2 := by linarith [r.property.2,q.property.1]
    exact_mod_cast hh
  rcases eq_or_lt_of_le hnm with hsame | hlt
  · subst m
    exact congrArg (c n) (Subtype.ext (by linarith only [ht]))
  · have hcases : m = n+1 ∨ m = n+2 := by omega
    rcases hcases with hm | hm
    · subst m
      simp only [Nat.cast_add,Nat.cast_one] at ht
      have hq : (q:ℝ) ≤ 1/2 := by linarith [r.property.2]
      let z : unitInterval := ⟨2*(q:ℝ),by constructor <;> linarith [q.property.1]⟩
      have hr : r = globalRight z := Subtype.ext (by dsimp only [globalRight,z]; linarith only [ht])
      have hq' : q = globalLeft z := Subtype.ext (by dsimp only [globalLeft,z]; ring)
      exact (congrArg (c n) hr).trans ((hoverlap n z).trans (congrArg (c (n+1)) hq'.symm))
    · subst m
      simp only [Nat.cast_add,Nat.cast_ofNat] at ht
      have hr : r = 1 := Subtype.ext (by change (r:ℝ) = 1; linarith [r.property.2,q.property.1])
      have hq : q = 0 := Subtype.ext (by change (q:ℝ) = 0; linarith [r.property.2,q.property.1])
      have hR : globalRight 1 = 1 := Subtype.ext (by norm_num [globalRight])
      have hL : globalLeft 0 = 0 := Subtype.ext (by norm_num [globalLeft])
      have hmid : globalLeft 1 = globalRight 0 := Subtype.ext (by norm_num [globalLeft,globalRight])
      have h1 := hoverlap n 1
      have h2 := hoverlap (n+1) 0
      rw [hR,hmid] at h1
      rw [hL] at h2
      rw [hr,hq]
      simpa only [Nat.add_assoc,one_add_one_eq_two] using h1.trans h2

private theorem global_continuous_charts
    {H : Type*} [TopologicalSpace H] (c : ℕ → C(unitInterval,H))
    (hoverlap : ∀ n r, c n (globalRight r) = c (n+1) (globalLeft r)) :
    ∃ u : C(ℝ≥0,H),
      (∀ n r, u (globalChartTime n r) = c n r) ∧
      ∀ t : ℝ≥0, ∃ n r, globalChartTime n r = t ∧
        (0 < t → (0:ℝ) < (r:ℝ) ∧ (r:ℝ) < 1) := by
  let φ : ∀ n : ℕ, C(globalStrip n,H) := fun n =>
    ⟨fun x => c n (globalStripCoordinate n x),by
      have hcoe : Continuous (fun x : globalStrip n => ((x:ℝ≥0):ℝ)) :=
        (continuous_subtype_val : Continuous (fun x : ℝ≥0 => (x:ℝ))).comp
          (continuous_subtype_val : Continuous (fun x : globalStrip n => (x:ℝ≥0)))
      exact (c n).continuous.comp ((hcoe.sub continuous_const).subtype_mk _)⟩
  have hφ : ∀ n m (x : ℝ≥0) (hn : x ∈ globalStrip n) (hm : x ∈ globalStrip m),
      φ n ⟨x,hn⟩ = φ m ⟨x,hm⟩ := by
    intro n m x hn hm
    exact global_chart_agreement c hoverlap n m _ _ (by dsimp only [globalStripCoordinate]; ring)
  have hcover : ∀ x : ℝ≥0, ∃ n, globalStrip n ∈ 𝓝 x :=
    fun x => (global_strips_nhds x).imp (fun _ hn => hn.1)
  let u : C(ℝ≥0,H) := ContinuousMap.liftCover globalStrip φ hφ hcover
  refine ⟨u,?_,?_⟩
  · intro n r
    have hx : globalChartTime n r ∈ globalStrip n := by
      change (n:ℝ)/2 ≤ (n:ℝ)/2+(r:ℝ) ∧ (n:ℝ)/2+(r:ℝ) ≤ (n:ℝ)/2+1
      constructor <;> linarith [r.property.1,r.property.2]
    have hh := ContinuousMap.liftCover_coe (S := globalStrip) (φ := φ) (hφ := hφ)
      (hS := hcover) (⟨globalChartTime n r,hx⟩ : globalStrip n)
    have hr : globalStripCoordinate n ⟨globalChartTime n r,hx⟩ = r := by
      apply Subtype.ext
      change ((n:ℝ)/2+(r:ℝ))-(n:ℝ)/2 = (r:ℝ)
      ring
    exact hh.trans (congrArg (c n) hr)
  · intro t
    obtain ⟨n,hn,hstrict⟩ := global_strips_nhds t
    let r := globalStripCoordinate n ⟨t,mem_of_mem_nhds hn⟩
    refine ⟨n,r,?_,?_⟩
    · apply Subtype.ext
      change (n:ℝ)/2+((t:ℝ)-(n:ℝ)/2) = (t:ℝ)
      ring
    · intro ht
      have hs := hstrict ht
      change 0 < (t:ℝ)-(n:ℝ)/2 ∧ (t:ℝ)-(n:ℝ)/2 < 1
      constructor <;> linarith only [hs.1,hs.2]

private theorem small_initial_energy
    {H : Type*} [NormedAddCommGroup H]
    (E : H → ℝ) (CE ε : ℝ) (hCE : 0 ≤ CE) (hε : 0 < ε)
    (hupp : ∀ x, E x ≤ CE*‖x‖^2) :
    ∃ η > 0, ∀ x : H, ‖x‖ ≤ η → 2*E x ≤ ε^2 := by
  let η := min ε (ε/(2*(CE+1)))
  have hη : 0 < η := lt_min hε (div_pos hε (by positivity))
  refine ⟨η,hη,?_⟩
  intro x hx
  have hxε : ‖x‖ ≤ ε := hx.trans (min_le_left _ _)
  have hxdiv := hx.trans (min_le_right ε (ε/(2*(CE+1))))
  have hh := (le_div_iff₀ (by positivity : 0 < 2*(CE+1))).mp hxdiv
  have hs : 2*CE*‖x‖ ≤ ε := by nlinarith only [hh,norm_nonneg x]
  have hp := mul_le_mul_of_nonneg_right hs (norm_nonneg x)
  have hq := mul_le_mul_of_nonneg_left hxε hε.le
  nlinarith only [hp,hq,hupp x]

private theorem energy_iteration
    {H Y : Type*} [NormedAddCommGroup H]
    (initial : Y → H) (curve : Y → C(unitInterval,H)) (Good : Y → Prop)
    (phase : H → ℂ) (E : H → ℝ) (τ a ε : ℝ)
    (hτ : 0 < τ) (ha : 0 < a) (hε : 0 < ε)
    (hlow : ∀ x, ‖x‖^2 ≤ 2*E x)
    (hsolve : ∀ x, phase x = 0 → ‖x‖ ≤ ε → ∃ y, Good y ∧ initial y = x)
    (hdecay : ∀ y, Good y → phase (initial y) = 0 → ∀ r : unitInterval,
      phase (curve y r) = 0 ∧ E (curve y r) ≤ Real.exp (-a*τ*(r:ℝ))*E (initial y))
    (x₀ : H) (hphase : phase x₀ = 0) (henergy : 2*E x₀ ≤ ε^2) :
    ∃ y : ℕ → Y, (∀ n, Good (y n)) ∧ initial (y 0) = x₀ ∧
      (∀ n, initial (y (n+1)) = curve (y n) globalHalf) ∧
      ∀ n r, phase (curve (y n) r) = 0 ∧
        E (curve (y n) r) ≤ Real.exp (-a*τ*((n:ℝ)/2+(r:ℝ)))*E x₀ := by
  let X := {x : H | phase x = 0 ∧ 2*E x ≤ ε^2}
  have hnorm (x : X) : ‖x.1‖ ≤ ε :=
    (sq_le_sq₀ (norm_nonneg _) hε.le).mp ((hlow x.1).trans x.2.2)
  have hex (x : X) : ∃ y, Good y ∧ initial y = x.1 := hsolve x.1 x.2.1 (hnorm x)
  let solve : X → Y := fun x => (hex x).choose
  have hGood (x : X) : Good (solve x) := (hex x).choose_spec.1
  have hinit (x : X) : initial (solve x) = x.1 := (hex x).choose_spec.2
  have hlocal (x : X) (r : unitInterval) : phase (curve (solve x) r) = 0 ∧
      E (curve (solve x) r) ≤ Real.exp (-a*τ*(r:ℝ))*E x.1 := by
    have hh := hdecay (solve x) (hGood x) (by rw [hinit]; exact x.2.1) r
    simpa only [hinit] using hh
  have hstep (x : X) : phase (curve (solve x) globalHalf) = 0 ∧
      2*E (curve (solve x) globalHalf) ≤ ε^2 := by
    have hh := hlocal x globalHalf
    have hnonneg : 0 ≤ E x.1 := by nlinarith only [hlow x.1,sq_nonneg ‖x.1‖]
    have he : Real.exp (-a*τ*(globalHalf:ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by dsimp only [globalHalf]; nlinarith only [mul_pos ha hτ])
    have he' : E (curve (solve x) globalHalf) ≤ E x.1 :=
      hh.2.trans ((mul_le_mul_of_nonneg_right he hnonneg).trans_eq (one_mul _))
    exact ⟨hh.1,(mul_le_mul_of_nonneg_left he' (by norm_num : (0:ℝ) ≤ 2)).trans x.2.2⟩
  let step : X → X := fun x => ⟨curve (solve x) globalHalf,hstep x⟩
  let x : ℕ → X := Nat.rec ⟨x₀,hphase,henergy⟩ (fun _ z => step z)
  let y : ℕ → Y := fun n => solve (x n)
  have hnext (n : ℕ) : initial (y (n+1)) = curve (y n) globalHalf := hinit (x (n+1))
  have hstart : initial (y 0) = x₀ := hinit (x 0)
  have hinitialE (n : ℕ) : E (initial (y n)) ≤ Real.exp (-a*τ*((n:ℝ)/2))*E x₀ := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_div,mul_zero,Real.exp_zero,one_mul,hstart] using (le_refl (E x₀))
    | succ n ih =>
      calc
        E (initial (y (n+1))) = E (curve (y n) globalHalf) := congrArg E (hnext n)
        _ ≤ Real.exp (-a*τ*(globalHalf:ℝ))*E (initial (y n)) :=
          (hdecay (y n) (hGood (x n)) (by rw [hinit]; exact (x n).2.1) globalHalf).2
        _ ≤ Real.exp (-a*τ*(globalHalf:ℝ))*(Real.exp (-a*τ*((n:ℝ)/2))*E x₀) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (-a*τ*(((n+1:ℕ):ℝ)/2))*E x₀ := by
          rw [← mul_assoc,← Real.exp_add]
          apply congrArg (fun z : ℝ => Real.exp z*E x₀)
          dsimp only [globalHalf]
          push_cast
          ring
  refine ⟨y,fun n => hGood (x n),hstart,hnext,?_⟩
  intro n r
  have hl := hdecay (y n) (hGood (x n)) (by rw [hinit]; exact (x n).2.1) r
  refine ⟨hl.1,hl.2.trans ?_⟩
  calc
    Real.exp (-a*τ*(r:ℝ))*E (initial (y n)) ≤
        Real.exp (-a*τ*(r:ℝ))*(Real.exp (-a*τ*((n:ℝ)/2))*E x₀) :=
      mul_le_mul_of_nonneg_left (hinitialE n) (Real.exp_pos _).le
    _ = Real.exp (-a*τ*((n:ℝ)/2+(r:ℝ)))*E x₀ := by
      rw [← mul_assoc,← Real.exp_add]
      apply congrArg (fun z : ℝ => Real.exp z*E x₀)
      ring

/-- Physical time associated with a point of a segment of length tau,
when successive segments start tau/2 apart. -/
def circleParabolicSegmentTime (τ : ℝ) (hτ : 0 < τ) (n : ℕ) (r : unitInterval) : ℝ≥0 :=
  ⟨τ*((n:ℝ)/2+(r:ℝ)),mul_nonneg hτ.le (add_nonneg (by positivity) r.property.1)⟩

private theorem global_continuation_of_curves
    {H Y : Type*} [NormedAddCommGroup H]
    (initial : Y → H) (curve : Y → C(unitInterval,H)) (Good : Y → Prop)
    (hcurve0 : ∀ y, curve y 0 = initial y)
    (phase : H → ℂ) (E : H → ℝ)
    (τ a ε CE : ℝ) (hτ : 0 < τ) (ha : 0 < a) (hε : 0 < ε) (hCE : 0 ≤ CE)
    (hlow : ∀ x, ‖x‖^2 ≤ 2*E x) (hupp : ∀ x, E x ≤ CE*‖x‖^2)
    (hsolve : ∀ x, phase x = 0 → ‖x‖ ≤ ε → ∃ y, Good y ∧ initial y = x)
    (hdecay : ∀ y, Good y → phase (initial y) = 0 → ∀ r : unitInterval,
      phase (curve y r) = 0 ∧ E (curve y r) ≤ Real.exp (-a*τ*(r:ℝ))*E (initial y))
    (hmatch : ∀ y z, Good y → Good z → initial z = curve y globalHalf →
      ∀ r, curve y (globalRight r) = curve z (globalLeft r)) :
    ∃ η > 0, ∀ x₀ : H, phase x₀ = 0 → ‖x₀‖ ≤ η →
      ∃ u : C(ℝ≥0,H), ∃ U : ℕ → Y,
        u 0 = x₀ ∧ (∀ n, Good (U n)) ∧
        (∀ n r, u (circleParabolicSegmentTime τ hτ n r) = curve (U n) r) ∧
        (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (r : unitInterval),
          (0:ℝ) < (r:ℝ) ∧ (r:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n r = t) ∧
        ∀ t : ℝ≥0, phase (u t) = 0 ∧ E (u t) ≤ Real.exp (-a*(t:ℝ))*E x₀ := by
  obtain ⟨η,hη,hsmall⟩ := small_initial_energy E CE ε hCE hε hupp
  refine ⟨η,hη,?_⟩
  intro x₀ hphase hnorm
  obtain ⟨U,hGood,hstart,hnext,hsegment⟩ := energy_iteration
    initial curve Good phase E τ a ε hτ ha hε hlow hsolve hdecay x₀ hphase (hsmall x₀ hnorm)
  have hoverlap (n : ℕ) (r : unitInterval) :
      curve (U n) (globalRight r) = curve (U (n+1)) (globalLeft r) :=
    hmatch (U n) (U (n+1)) (hGood n) (hGood (n+1)) (hnext n) r
  obtain ⟨g,hg,hcover⟩ := global_continuous_charts (fun n => curve (U n)) hoverlap
  let scale : C(ℝ≥0,ℝ≥0) :=
    ⟨fun t => ⟨(t:ℝ)/τ,div_nonneg (NNReal.coe_nonneg t) hτ.le⟩,
      (continuous_subtype_val.div_const τ).subtype_mk _⟩
  let u : C(ℝ≥0,H) := g.comp scale
  have hscale (n : ℕ) (r : unitInterval) :
      scale (circleParabolicSegmentTime τ hτ n r) = globalChartTime n r := by
    apply Subtype.ext
    change (τ*((n:ℝ)/2+(r:ℝ)))/τ = (n:ℝ)/2+(r:ℝ)
    field_simp [ne_of_gt hτ]
  have hrepr (n : ℕ) (r : unitInterval) :
      u (circleParabolicSegmentTime τ hτ n r) = curve (U n) r := by
    change g (scale (circleParabolicSegmentTime τ hτ n r)) = _
    exact (congrArg g (hscale n r)).trans (hg n r)
  have hphysicalcover (t : ℝ≥0) : ∃ n r, circleParabolicSegmentTime τ hτ n r = t ∧
      (0 < t → (0:ℝ) < (r:ℝ) ∧ (r:ℝ) < 1) := by
    obtain ⟨n,r,ht,hstrict⟩ := hcover (scale t)
    refine ⟨n,r,?_,?_⟩
    · apply Subtype.ext
      have hreal := congrArg (fun z : ℝ≥0 => (z:ℝ)) ht
      change (n:ℝ)/2+(r:ℝ) = (t:ℝ)/τ at hreal
      change τ*((n:ℝ)/2+(r:ℝ)) = (t:ℝ)
      calc
        τ*((n:ℝ)/2+(r:ℝ)) = τ*((t:ℝ)/τ) := congrArg (fun z : ℝ => τ*z) hreal
        _ = (t:ℝ) := by field_simp [ne_of_gt hτ]
    · intro htpos
      have hscaled : (0:ℝ≥0) < scale t := by
        change 0 < (t:ℝ)/τ
        exact div_pos (show (0:ℝ) < (t:ℝ) from htpos) hτ
      exact hstrict hscaled
  have hzero : circleParabolicSegmentTime τ hτ 0 0 = 0 := by
    apply Subtype.ext
    norm_num [circleParabolicSegmentTime]
  have hinitcurve : curve (U 0) 0 = x₀ := (hcurve0 (U 0)).trans hstart
  refine ⟨u,U,?_,hGood,hrepr,?_,?_⟩
  · exact (congrArg u hzero.symm).trans ((hrepr 0 0).trans hinitcurve)
  · intro t ht
    obtain ⟨n,r,hr,hstrict⟩ := hphysicalcover t
    exact ⟨n,r,(hstrict ht).1,(hstrict ht).2,hr⟩
  · intro t
    obtain ⟨n,r,ht,hstrict⟩ := hphysicalcover t
    have hv : u t = curve (U n) r := (congrArg u ht.symm).trans (hrepr n r)
    have htime := congrArg (fun z : ℝ≥0 => (z:ℝ)) ht
    change τ*((n:ℝ)/2+(r:ℝ)) = (t:ℝ) at htime
    have hexp : -a*τ*((n:ℝ)/2+(r:ℝ)) = -a*(t:ℝ) := by
      calc
        -a*τ*((n:ℝ)/2+(r:ℝ)) = -a*(τ*((n:ℝ)/2+(r:ℝ))) := by ring
        _ = -a*(t:ℝ) := congrArg (fun z : ℝ => -a*z) htime
    have hs := hsegment n r
    exact ⟨(congrArg phase hv).trans hs.1,
      (congrArg E hv).trans_le (hs.2.trans_eq (congrArg (fun z : ℝ => Real.exp z*E x₀) hexp))⟩

private theorem half_witness_overlap
    {Y H : Type*} (initial : Y → H) (curve : Y → unitInterval → H) (Good : Y → Prop)
    (hunique : ∀ U V, initial U = initial V → Good U → Good V → U = V)
    (U V : Y) (hU : Good U) (hV : Good V)
    (left right : unitInterval → H) (a b : H)
    (hinitU : initial U = a) (hinitV : initial V = b) (hab : a = b)
    (hleft : ∀ r, curve U r = left r) (hright : ∀ r, curve V r = right r) :
    ∀ r, left r = right r := by
  have heq : U = V := hunique U V (hinitU.trans (hab.trans hinitV.symm)) hU hV
  intro r
  exact (hleft r).symm.trans ((congrArg (fun W => curve W r) heq).trans (hright r))

private theorem global_left_affine (r : unitInterval) :
    unitTimeAffine 0 globalHalf (by change (0:ℝ) < 1/2; norm_num) r = globalLeft r := by
  apply Subtype.ext
  change 0+((1/2:ℝ)-0)*(r:ℝ) = (r:ℝ)/2
  ring

private theorem global_right_affine (r : unitInterval) :
    unitTimeAffine globalHalf 1 (by change (1/2:ℝ) < 1; norm_num) r = globalRight r := by
  apply Subtype.ext
  change (1/2:ℝ)+(1-1/2)*(r:ℝ) = (1+(r:ℝ))/2
  ring

variable (T : ℝ) [Fact (0 < T)]

private def globalParabolicGood (τ δ : ℝ)
    (F : CircleSobolevSpace T 4 → CircleL2 T) (U : CircleParabolicSpace T τ) : Prop :=
  ‖circleParabolicCurve T τ U‖ < δ ∧
    ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r = F (circleParabolicH4 T τ U r)

set_option maxHeartbeats 800000 in
private theorem actual_half_overlap
    (τ : ℝ) (hτ : 0 < τ) (δ : ℝ)
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (hunique : ∀ σ : ℝ, 0 < σ → ∀ U V : CircleParabolicSpace T σ,
      circleParabolicInitialValue T σ U = circleParabolicInitialValue T σ V →
      globalParabolicGood T σ δ F U → globalParabolicGood T σ δ F V → U = V)
    (U V : CircleParabolicSpace T τ)
    (hnext : circleParabolicInitialValue T τ V = circleParabolicCurve T τ U globalHalf)
    (hU : globalParabolicGood T τ δ F U) (hV : globalParabolicGood T τ δ F V) :
    ∀ r, circleParabolicCurve T τ U (globalRight r) = circleParabolicCurve T τ V (globalLeft r) := by
  have hUD := circle_parabolic_half_restrictions T τ U
  have hVD := circle_parabolic_half_restrictions T τ V
  let U₁ : CircleParabolicSpace T (τ/2) := hUD.choose_spec.choose
  let V₀ : CircleParabolicSpace T (τ/2) := hVD.choose
  have hU₁ := hUD.choose_spec.choose_spec.2
  have hV₀ := hVD.choose_spec.choose_spec.1
  have hgU : globalParabolicGood T (τ/2) δ F U₁ :=
    ⟨hU₁.2.2.2.2.1.trans_lt hU.1,hU₁.2.2.2.2.2 F hU.2⟩
  have hgV : globalParabolicGood T (τ/2) δ F V₀ :=
    ⟨hV₀.2.2.2.2.1.trans_lt hV.1,hV₀.2.2.2.2.2 F hV.2⟩
  exact half_witness_overlap
    (circleParabolicInitialValue T (τ/2)) (fun W r => circleParabolicCurve T (τ/2) W r)
    (globalParabolicGood T (τ/2) δ F) (hunique (τ/2) (half_pos hτ)) U₁ V₀ hgU hgV
    (fun r => circleParabolicCurve T τ U (globalRight r))
    (fun r => circleParabolicCurve T τ V (globalLeft r))
    (circleParabolicCurve T τ U globalHalf) (circleParabolicInitialValue T τ V)
    hU₁.2.2.2.1 hV₀.2.2.2.1 hnext.symm
    (fun r => (hU₁.1 r).trans (congrArg (circleParabolicCurve T τ U) (global_right_affine r)))
    (fun r => (hV₀.1 r).trans (congrArg (circleParabolicCurve T τ V) (global_left_affine r)))

set_option maxHeartbeats 800000 in
/-- Continuation of genuine local parabolic solutions by overlaps of half their
duration.  All positive times lie inside one of the displayed actual local
solutions.  The hypotheses are local existence, local energy decay, an energy
equivalent to the H2 norm, and uniqueness in the common small H2 neighbourhood. -/
theorem circle_parabolic_global_continuation
    (τ a ε δ CE : ℝ) (hτ : 0 < τ) (ha : 0 < a) (hε : 0 < ε)
    (hCE : 0 ≤ CE)
    (F : CircleSobolevSpace T 4 → CircleL2 T)
    (phase : CircleSobolevSpace T 2 →L[ℂ] ℂ)
    (E : CircleSobolevSpace T 2 → ℝ)
    (P : CircleParabolicSpace T τ → Prop)
    (hlow : ∀ x, ‖x‖^2 ≤ 2*E x)
    (hupp : ∀ x, E x ≤ CE*‖x‖^2)
    (hsolve : ∀ x, phase x = 0 → ‖x‖ ≤ ε →
      ∃ U : CircleParabolicSpace T τ,
        circleParabolicInitialValue T τ U = x ∧
        (‖circleParabolicCurve T τ U‖ < δ ∧
          ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r = F (circleParabolicH4 T τ U r)) ∧
        P U)
    (hdecay : ∀ U : CircleParabolicSpace T τ,
      phase (circleParabolicInitialValue T τ U) = 0 →
      ‖circleParabolicCurve T τ U‖ < δ →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ U r = F (circleParabolicH4 T τ U r)) →
      ∀ r : unitInterval, phase (circleParabolicCurve T τ U r) = 0 ∧
        E (circleParabolicCurve T τ U r) ≤
          Real.exp (-a*τ*(r:ℝ))*E (circleParabolicInitialValue T τ U))
    (hunique : ∀ σ : ℝ, 0 < σ → ∀ U V : CircleParabolicSpace T σ,
      circleParabolicInitialValue T σ U = circleParabolicInitialValue T σ V →
      ‖circleParabolicCurve T σ U‖ < δ → ‖circleParabolicCurve T σ V‖ < δ →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T σ U r = F (circleParabolicH4 T σ U r)) →
      (∀ᵐ r ∂volume, circleParabolicTimeDerivative T σ V r = F (circleParabolicH4 T σ V r)) → U = V) :
    ∃ η > 0, ∀ x₀ : CircleSobolevSpace T 2, phase x₀ = 0 → ‖x₀‖ ≤ η →
      ∃ u : C(ℝ≥0,CircleSobolevSpace T 2), ∃ U : ℕ → CircleParabolicSpace T τ,
        u 0 = x₀ ∧
        (∀ n, (‖circleParabolicCurve T τ (U n)‖ < δ ∧
          ∀ᵐ r ∂volume, circleParabolicTimeDerivative T τ (U n) r = F (circleParabolicH4 T τ (U n) r)) ∧
          P (U n)) ∧
        (∀ n r, u (circleParabolicSegmentTime τ hτ n r) = circleParabolicCurve T τ (U n) r) ∧
        (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (r : unitInterval), (0:ℝ) < (r:ℝ) ∧ (r:ℝ) < 1 ∧
          circleParabolicSegmentTime τ hτ n r = t) ∧
        ∀ t : ℝ≥0, phase (u t) = 0 ∧ E (u t) ≤ Real.exp (-a*(t:ℝ))*E x₀ := by
  let Good : CircleParabolicSpace T τ → Prop := fun U => globalParabolicGood T τ δ F U ∧ P U
  have hlocal : ∀ x, phase x = 0 → ‖x‖ ≤ ε →
      ∃ U : CircleParabolicSpace T τ, Good U ∧ circleParabolicInitialValue T τ U = x := by
    intro x hp hx
    exact (hsolve x hp hx).imp (fun U hU => ⟨hU.2,hU.1⟩)
  have henergy : ∀ U : CircleParabolicSpace T τ, Good U →
      phase (circleParabolicInitialValue T τ U) = 0 → ∀ r : unitInterval,
        phase (circleParabolicCurve T τ U r) = 0 ∧
          E (circleParabolicCurve T τ U r) ≤
            Real.exp (-a*τ*(r:ℝ))*E (circleParabolicInitialValue T τ U) := by
    intro U hU hp
    exact hdecay U hp hU.1.1 hU.1.2
  have huniq : ∀ σ : ℝ, 0 < σ → ∀ U V : CircleParabolicSpace T σ,
      circleParabolicInitialValue T σ U = circleParabolicInitialValue T σ V →
      globalParabolicGood T σ δ F U → globalParabolicGood T σ δ F V → U = V := by
    intro σ hσ U V hi hU hV
    exact hunique σ hσ U V hi hU.1 hV.1 hU.2 hV.2
  have hmatch : ∀ U V : CircleParabolicSpace T τ, Good U → Good V →
      circleParabolicInitialValue T τ V = circleParabolicCurve T τ U globalHalf →
      ∀ r, circleParabolicCurve T τ U (globalRight r) = circleParabolicCurve T τ V (globalLeft r) := by
    intro U V hU hV hn
    exact actual_half_overlap T τ hτ δ F huniq U V hn hU.1 hV.1
  exact global_continuation_of_curves
    (circleParabolicInitialValue T τ) (circleParabolicCurve T τ) Good (fun U => rfl)
    phase E τ a ε CE hτ ha hε hCE hlow hupp hlocal henergy hmatch

end Lemniscate
