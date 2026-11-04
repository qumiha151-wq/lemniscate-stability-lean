import Lemniscate.PeriodicParabolicGlobalSolution
import Lemniscate.BernoulliParabolicLocalSolution
import Lemniscate.BernoulliParabolicEnergyEstimate
import Lemniscate.PeriodicParabolicNonlinearUniqueness
import Lemniscate.PeriodicSobolevEnergyNorm

/-! Global small-data stability of the actual modulated Bernoulli equation.

The time interval and linear inverse are those of the uniform local theorem.
Energy decay keeps the restart values small, actual half restrictions and
uniqueness identify overlaps, and the retained local witness gives both the
common parabolic bound and realness. 
-/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter Set CoarseArithmetic
open scoped ENNReal NNReal Topology ComplexConjugate

private theorem discard_local_uniqueness
    {H X : Type*} (N : H → ℝ) (R : ℝ → H → X → Prop) (P : H → X → Prop)
    (h : ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ x : H, N x ≤ ε → ∃ U : X, R r x U ∧ P x U ∧
        ∀ V : X, R r x V → V = U) :
    ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ x : H, N x ≤ ε → ∃ U : X, R r x U ∧ P x U := by
  intro η hη
  obtain ⟨ε,hε,r,hr,hrη,hs⟩ := h η hη
  exact ⟨ε,hε,r,hr,hrη,fun x hx => (hs x hx).imp (fun U hU => ⟨hU.1,hU.2.1⟩)⟩

private theorem segment_restart_data
    {H Y : Type*} (initial : Y → H) (curve : Y → unitInterval → H)
    (hc0 : ∀ y, curve y 0 = initial y)
    (τ : ℝ) (hτ : 0 < τ) (u : ℝ≥0 → H) (U : ℕ → Y) (x₀ : H)
    (h₀ : u 0 = x₀)
    (hrep : ∀ n r, u (circleParabolicSegmentTime τ hτ n r) = curve (U n) r) :
    initial (U 0) = x₀ ∧
      ∀ n, initial (U (n+1)) = curve (U n) ⟨1/2,by constructor <;> norm_num⟩ := by
  have hz : circleParabolicSegmentTime τ hτ 0 0 = 0 := by
    apply Subtype.ext
    norm_num [circleParabolicSegmentTime]
  refine ⟨(hc0 (U 0)).symm.trans ((hrep 0 0).symm.trans ((congrArg u hz).trans h₀)),?_⟩
  intro n
  let m : unitInterval := ⟨1/2,by constructor <;> norm_num⟩
  have ht : circleParabolicSegmentTime τ hτ (n+1) 0 = circleParabolicSegmentTime τ hτ n m := by
    apply Subtype.ext
    change τ*(((n+1:ℕ):ℝ)/2+0) = τ*((n:ℝ)/2+1/2)
    push_cast
    ring
  exact (hc0 (U (n+1))).symm.trans
    ((hrep (n+1) 0).symm.trans ((congrArg u ht).trans (hrep n m)))

private theorem segment_real_iteration
    {H Y : Type*} (initial : Y → H) (curve : Y → unitInterval → H)
    (j : H → H) (J : Y → Y) (U : ℕ → Y)
    (hJcurve : ∀ y r, curve (J y) r = j (curve y r))
    (hmeta : ∀ n, j (initial (U n)) = initial (U n) → J (U n) = U n)
    (h₀ : j (initial (U 0)) = initial (U 0))
    (hnext : ∀ n, initial (U (n+1)) = curve (U n) ⟨1/2,by constructor <;> norm_num⟩) :
    ∀ n, J (U n) = U n ∧ ∀ r, j (curve (U n) r) = curve (U n) r := by
  intro n
  induction n with
  | zero =>
    have hJ := hmeta 0 h₀
    exact ⟨hJ,fun r => (hJcurve (U 0) r).symm.trans
      (congrArg (fun y => curve y r) hJ)⟩
  | succ n ih =>
    have hi : j (initial (U (n+1))) = initial (U (n+1)) :=
      (congrArg j (hnext n)).trans ((ih.2 _).trans (hnext n).symm)
    have hJ := hmeta (n+1) hi
    exact ⟨hJ,fun r => (hJcurve (U (n+1)) r).symm.trans
      (congrArg (fun y => curve y r) hJ)⟩

private theorem energy_to_norm_decay
    {H : Type*} [NormedAddCommGroup H] (E : H → ℝ) (CE μ t : ℝ)
    (hCE : 0 < CE) (x y : H)
    (hx : ‖x‖^2 ≤ 2*E x) (hy : E y ≤ CE*‖y‖^2)
    (hdecay : E x ≤ Real.exp (-2*μ*t)*E y) :
    ‖x‖ ≤ Real.sqrt (2*CE)*Real.exp (-μ*t)*‖y‖ := by
  have he : (Real.exp (-μ*t))^2 = Real.exp (-2*μ*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hs : (Real.sqrt (2*CE))^2 = 2*CE := Real.sq_sqrt (by positivity)
  have hsq : ‖x‖^2 ≤ (Real.sqrt (2*CE)*Real.exp (-μ*t)*‖y‖)^2 := by
    calc
      ‖x‖^2 ≤ 2*E x := hx
      _ ≤ 2*(Real.exp (-2*μ*t)*(CE*‖y‖^2)) :=
        mul_le_mul_of_nonneg_left (hdecay.trans
          (mul_le_mul_of_nonneg_left hy (Real.exp_pos _).le)) (by norm_num)
      _ = (Real.sqrt (2*CE)*Real.exp (-μ*t)*‖y‖)^2 := by rw [mul_pow,mul_pow,hs,he]; ring
  exact (sq_le_sq₀ (norm_nonneg x) (by positivity)).mp hsq

private theorem real_norm_orbit_of_data
    {H Y : Type*} [NormedAddCommGroup H]
    (initial : Y → H) (curve : Y → C(unitInterval,H))
    (hc0 : ∀ y, curve y 0 = initial y)
    (j : H → H) (J : Y → Y) (hJcurve : ∀ y t, curve (J y) t = j (curve y t))
    (N : Y → ℝ) (A B : Y → Prop) (hAB : ∀ y, A y → B y)
    (phase : H → ℂ) (E : H → ℝ) (CE : ℝ) (hCE : 0 < CE)
    (hlow : ∀ x, ‖x‖^2 ≤ 2*E x) (hupp : ∀ x, E x ≤ CE*‖x‖^2)
    (τ : ℝ) (hτ : 0 < τ) (μ r : ℝ) (x₀ : H) (hxreal : j x₀ = x₀)
    (h : ∃ u : C(ℝ≥0,H), ∃ U : ℕ → Y,
      u 0 = x₀ ∧
      (∀ n, A (U n) ∧ N (U n) ≤ r ∧
        (j (initial (U n)) = initial (U n) → J (U n) = U n)) ∧
      (∀ n t, u (circleParabolicSegmentTime τ hτ n t) = curve (U n) t) ∧
      (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (s : unitInterval),
        (0:ℝ) < (s:ℝ) ∧ (s:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n s = t) ∧
      ∀ t : ℝ≥0, phase (u t) = 0 ∧ E (u t) ≤ Real.exp (-(2*μ)*(t:ℝ))*E x₀) :
    ∃ u : C(ℝ≥0,H), ∃ U : ℕ → Y,
      u 0 = x₀ ∧
      (∀ n, N (U n) ≤ r ∧ J (U n) = U n ∧ B (U n)) ∧
      (∀ n t, u (circleParabolicSegmentTime τ hτ n t) = curve (U n) t) ∧
      (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (s : unitInterval),
        (0:ℝ) < (s:ℝ) ∧ (s:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n s = t) ∧
      ∀ t : ℝ≥0, j (u t) = u t ∧ phase (u t) = 0 ∧
        ‖u t‖ ≤ Real.sqrt (2*CE)*Real.exp (-μ*(t:ℝ))*‖x₀‖ := by
  obtain ⟨u,U,hu₀,hseg,hrep,hcover,hbound⟩ := h
  have hrestart := segment_restart_data initial (fun y t => curve y t) hc0 τ hτ u U x₀ hu₀ hrep
  have hreal := segment_real_iteration initial (fun y t => curve y t) j J U hJcurve
    (fun n => (hseg n).2.2) (by simpa only [hrestart.1] using hxreal) hrestart.2
  refine ⟨u,U,hu₀,?_,hrep,hcover,?_⟩
  · intro n
    exact ⟨(hseg n).2.1,(hreal n).1,hAB (U n) (hseg n).1⟩
  · intro t
    have hrt : j (u t) = u t := by
      by_cases ht : t = 0
      · simpa only [ht,hu₀] using hxreal
      · obtain ⟨n,s,_,_,hs⟩ := hcover t (lt_of_le_of_ne (show (0:ℝ≥0) ≤ t from zero_le) (Ne.symm ht))
        have hv : u t = curve (U n) s := (congrArg u hs.symm).trans (hrep n s)
        exact (congrArg j hv).trans (((hreal n).2 s).trans hv.symm)
    exact ⟨hrt,(hbound t).1,energy_to_norm_decay E CE μ (t:ℝ) hCE (u t) x₀
      (hlow _) (hupp _) (by
        have he : -(2*μ)*(t:ℝ) = -2*μ*(t:ℝ) := by ring
        simpa only [he] using (hbound t).2)⟩

private theorem radius_orbit_transport
    {H : Type*} {Real Phase : H → Prop} {Small : ℝ → H → Prop}
    {A B : H → Prop}
    (h : ∃ ε > 0, ∀ x, Phase x → Small ε x → A x)
    (k : ∀ x, Real x → A x → B x) :
    ∃ ε > 0, ∀ x, Real x → Phase x → Small ε x → B x := by
  obtain ⟨ε,hε,hs⟩ := h
  exact ⟨ε,hε,fun x hx hp hn => k x hx (hs x hp hn)⟩

private theorem fixed_radius_transport {P : ℝ → ℝ → Prop}
    {η : ℝ} (r : ℝ) (hr : 0 < r) (hrη : r < η)
    (h : ∃ ε > 0, P ε r) :
    ∃ ε > 0, ∃ s > 0, s < η ∧ P ε s := by
  obtain ⟨ε,hε,hP⟩ := h
  exact ⟨ε,hε,r,hr,hrη,hP⟩

private theorem unique_radius_transport {P : ℝ → Prop} {Q : Prop} {δ₀ : ℝ}
    (h : ∃ δ > 0, δ ≤ δ₀ ∧ P δ)
    (k : ∀ δ, 0 < δ → δ ≤ δ₀ → P δ → Q) : Q := by
  obtain ⟨δ,hδ,hδ₀,hP⟩ := h
  exact k δ hδ hδ₀ hP

private theorem positive_triple_transport {P : ℝ → ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, ∃ c > 0, P a b c)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → ∀ c, 0 < c → P a b c → Q) : Q := by
  obtain ⟨a,ha,b,hb,c,hc,hP⟩ := h
  exact k a ha b hb c hc hP

private theorem use_tame_radius_data {Z : Prop} {A : ℝ → ℝ → Prop}
    (h : ∃ δ > 0, ∃ C > 0, A δ C)
    (k : ∀ δ, 0 < δ → ∀ C, 0 < C → A δ C → Z) : Z := by
  obtain ⟨δ,hδ,C,hC,hA⟩ := h
  exact k δ hδ C hC hA

private theorem local_small_metadata
    {H Y : Type*} (initial : Y → H) (N : H → ℝ) (size M : Y → ℝ)
    (j : H → H) (J : Y → Y) (P : Y → Prop)
    (ε r δ : ℝ) (hrδ : r < δ) (hsize : ∀ y, size y ≤ M y)
    (hsolve : ∀ x, N x ≤ ε → ∃ y,
      (M y ≤ r ∧ initial y = x ∧ P y) ∧ (j x = x → J y = y)) :
    ∀ x, N x ≤ ε → ∃ y, initial y = x ∧ (size y < δ ∧ P y) ∧
      (M y ≤ r ∧ (j (initial y) = initial y → J y = y)) := by
  intro x hx
  obtain ⟨y,hy,hJ⟩ := hsolve x hx
  refine ⟨y,hy.2.1,⟨(hsize y).trans_lt (hy.1.trans_lt hrδ),hy.2.2⟩,hy.1,?_⟩
  intro hreal
  exact hJ ((congrArg j hy.2.1).symm.trans (hreal.trans hy.2.1))

private theorem local_energy_transport
    {H Y : Type*} (initial : Y → H) (curve : Y → unitInterval → H)
    (hc0 : ∀ y, curve y 0 = initial y)
    (phase : H → ℂ) (E : H → ℝ) (size : Y → ℝ)
    (P : Y → Prop) {D : Y → unitInterval → Prop}
    (τ μ δ δE : ℝ) (hδ : δ ≤ δE)
    (hdecay : ∀ y, phase (initial y) = 0 → size y < δE → P y →
      (∀ t, phase (curve y t) = 0) ∧ ∀ t : unitInterval,
        E (curve y t) ≤ Real.exp (-2*τ*μ*(t:ℝ))*E (curve y 0) ∧ D y t) :
    ∀ y, phase (initial y) = 0 → size y < δ → P y → ∀ t : unitInterval,
      phase (curve y t) = 0 ∧
        E (curve y t) ≤ Real.exp (-(2*μ)*τ*(t:ℝ))*E (initial y) := by
  intro y hi hs hp t
  have hd := hdecay y hi (hs.trans_le hδ) hp
  refine ⟨hd.1 t,((hd.2 t).1).trans_eq ?_⟩
  exact congrArg₂ (fun a b : ℝ => Real.exp a*b) (by ring) (congrArg E (hc0 y))

section Data
variable (S : ℝ) [Fact (0 < S)]

private def bernoulliGlobalEnergy (V : CircleL2 S →L[ℂ] CircleL2 S)
    (κ : ℝ) (f : CircleSobolevSpace S 2) : ℝ :=
  ‖circleSobolevCoordinate S 2 0 f‖^2+4*‖circleSobolevCoordinate S 2 2 f‖^2+
    κ*‖V (circleSobolevCoordinate S 2 0 f)‖^2

private def bernoulliGlobalLocalData
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S) (τ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
    ∀ x : CircleSobolevSpace S 2, ‖x‖ ≤ ε → ∃ U : CircleParabolicSpace S τ,
      (‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = x ∧
        ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
          circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) ∧
      (circleSobolevConjugation S 2 x = x → circleParabolicConjugation S τ U = U)

private def bernoulliGlobalEnergyData
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (V : CircleL2 S →L[ℂ] CircleL2 S) (g : ℝ) : Prop :=
  ∀ μ : ℝ, 0 < μ → μ < g →
    ∃ κ > 0, ∃ δ > 0, ∃ c > 0,
      (∀ h : CircleSobolevSpace S 2, ‖h‖ < δ →
        circleNormalGraphRotationFunctional S Ψ (circleNormalGraphRotationField S K h) ≠ 0) ∧
      ∀ σ : ℝ, 0 < σ → ∀ U : CircleParabolicSpace S σ,
        inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S σ U)) = 0 →
        ‖circleParabolicCurve S σ U‖ < δ →
        (∀ᵐ r ∂volume, circleParabolicTimeDerivative S σ U r =
          circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S σ U r)) →
        let E : unitInterval → ℝ := fun r =>
          bernoulliGlobalEnergy S V κ (circleParabolicCurve S σ U r)
        (∀ r, inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicCurve S σ U r)) = 0) ∧
          ∀ t : unitInterval, E t ≤ Real.exp (-2*σ*μ*(t:ℝ))*E 0 ∧
            (2*σ*c)*(∫ r in Iic t, ‖circleParabolicH4 S σ U r‖^2 ∂volume) ≤ E 0

private def bernoulliGlobalOrbit
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (τ : ℝ) (hτ : 0 < τ) (μ C r : ℝ) (x₀ : CircleSobolevSpace S 2) : Prop :=
  ∃ u : C(ℝ≥0,CircleSobolevSpace S 2), ∃ U : ℕ → CircleParabolicSpace S τ,
          u 0 = x₀ ∧
          (∀ n, ‖U n‖ ≤ r ∧ circleParabolicConjugation S τ (U n) = U n ∧
            ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ (U n) t =
              circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ (U n) t)) ∧
          (∀ n t, u (circleParabolicSegmentTime τ hτ n t) = circleParabolicCurve S τ (U n) t) ∧
          (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (s : unitInterval),
            (0:ℝ) < (s:ℝ) ∧ (s:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n s = t) ∧
          ∀ t : ℝ≥0, circleSobolevConjugation S 2 (u t) = u t ∧
            inner ℂ Ψ (circleSobolevCoordinate S 2 0 (u t)) = 0 ∧
            ‖u t‖ ≤ C*Real.exp (-μ*(t:ℝ))*‖x₀‖

private def bernoulliGlobalConclusion
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (τ : ℝ) (hτ : 0 < τ) (g : ℝ) : Prop :=
  ∀ μ : ℝ, 0 < μ → μ < g → ∃ C > 0,
    ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
      ∀ x₀ : CircleSobolevSpace S 2,
        circleSobolevConjugation S 2 x₀ = x₀ →
        inner ℂ Ψ (circleSobolevCoordinate S 2 0 x₀) = 0 → ‖x₀‖ ≤ ε →
        bernoulliGlobalOrbit S K Ψ τ hτ μ C r x₀

set_option maxHeartbeats 1200000 in
private theorem bernoulli_global_at_radius
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (τ μ εL δ CE r : ℝ) (hτ : 0 < τ) (hμ : 0 < μ) (hεL : 0 < εL)
    (hCE : 0 < CE) (E : CircleSobolevSpace S 2 → ℝ)
    (hlow : ∀ x, ‖x‖^2 ≤ 2*E x) (hupp : ∀ x, E x ≤ CE*‖x‖^2)
    (hsol : ∀ x, inner ℂ Ψ (circleSobolevCoordinate S 2 0 x) = 0 → ‖x‖ ≤ εL →
      ∃ U : CircleParabolicSpace S τ,
        circleParabolicInitialValue S τ U = x ∧
        (‖circleParabolicCurve S τ U‖ < δ ∧
          ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
            circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) ∧
        (‖U‖ ≤ r ∧ (circleSobolevConjugation S 2 (circleParabolicInitialValue S τ U) =
          circleParabolicInitialValue S τ U → circleParabolicConjugation S τ U = U)))
    (hdecay : ∀ U : CircleParabolicSpace S τ,
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicInitialValue S τ U)) = 0 →
      ‖circleParabolicCurve S τ U‖ < δ →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S τ U t)) →
      ∀ t : unitInterval,
        inner ℂ Ψ (circleSobolevCoordinate S 2 0 (circleParabolicCurve S τ U t)) = 0 ∧
        E (circleParabolicCurve S τ U t) ≤
          Real.exp (-(2*μ)*τ*(t:ℝ))*E (circleParabolicInitialValue S τ U))
    (huniq : ∀ σ : ℝ, 0 < σ → ∀ U V : CircleParabolicSpace S σ,
      circleParabolicInitialValue S σ U = circleParabolicInitialValue S σ V →
      ‖circleParabolicCurve S σ U‖ < δ → ‖circleParabolicCurve S σ V‖ < δ →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S σ U t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S σ U t)) →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S σ V t =
        circleNormalGraphModulatedFlow S K (15/2) Ψ (circleParabolicH4 S σ V t)) → U = V) :
    ∃ ε > 0, ∀ x₀ : CircleSobolevSpace S 2,
      circleSobolevConjugation S 2 x₀ = x₀ →
      inner ℂ Ψ (circleSobolevCoordinate S 2 0 x₀) = 0 → ‖x₀‖ ≤ ε →
      bernoulliGlobalOrbit S K Ψ τ hτ μ (Real.sqrt (2*CE)) r x₀ := by
  let F := circleNormalGraphModulatedFlow S K (15/2) Ψ
  let phase : CircleSobolevSpace S 2 →L[ℂ] ℂ :=
    (innerSL ℂ Ψ).comp (circleSobolevCoordinate S 2 0)
  let P : CircleParabolicSpace S τ → Prop := fun U => ‖U‖ ≤ r ∧
    (circleSobolevConjugation S 2 (circleParabolicInitialValue S τ U) =
      circleParabolicInitialValue S τ U → circleParabolicConjugation S τ U = U)
  refine radius_orbit_transport
    (circle_parabolic_global_continuation S τ (2*μ) εL δ CE hτ
      (by positivity) hεL hCE.le F phase E P hlow hupp hsol hdecay huniq) ?_
  intro x₀ hxreal hOrbit
  exact real_norm_orbit_of_data (circleParabolicInitialValue S τ)
    (fun W => circleParabolicCurve S τ W) (fun _ => rfl)
    (circleSobolevConjugation S 2) (circleParabolicConjugation S τ)
    (fun W t => (circle_parabolic_conjugation_components S τ W).1 t)
    (fun W : CircleParabolicSpace S τ => ‖W‖)
    (fun W => ‖circleParabolicCurve S τ W‖ < δ ∧
      ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ W t = F (circleParabolicH4 S τ W t))
    (fun W => ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ W t = F (circleParabolicH4 S τ W t))
    (fun _ hW => hW.2) phase E CE hCE hlow hupp τ hτ μ r x₀ hxreal hOrbit

set_option maxHeartbeats 1200000 in
private theorem bernoulli_global_of_data
    (K : BackgroundJetOver C(AddCircle S, ℂ)) (Ψ : CircleL2 S)
    (V : CircleL2 S →L[ℂ] CircleL2 S)
    (D : CircleSobolevSpace S 4 →L[ℂ] CircleL2 S)
    (B : CircleSobolevSpace S 2 →L[ℂ] CircleL2 S)
    (hBA : ∀ f, circleSobolevPrincipalOperator S f-
      B (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) = -(D f))
    (δ₀ C₀ : ℝ) (hδ₀ : 0 < δ₀) (hC₀ : 0 ≤ C₀)
    (htame : ∀ f g : CircleSobolevSpace S 4,
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖ < δ₀ →
      ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖ < δ₀ →
      ‖circleNormalGraphModulatedFlow S K (15/2) Ψ f-
        circleNormalGraphModulatedFlow S K (15/2) Ψ g-D (f-g)‖ ≤ C₀*
          ((‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)‖+
            ‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 g)‖)*‖f-g‖+
          (‖f‖+‖g‖)*‖circleSobolevInclusion S 2 (circleSobolevInclusion S 3 (f-g))‖))
    (τ : ℝ) (hτ : 0 < τ)
    (hlocal : bernoulliGlobalLocalData S K Ψ τ)
    (g : ℝ)
    (henergy : bernoulliGlobalEnergyData S K Ψ V g) :
    bernoulliGlobalConclusion S K Ψ τ hτ g := by
  let F := circleNormalGraphModulatedFlow S K (15/2) Ψ
  refine unique_radius_transport
    (circle_parabolic_nonlinear_uniqueness S F D B hBA δ₀ C₀ hδ₀ hC₀ htame) ?_
  intro δU hδU hδUle hunique
  intro μ hμ hμg
  refine positive_triple_transport (henergy μ hμ hμg) ?_
  intro κ hκ δE hδE c hc hEnergy
  have hdecay := hEnergy.2
  let E := bernoulliGlobalEnergy S V κ
  let CE : ℝ := 4+κ*‖V‖^2
  have hCE : 0 < CE := by dsimp only [CE]; positivity
  have hlow (x : CircleSobolevSpace S 2) : ‖x‖^2 ≤ 2*E x :=
    (circle_sobolev_energy_norm_equivalence S V κ hκ.le x).1
  have hupp (x : CircleSobolevSpace S 2) : E x ≤ CE*‖x‖^2 :=
    (circle_sobolev_energy_norm_equivalence S V κ hκ.le x).2
  refine ⟨Real.sqrt (2*CE),Real.sqrt_pos.2 (by positivity),?_⟩
  intro η hη
  let δ := min δU δE
  have hδ : 0 < δ := lt_min hδU hδE
  refine use_tame_radius_data (hlocal (min η δ) (lt_min hη hδ)) ?_
  intro εL hεL r hr hLocal
  have hrη : r < η := hLocal.1.trans_le (min_le_left _ _)
  have hrδ : r < δ := hLocal.1.trans_le (min_le_right _ _)
  let phase : CircleSobolevSpace S 2 → ℂ :=
    fun x => inner ℂ Ψ (circleSobolevCoordinate S 2 0 x)
  have hsol := fun (x : CircleSobolevSpace S 2) (_ : phase x = 0) (hx : ‖x‖ ≤ εL) =>
    local_small_metadata (circleParabolicInitialValue S τ) (fun x => ‖x‖)
      (fun U => ‖circleParabolicCurve S τ U‖) (fun U : CircleParabolicSpace S τ => ‖U‖)
      (circleSobolevConjugation S 2) (circleParabolicConjugation S τ)
      (fun U => ∀ᵐ t ∂volume,
        circleParabolicTimeDerivative S τ U t = F (circleParabolicH4 S τ U t))
      εL r δ hrδ (fun U => norm_fst_le U.1) hLocal.2 x hx
  have hlocalDecay := local_energy_transport
    (circleParabolicInitialValue S τ) (fun U t => circleParabolicCurve S τ U t)
    (fun _ => rfl) phase E (fun U => ‖circleParabolicCurve S τ U‖)
    (fun U => ∀ᵐ t ∂volume,
      circleParabolicTimeDerivative S τ U t = F (circleParabolicH4 S τ U t))
    τ μ δ δE (min_le_right _ _) (hdecay τ hτ)
  have huniq : ∀ σ : ℝ, 0 < σ → ∀ U V : CircleParabolicSpace S σ,
      circleParabolicInitialValue S σ U = circleParabolicInitialValue S σ V →
      ‖circleParabolicCurve S σ U‖ < δ → ‖circleParabolicCurve S σ V‖ < δ →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S σ U t = F (circleParabolicH4 S σ U t)) →
      (∀ᵐ t ∂volume, circleParabolicTimeDerivative S σ V t = F (circleParabolicH4 S σ V t)) → U = V := by
    intro σ hσ U V hi hU hV hPU hPV
    exact hunique σ hσ U V hi (hU.trans_le (min_le_left _ _))
      (hV.trans_le (min_le_left _ _)) hPU hPV
  exact fixed_radius_transport r hr hrη
    (bernoulli_global_at_radius S K Ψ τ μ εL δ CE r hτ hμ hεL hCE E
      hlow hupp hsol hlocalDecay huniq)

private theorem uniform_global_witness_transport
    {W : ℝ → Type*} {Q : ∀ τ, W τ → Prop} {L : ℝ → Prop}
    {G : ∀ τ : ℝ, 0 < τ → Prop}
    (h : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ∃ e : W τ, Q τ e ∧ L τ)
    (k : ∀ τ (hτ : 0 < τ), τ ≤ 1 → ∀ e : W τ, Q τ e → L τ → G τ hτ) :
    ∃ τ : ℝ, ∃ hτ : 0 < τ, τ ≤ 1 ∧ ∃ e : W τ, Q τ e ∧ G τ hτ := by
  obtain ⟨τ,hτ,hτ₁,e,he,hL⟩ := h
  exact ⟨τ,hτ,hτ₁,e,he,k τ hτ hτ₁ e he hL⟩

private theorem bernoulli_global_principal_split
    (Q P : C(AddCircle S, ℂ)) (hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1)
    (f : CircleSobolevSpace S 4) :
    circleSobolevPrincipalOperator S f-
      (circleSobolevCoordinate S 2 0+
        circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)))
          (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) =
      -(circleNormalGraphDerivative S (circleBernoulliBackground S Q P) (15/2) f) := by
  have hD : circleNormalGraphDerivative S (circleBernoulliBackground S Q P) (15/2) =
      circleSobolevOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4)) :=
    (circle_normal_graph_hasFDerivAt S (circleBernoulliBackground S Q P) (15/2)).unique
      (bernoulli_sobolev_flow_linearization S Q P hE).2
  rw [hD,circle_sobolev_operator_lower_order]
  have hv : circleSobolevCoordinate S 2 0
      (circleSobolevInclusion S 2 (circleSobolevInclusion S 3 f)) =
        circleSobolevCoordinate S 4 0 f := rfl
  simp only [circleSobolevPrincipalOperator,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,hv]
  module

end Data

variable (T S : ℝ) [Fact (0 < T)] [Fact (0 < S)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
include hq hp he hqreal hpreal hs hc ho hr

set_option maxHeartbeats 1200000 in
/-- On every positive cover the actual real modulated Bernoulli equation has
a global small-data maximal-regularity solution decaying at every rate below
the proved cover gap. One local time and one linear data inverse serve every
rate and every requested common parabolic bound for its overlapping segments. -/
theorem bernoulli_cover_modulated_real_global_solution
    (ψ : circleH4Domain T)
    (hnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (M : ℕ) (hM : 0 < M) (hS : S = (M:ℝ)*T) :
    let Ext := circlePeriodicExtension T S M hS
    let Q := Ext q
    let P := Ext p
    let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
    let K := circleBernoulliBackground S Q P
    let B := circleSobolevCoordinate S 2 0+
      circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
    let gM : ℝ := if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)
    circleConjugate S (Ψ:CircleL2 S) = (Ψ:CircleL2 S) ∧
      inner ℂ (Ψ:CircleL2 S) (circleContinuousL2 S K.b) ≠ 0 ∧
      ∃ τ : ℝ, ∃ hτ : 0 < τ, τ ≤ 1 ∧
        ∃ e : CircleParabolicSpace S τ ≃L[ℂ]
            (CircleSobolevSpace S 2 × CircleTimeL2 S),
          e.toContinuousLinearMap = circleParabolicLowerOrderData S τ B ∧
          ∀ μ : ℝ, 0 < μ → μ < gM → ∃ C > 0,
            ∀ η : ℝ, 0 < η → ∃ ε > 0, ∃ r > 0, r < η ∧
              ∀ x₀ : CircleSobolevSpace S 2,
                circleSobolevConjugation S 2 x₀ = x₀ →
                inner ℂ (Ψ:CircleL2 S) (circleSobolevCoordinate S 2 0 x₀) = 0 → ‖x₀‖ ≤ ε →
                ∃ u : C(ℝ≥0,CircleSobolevSpace S 2), ∃ U : ℕ → CircleParabolicSpace S τ,
                  u 0 = x₀ ∧
                  (∀ n, ‖U n‖ ≤ r ∧ circleParabolicConjugation S τ (U n) = U n ∧
                    ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ (U n) t =
                      circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S)
                        (circleParabolicH4 S τ (U n) t)) ∧
                  (∀ n t, u (circleParabolicSegmentTime τ hτ n t) = circleParabolicCurve S τ (U n) t) ∧
                  (∀ t : ℝ≥0, 0 < t → ∃ (n : ℕ) (s : unitInterval),
                    (0:ℝ) < (s:ℝ) ∧ (s:ℝ) < 1 ∧ circleParabolicSegmentTime τ hτ n s = t) ∧
                  ∀ t : ℝ≥0, circleSobolevConjugation S 2 (u t) = u t ∧
                    inner ℂ (Ψ:CircleL2 S) (circleSobolevCoordinate S 2 0 (u t)) = 0 ∧
                    ‖u t‖ ≤ C*Real.exp (-μ*(t:ℝ))*‖x₀‖ := by
  dsimp only
  let Ext := circlePeriodicExtension T S M hS
  let Q := Ext q
  let P := Ext p
  let Ψ := circleCoverEmbeddingH4 T S M hM hS 0 ψ
  let K := circleBernoulliBackground S Q P
  let B := circleSobolevCoordinate S 2 0+
    circleSobolevLowerOrderOperator S (Q^2) ((2:ℂ) • (Q*P)) (1-(3:ℂ) • (Q^4))
  let V : CircleL2 S →L[ℂ] CircleL2 S :=
    (circleCoverStableMetric T S q p hq hp he hqreal hpreal hs hc ho hr
      M hM (ψ:CircleL2 T) hnorm).toContinuousLinearMap
  have hloc := bernoulli_cover_modulated_real_local_solution T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  have hdata := (paper_periodic_cover_modulated_tame_data T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS).2.2
  have henergy := bernoulli_cover_parabolic_energy_estimate T S q p hq hp he
    hqreal hpreal hs hc ho hr ψ hnorm hψzero M hM hS
  dsimp only at henergy
  have hE : ∀ x, 2*(P x)^2+(Q x)^4 = 1 :=
    fun x => he (circleCoverProjection T S M hS x)
  refine ⟨hloc.1,hloc.2.1,?_⟩
  refine uniform_global_witness_transport hloc.2.2 ?_
  intro τ hτ hτ₁ e heq hlocal
  have hlocal' := discard_local_uniqueness
    (H := CircleSobolevSpace S 2) (X := CircleParabolicSpace S τ) (fun x => ‖x‖)
    (fun r x U => ‖U‖ ≤ r ∧ circleParabolicInitialValue S τ U = x ∧
      ∀ᵐ t ∂volume, circleParabolicTimeDerivative S τ U t =
        circleNormalGraphModulatedFlow S K (15/2) (Ψ:CircleL2 S) (circleParabolicH4 S τ U t))
    (fun x U => circleSobolevConjugation S 2 x = x → circleParabolicConjugation S τ U = U) hlocal
  refine use_tame_radius_data hdata.2.2.2.2.2 ?_
  intro δ hδ C hC hTame
  exact bernoulli_global_of_data S K (Ψ:CircleL2 S) V
    (circleNormalGraphDerivative S K (15/2)) B
    (bernoulli_global_principal_split S Q P hE) δ C hδ hC.le hTame.2 τ hτ hlocal'
    (if M = 1 then 21/4 else 1/(2*(M:ℝ)^2)) henergy

end Profile
end Lemniscate

