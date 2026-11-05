import Lemniscate.PeriodicNormalGraphH2Entry
import Lemniscate.NormalGraphRotationPhase
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Lemniscate.FrenetComparison
import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.Real.Sqrt

/-! Curvature-profile closeness gives the actual real H2 graph in the adjoint
phase condition after a Euclidean motion. The C1 projection and small-angle
selection are internal to this initial-data theorem. -/
noncomputable section
namespace Lemniscate

open Complex Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate NNReal

private def phaseRotation (θ : ℝ) : ℂ := Complex.exp ((-θ:ℝ)*I)

private theorem phase_rotation_norm (θ : ℝ) : ‖phaseRotation θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (-θ)

private theorem phase_rotation_deriv (θ : ℝ) :
    HasDerivAt phaseRotation (-I*phaseRotation θ) θ := by
  have hd := (((hasDerivAt_id θ).neg).ofReal_comp.mul_const I).cexp
  apply hd.congr_deriv
  simp only [phaseRotation,id_eq,Pi.neg_apply,Complex.ofReal_neg,Complex.ofReal_one]
  ring

private theorem phase_rotation_lipschitz (a b : ℝ) :
    ‖phaseRotation a-phaseRotation b‖ ≤ |a-b| := by
  simpa only [Real.norm_eq_abs,one_mul] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := (Set.univ : Set ℝ)) (C := 1)
      (fun t _ => (phase_rotation_deriv t).hasDerivWithinAt)
      (fun t _ => by rw [norm_mul,norm_neg,Complex.norm_I,phase_rotation_norm,one_mul])
      convex_univ (mem_univ b) (mem_univ a)

private theorem phase_periodic_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (T : ℝ) (hp : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro s
  have heq : (fun u => f (u+T)) = f := funext hp
  simpa only [deriv_comp_add_const] using congrArg (fun F => deriv F s) heq

/-- The Hermitian pairing of two real circle functions is real. -/
theorem circle_inner_im_eq_zero_of_real (T : ℝ) [Fact (0<T)]
    (ψ v : CircleL2 T) (hψ : circleConjugate T ψ = ψ)
    (hv : circleConjugate T v = v) : (inner ℂ ψ v).im = 0 := by
  have heq : conj (inner ℂ ψ v) = inner ℂ ψ v := by
    rw [← circle_conjugate_inner,hψ,hv]
  have hi := congrArg Complex.im heq
  simp only [Complex.conj_im] at hi
  linarith

/-- Continuous pointwise velocities give the actual derivative in the
continuous-function space on a compact spatial domain. -/
theorem continuous_map_hasDerivAt_of_pointwise
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F G : ℝ → C(X,ℂ)) (a b : ℝ)
    (hG : ContinuousOn G (Ioo a b))
    (hd : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun r => F r x) (G t x) t)
    (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt F (G t) t := by
  have hint (r : ℝ) (hr : r ∈ Ioo a b) : IntervalIntegrable G volume t r :=
    (hG.mono (ordConnected_Ioo.uIcc_subset ht hr)).intervalIntegrable
  have hprimitive (r : ℝ) (hr : r ∈ Ioo a b) :
      F r-F t = ∫ v in t..r, G v := by
    apply ContinuousMap.ext
    intro x
    have heval : (∫ v in t..r, G v) x = ∫ v in t..r, G v x :=
      ((ContinuousMap.evalCLM ℂ x).intervalIntegral_comp_comm (hint r hr)).symm
    change F r x-F t x = (∫ v in t..r, G v) x
    rw [heval]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun v hv => hd v (ordConnected_Ioo.uIcc_subset ht hr hv) x)
      (((ContinuousMap.evalCLM ℂ x).continuous.comp_continuousOn
        (hG.mono (ordConnected_Ioo.uIcc_subset ht hr))).intervalIntegrable)).symm
  have heq : F =ᶠ[𝓝 t] fun r => F t+∫ v in t..r, G v := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    have hp := hprimitive r hr
    exact (sub_eq_iff_eq_add.mp hp).trans (add_comm _ _)
  have hI : HasDerivAt (fun r => ∫ v in t..r, G v) (G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hint t ht)
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hG t ht)
      (hG.continuousAt (isOpen_Ioo.mem_nhds ht))
  exact (hI.const_add (F t)).congr_of_eventuallyEq heq

private theorem phase_root_on_small_interval
    (φ d : ℝ → ℝ) (q r A : ℝ) (hq : q ≠ 0) (hr : 0<r) (hA : 0≤A)
    (hzero : |φ 0| ≤ A) (hsize : A ≤ |q|/2*r)
    (hd : ∀ t ∈ Ioo (-2*r) (2*r), HasDerivAt φ (d t) t)
    (hnear : ∀ t ∈ Ioo (-2*r) (2*r), |d t+q| ≤ |q|/2) :
    ∃ t ∈ Icc (-r) r, φ t = 0 := by
  have hmem (t : ℝ) (ht : t ∈ Icc (-r) r) : t ∈ Ioo (-2*r) (2*r) := by
    constructor <;> linarith [ht.1,ht.2]
  have hcont : ContinuousOn φ (Icc (-r) r) :=
    fun t ht => (hd t (hmem t ht)).continuousAt.continuousWithinAt
  let E : ℝ → ℝ := fun t => φ t+q*t
  have hE (t : ℝ) (ht : t ∈ Icc (-r) r) : HasDerivAt E (d t+q) t := by
    simpa only [E,id_eq,one_mul,mul_one,Pi.add_apply] using!
      (hd t (hmem t ht)).add ((hasDerivAt_id t).const_mul q)
  have herr (t : ℝ) (ht : t ∈ Icc (-r) r) :
      |φ t-φ 0+q*t| ≤ |q|/2*|t| := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := E) (f' := fun u => d u+q) (s := Icc (-r) r) (C := |q|/2)
      (fun u hu => (hE u hu).hasDerivWithinAt)
      (fun u hu => by simpa only [Real.norm_eq_abs] using hnear u (hmem u hu))
      (convex_Icc (-r) r) (show (0:ℝ) ∈ Icc (-r) r by constructor <;> linarith) ht
    simpa only [E,Real.norm_eq_abs,mul_zero,add_zero,sub_zero,
      show φ t+q*t-φ 0 = φ t-φ 0+q*t by ring] using hh
  have hleft := herr (-r) (by constructor <;> linarith)
  have hright := herr r (by constructor <;> linarith)
  rw [abs_neg,abs_of_pos hr] at hleft
  rw [abs_of_pos hr] at hright
  rcases lt_or_gt_of_ne hq with hqneg | hqpos
  · have hneg := abs_of_neg hqneg
    rw [hneg] at hleft hright hsize
    have hl : φ (-r) ≤ 0 := by
      nlinarith only [(abs_le.mp hleft).2,(abs_le.mp hzero).2,hsize]
    have hu : 0 ≤ φ r := by
      nlinarith only [(abs_le.mp hright).1,(abs_le.mp hzero).1,hsize]
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by linarith : -r≤r) hcont ⟨hl,hu⟩
    exact ⟨t,ht,he⟩
  · have hpos := abs_of_pos hqpos
    rw [hpos] at hleft hright hsize
    have hl : 0 ≤ φ (-r) := by
      nlinarith only [(abs_le.mp hleft).1,(abs_le.mp hzero).1,hsize]
    have hu : φ r ≤ 0 := by
      nlinarith only [(abs_le.mp hright).2,(abs_le.mp hzero).2,hsize]
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' (by linarith : -r≤r) hcont ⟨hu,hl⟩
    exact ⟨t,ht,he⟩

private structure PhaseProjection (T : ℝ) [Fact (0<T)]
    (γ β Tβ : ℝ → ℂ) (K e L : ℝ) where
  χ : ℝ → ℝ
  h : ℝ → ℝ
  hsmooth : ContDiff ℝ ∞ h
  hper : Function.Periodic h T
  χsmooth : ContDiff ℝ ∞ χ
  χper : Function.Periodic (fun s => χ s-s) T
  graph : ∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s
  shift : ∀ s, |χ s-s| ≤ 2*e
  height : ∀ s, |h s| ≤ 3*e
  dh : ∀ s, |deriv h s| ≤ 4*(e+2*K*e)
  lower : ∀ s, (1/4:ℝ) ≤ deriv χ s
  upper : ∀ s, deriv χ s ≤ 4
  H : CircleSobolevSpace T 2
  real : circleSobolevConjugation T 2 H = H
  value : circleSobolevCoordinate T 2 0 H = circleContinuousL2 T
    (periodicCircleFunction T (fun s => (h s:ℂ))
      (fun s => congrArg Complex.ofReal (hper s))
      (Complex.continuous_ofReal.comp hsmooth.continuous))
  bound : ‖H‖ ≤ L

private def PhaseProjection.heightCircle {T : ℝ} [Fact (0<T)]
    {γ β Tβ : ℝ → ℂ} {K e L : ℝ} (p : PhaseProjection T γ β Tβ K e L) :
    C(AddCircle T,ℂ) :=
  periodicCircleFunction T (fun s => (p.h s:ℂ))
    (fun s => congrArg Complex.ofReal (p.hper s))
    (Complex.continuous_ofReal.comp p.hsmooth.continuous)

private theorem phase_graph_ratio
    (γ β Tγ Tβ : ℝ → ℂ) (k χ h : ℝ → ℝ)
    (hγ : ∀ s, HasDerivAt γ (Tγ s) s) (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (huβ : ∀ s, ‖Tβ s‖ = 1) (hχ : ContDiff ℝ ∞ χ) (hh : ContDiff ℝ ∞ h)
    (hgraph : ∀ s, γ (χ s) = β s+I*(h s:ℂ)*Tβ s)
    (s : ℝ) (hg : 0<deriv χ s) :
    let W := conj (Tβ s)*Tγ (χ s)
    deriv h s/(1-k s*h s) = W.im/W.re := by
  let g := deriv χ s
  let A := 1-k s*h s
  let W := conj (Tβ s)*Tγ (χ s)
  have hself : conj (Tβ s)*Tβ s = 1 := by rw [Complex.conj_mul',huβ s]; norm_num
  have hχd : HasDerivAt χ g s := ((hχ.differentiable (by simp)) s).hasDerivAt
  have hhd : HasDerivAt h (deriv h s) s := ((hh.differentiable (by simp)) s).hasDerivAt
  have hl : HasDerivAt (γ ∘ χ) ((g:ℂ)*Tγ (χ s)) s := by
    simpa only [real_smul] using! (hγ (χ s)).scomp s hχd
  have hr := (hβ s).add ((hhd.ofReal_comp.const_mul I).mul (hTβ s))
  have heq : γ ∘ χ = fun u => β u+I*(h u:ℂ)*Tβ u := funext hgraph
  rw [heq] at hl
  have hc := congrArg (fun z : ℂ => conj (Tβ s)*z) (hl.unique hr)
  have hframe : (g:ℂ)*W = (A:ℂ)+I*((deriv h s:ℝ):ℂ) := by
    dsimp only [W,A]
    push_cast
    calc
      _ = conj (Tβ s)*((g:ℂ)*Tγ (χ s)) := by ring
      _ = conj (Tβ s)*(Tβ s+(I*((deriv h s:ℝ):ℂ)*Tβ s+
          I*(h s:ℂ)*(I*(k s:ℂ)*Tβ s))) := hc
      _ = (1-(k s:ℂ)*(h s:ℂ)+I*((deriv h s:ℝ):ℂ))*(conj (Tβ s)*Tβ s) := by
        ring_nf
        rw [Complex.I_sq]
        ring
      _ = _ := by rw [hself,mul_one]
  have hA : A = g*W.re := by
    have hc := congrArg Complex.re hframe
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero] using hc.symm
  have hB : deriv h s = g*W.im := by
    have hc := congrArg Complex.im hframe
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,add_zero,zero_add] using hc.symm
  change deriv h s/A = W.im/W.re
  rw [hA,hB,mul_div_mul_left _ _ (ne_of_gt hg)]

private theorem phase_family_root
    (T : ℝ) [Fact (0<T)] (γ β Tγ Tβ : ℝ → ℂ) (k : ℝ → ℝ)
    (hγsmooth : ContDiff ℝ ∞ γ) (hβsmooth : ContDiff ℝ ∞ β)
    (hγ : ∀ s, HasDerivAt γ (Tγ s) s) (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (huγ : ∀ s, ‖Tγ s‖=1) (huβ : ∀ s, ‖Tβ s‖=1)
    (hγper : Function.Periodic γ T) (hβper : Function.Periodic β T)
    (K R ε r δ : ℝ) (hK : 0≤K) (hR : 1≤R) (hε : 0<ε) (hε₁ : ε≤1)
    (hr : 0<r) (hδ : 0≤δ) (hk : ∀ s, |k s|≤K)
    (hsmall : ε+K*(4*ε)≤1/2) (hγbound : ∀ s, ‖γ s‖≤R) (hβbound : ∀ s, ‖β s‖≤R)
    (htangent : ∀ θ ∈ Ioo (-2*r) (2*r), ∀ s,
      ‖phaseRotation θ*Tγ s-Tβ s‖≤ε)
    (e L : ℝ → ℝ) (he : ∀ θ ∈ Ioo (-2*r) (2*r), e θ≤ε) (he₀ : e 0=δ)
    (p : (θ : Ioo (-2*r) (2*r)) →
      PhaseProjection T (fun s => phaseRotation θ*γ s) β Tβ K (e θ) (L θ))
    (b : C(AddCircle T,ℂ))
    (hb : ∀ s : ℝ, b (s:AddCircle T)=((conj (Tβ s)*β s).re:ℂ))
    (ψ : CircleL2 T) (hψ : circleConjugate T ψ=ψ)
    (q : ℝ) (hq : q≠0) (hpair : inner ℂ ψ (circleContinuousL2 T b)=(q:ℂ))
    (hsize : 3*‖ψ‖*δ≤|q|/2*r)
    (hnear : ‖ψ‖*(2*(R+3)*(1+2*K)*ε)≤|q|/2) :
    ∃ θ : Ioo (-2*r) (2*r), |(θ:ℝ)|≤r ∧
      inner ℂ ψ (circleSobolevCoordinate T 2 0 (p θ).H)=0 := by
  have hR0 : 0≤R := le_trans (by norm_num : (0:ℝ)≤1) hR
  let D := Ioo (-2*r) (2*r)
  have hzero : (0:ℝ)∈D := by constructor <;> linarith
  let χ : ℝ → ℝ → ℝ := fun θ s => if ht : θ∈D then (p ⟨θ,ht⟩).χ s else s
  let h : ℝ → ℝ → ℝ := fun θ s => if ht : θ∈D then (p ⟨θ,ht⟩).h s else 0
  let Q : ℝ → C(AddCircle T,ℂ) := fun θ => if ht : θ∈D then (p ⟨θ,ht⟩).heightCircle else 0
  have hχsm (θ : ℝ) (ht : θ∈D) : ContDiff ℝ ∞ (χ θ) := by
    simpa only [χ,dif_pos ht] using (p ⟨θ,ht⟩).χsmooth
  have hhsm (θ : ℝ) (ht : θ∈D) : ContDiff ℝ ∞ (h θ) := by
    simpa only [h,dif_pos ht] using (p ⟨θ,ht⟩).hsmooth
  have hgph (θ : ℝ) (ht : θ∈D) (s : ℝ) :
      phaseRotation θ*γ (χ θ s)=β s+I*(h θ s:ℂ)*Tβ s := by
    simpa only [χ,h,dif_pos ht] using (p ⟨θ,ht⟩).graph s
  have hχshift (θ : ℝ) (ht : θ∈D) (s : ℝ) : |χ θ s-s|≤2*ε := by
    simpa only [χ,dif_pos ht] using ((p ⟨θ,ht⟩).shift s).trans
      (mul_le_mul_of_nonneg_left (he θ ht) (by norm_num))
  have hχlow (θ : ℝ) (ht : θ∈D) (s : ℝ) : (1/4:ℝ)≤deriv (χ θ) s := by
    simpa only [χ,dif_pos ht] using (p ⟨θ,ht⟩).lower s
  have hχup (θ : ℝ) (ht : θ∈D) (s : ℝ) : deriv (χ θ) s≤4 := by
    simpa only [χ,dif_pos ht] using (p ⟨θ,ht⟩).upper s
  have hself (s : ℝ) : conj (Tβ s)*Tβ s=1 := by rw [Complex.conj_mul',huβ s]; norm_num
  have hroots (θ : ℝ) (ht : θ∈D) (s : ℝ) :
      (conj (Tβ s)*(phaseRotation θ*γ (χ θ s)-β s)).re=0 := by
    rw [hgph θ ht s,add_sub_cancel_left]
    have heq : conj (Tβ s)*(I*(h θ s:ℂ)*Tβ s)=I*(h θ s:ℂ) := by
      calc
        _ = I*(h θ s:ℂ)*(conj (Tβ s)*Tβ s) := by ring
        _ = _ := by rw [hself,mul_one]
    rw [heq]
    simp
  have hχlipθ (θ η : D) (s : ℝ) : |χ θ s-χ η s|≤2*R*|(θ:ℝ)-η| := by
    have hc := normal_projection_height_comparison
      (fun u => phaseRotation θ*γ u) (fun u => phaseRotation η*γ u) β
      (fun u => phaseRotation θ*Tγ u) Tβ k
      (fun u => (hγ u).const_mul (phaseRotation θ)) hTβ
      (fun u => by rw [norm_mul,phase_rotation_norm,huγ u,one_mul]) huβ
      K ε (4*ε) hK hk (htangent θ θ.property) hsmall s (χ θ s) (χ η s)
      ((hχshift θ θ.property s).trans (by linarith))
      ((hχshift η η.property s).trans (by linarith))
      (hroots θ θ.property s) (hroots η η.property s)
    have hb : ‖phaseRotation θ*γ (χ η s)-phaseRotation η*γ (χ η s)‖≤R*|(θ:ℝ)-η| := by
      rw [← sub_mul,norm_mul]
      exact (mul_le_mul (phase_rotation_lipschitz θ η) (hγbound _)
        (norm_nonneg _) (abs_nonneg _)).trans_eq (by ring)
    exact hc.1.trans ((mul_le_mul_of_nonneg_left hb (by norm_num)).trans_eq (by ring))
  have hχlips (θ : D) (s t : ℝ) : |χ θ s-χ θ t|≤4*|s-t| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := 4)
        (fun u _ => ((hχsm θ θ.property).differentiable (by simp) u).hasDerivAt.hasDerivWithinAt)
        (fun u _ => by rw [Real.norm_eq_abs,abs_of_nonneg (by linarith [hχlow θ θ.property u])]; exact hχup θ θ.property u)
        convex_univ (mem_univ t) (mem_univ s)
  have hχjoint : Continuous (fun z : D × ℝ => χ z.1 z.2) := by
    let c : ℝ≥0 := ⟨4+2*R,by positivity⟩
    apply LipschitzWith.continuous (K := c)
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have ht : |(z.1:ℝ)-w.1|≤dist z w := by
      simpa only [Prod.dist_eq,Subtype.dist_eq,Real.dist_eq] using
        (le_max_left (dist z.1 w.1) (dist z.2 w.2))
    have hs : |z.2-w.2|≤dist z w := by
      simpa only [Prod.dist_eq,Subtype.dist_eq,Real.dist_eq] using
        (le_max_right (dist z.1 w.1) (dist z.2 w.2))
    have htriangle : |χ z.1 z.2-χ w.1 w.2|≤
        |χ z.1 z.2-χ z.1 w.2|+|χ z.1 w.2-χ w.1 w.2| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le_norm_sub_add_norm_sub
        (χ z.1 z.2) (χ z.1 w.2) (χ w.1 w.2)
    have hb := htriangle.trans
      (add_le_add (hχlips z.1 z.2 w.2) (hχlipθ z.1 w.1 w.2))
    rw [Real.dist_eq]
    change |χ z.1 z.2-χ w.1 w.2|≤(4+2*R)*dist z w
    exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤4),
      mul_le_mul_of_nonneg_left ht (by positivity : (0:ℝ)≤2*R)])
  have hTγcont : Continuous Tγ := by
    have heq : deriv γ=Tγ := funext fun s => (hγ s).deriv
    rw [← heq]
    exact (contDiff_infty_iff_deriv.mp hγsmooth).2.continuous
  have hTβcont : Continuous Tβ := by
    have heq : deriv β=Tβ := funext fun s => (hβ s).deriv
    rw [← heq]
    exact (contDiff_infty_iff_deriv.mp hβsmooth).2.continuous
  have hRcont : Continuous phaseRotation :=
    continuous_iff_continuousAt.mpr fun t => (phase_rotation_deriv t).continuousAt
  let W : ℝ → ℝ → ℂ := fun θ s => conj (Tβ s)*(phaseRotation θ*Tγ (χ θ s))
  let Z : ℝ → ℂ := fun s => conj (Tβ s)*β s
  have hWjoint : Continuous (fun z : D × ℝ => W z.1 z.2) := by
    exact (Complex.continuous_conj.comp (hTβcont.comp continuous_snd)).mul
      ((hRcont.comp (continuous_subtype_val.comp continuous_fst)).mul (hTγcont.comp hχjoint))
  have hZcont : Continuous Z := (Complex.continuous_conj.comp hTβcont).mul hβsmooth.continuous
  have hHjoint : Continuous (fun z : D × ℝ => h z.1 z.2) := by
    have heq : (fun z : D × ℝ => h z.1 z.2) = fun z =>
        (conj (Tβ z.2)*(phaseRotation z.1*γ (χ z.1 z.2)-β z.2)).im := by
      funext z
      rw [hgph z.1 z.1.property z.2,add_sub_cancel_left]
      have hu := hself z.2
      have hc : conj (Tβ z.2)*(I*(h z.1 z.2:ℂ)*Tβ z.2)=I*(h z.1 z.2:ℂ) := by
        calc
          _ = I*(h z.1 z.2:ℂ)*(conj (Tβ z.2)*Tβ z.2) := by ring
          _ = _ := by rw [hu,mul_one]
      rw [hc]
      simp
    rw [heq]
    exact Complex.continuous_im.comp
      ((Complex.continuous_conj.comp (hTβcont.comp continuous_snd)).mul
        (((hRcont.comp (continuous_subtype_val.comp continuous_fst)).mul
          (hγsmooth.continuous.comp hχjoint)).sub (hβsmooth.continuous.comp continuous_snd)))
  have hTβper : Function.Periodic Tβ T := by
    have hd : deriv β=Tβ := funext fun s => (hβ s).deriv
    rw [← hd]
    exact phase_periodic_deriv β T hβper
  have hTγper : Function.Periodic Tγ T := by
    have hd : deriv γ=Tγ := funext fun s => (hγ s).deriv
    rw [← hd]
    exact phase_periodic_deriv γ T hγper
  have hTlip (s t : ℝ) : ‖Tβ t-Tβ s‖≤K*|t-s| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := (Set.univ : Set ℝ)) (C := K)
        (fun u _ => (hTβ u).hasDerivWithinAt)
        (fun u _ => by simpa only [norm_mul,Complex.norm_I,Complex.norm_real,
          Real.norm_eq_abs,huβ u,one_mul,mul_one] using hk u)
        convex_univ (mem_univ s) (mem_univ t)
  have hWdist (θ : ℝ) (ht : θ∈D) (s : ℝ) : ‖W θ s-1‖≤(1+2*K)*ε := by
    have heq : W θ s-1=conj (Tβ s)*(phaseRotation θ*Tγ (χ θ s)-Tβ s) := by
      dsimp only [W]
      rw [mul_sub,hself]
    rw [heq,norm_mul,Complex.norm_conj,huβ s,one_mul]
    calc
      _ ≤ ‖phaseRotation θ*Tγ (χ θ s)-Tβ (χ θ s)‖+‖Tβ (χ θ s)-Tβ s‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε+K*|χ θ s-s| := add_le_add (htangent θ ht _) (hTlip s _)
      _ ≤ ε+K*(2*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left (hχshift θ ht s) hK)
      _ = _ := by ring
  have hWre (θ : ℝ) (ht : θ∈D) (s : ℝ) : 1/2≤(W θ s).re := by
    have hh := (Complex.abs_re_le_norm (W θ s-1)).trans (hWdist θ ht s)
    simp only [Complex.sub_re,Complex.one_re] at hh
    nlinarith only [(abs_le.mp hh).1,hsmall,mul_nonneg hK hε.le]
  have hWim (θ : ℝ) (ht : θ∈D) (s : ℝ) : |(W θ s).im|≤(1+2*K)*ε := by
    simpa only [Complex.sub_im,Complex.one_im,sub_zero] using
      (Complex.abs_im_le_norm (W θ s-1)).trans (hWdist θ ht s)
  let J : ℝ → ℝ → ℝ := fun θ s => (Z s).re+((Z s).im+h θ s)*(W θ s).im/(W θ s).re
  have hJjoint : Continuous (fun z : D × ℝ => J z.1 z.2) := by
    exact (Complex.continuous_re.comp (hZcont.comp continuous_snd)).add
      ((((Complex.continuous_im.comp (hZcont.comp continuous_snd)).add hHjoint).mul
        (Complex.continuous_im.comp hWjoint)).div
        (Complex.continuous_re.comp hWjoint)
        (fun z => ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hWre z.1 z.1.property z.2))))
  have hχperiod (θ : D) (s : ℝ) : χ θ (s+T)=χ θ s+T := by
    have hp := (p θ).χper s
    change (p θ).χ (s+T)-(s+T)=(p θ).χ s-s at hp
    change (if ht : (θ:ℝ)∈D then (p ⟨θ,ht⟩).χ (s+T) else s+T)=
      (if ht : (θ:ℝ)∈D then (p ⟨θ,ht⟩).χ s else s)+T
    simp only [dif_pos θ.property]
    linarith
  have hJper (θ : D) : Function.Periodic (J θ) T := by
    intro s
    dsimp only [J,W,Z]
    rw [hχperiod θ s,hTγper,hTβper,hβper]
    have hp : h θ (s+T)=h θ s := by
      simpa only [h,dif_pos θ.property] using (p θ).hper s
    rw [hp]
  let G : ℝ → C(AddCircle T,ℂ) := fun θ => if ht : θ∈D then
    periodicCircleFunction T (fun s => (J θ s:ℂ))
      (fun s => congrArg Complex.ofReal (hJper ⟨θ,ht⟩ s))
      (Complex.continuous_ofReal.comp (hJjoint.curry_right (x := (⟨θ,ht⟩ : D)))) else 0
  have hGeval (θ : ℝ) (ht : θ∈D) (s : ℝ) : G θ (s:AddCircle T)=(J θ s:ℂ) := by
    dsimp only [G]
    rw [dif_pos ht]
    rfl
  have hQeval (θ s : ℝ) : Q θ (s:AddCircle T)=(h θ s:ℂ) := by
    by_cases ht : θ∈D
    · dsimp only [Q,h]
      simp only [dif_pos ht]
      rfl
    · simp only [Q,h,dif_neg ht,ContinuousMap.zero_apply,Complex.ofReal_zero]
  have hGcont : ContinuousOn G D := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hmap : IsOpenQuotientMap (fun z : D × ℝ => (z.1,(z.2:AddCircle T))) :=
      IsOpenQuotientMap.id.prodMap (QuotientAddGroup.isOpenQuotientMap_mk
        (N := AddSubgroup.zmultiples T))
    apply hmap.continuous_comp_iff.mp
    have heq : (fun z : D × ℝ => G z.1 (z.2:AddCircle T))=
        fun z => (J z.1 z.2:ℂ) := by
      funext z
      exact hGeval z.1 z.1.property z.2
    change Continuous (fun z : D × ℝ => G z.1 (z.2:AddCircle T))
    rw [heq]
    exact Complex.continuous_ofReal.comp hJjoint
  have hpoint := normal_graph_rotation_phase_derivative γ β Tγ Tβ k hγsmooth
    hγ hβ hTβ huγ huβ K ε hK hε hk hsmall (-2*r) (2*r) χ h
    htangent hχsm hhsm hgph hχshift hχlow
  have hratio (θ : ℝ) (ht : θ∈D) (s : ℝ) :
      deriv (h θ) s/(1-k s*h θ s)=(W θ s).im/(W θ s).re :=
    phase_graph_ratio (fun u => phaseRotation θ*γ u) β
      (fun u => phaseRotation θ*Tγ u) Tβ k (χ θ) (h θ)
      (fun u => (hγ u).const_mul (phaseRotation θ)) hβ hTβ huβ
      (hχsm θ ht) (hhsm θ ht) (hgph θ ht) s
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (hχlow θ ht s))
  have hQpoint (θ : ℝ) (ht : θ∈D) (x : AddCircle T) :
      HasDerivAt (fun t => Q t x) (-G θ x) θ := by
    induction x using QuotientAddGroup.induction_on
    rename_i s
    have heq : (fun t => Q t (s:AddCircle T))=fun t => (h t s:ℂ) := by
      funext t
      exact hQeval t s
    rw [heq]
    have hd := (hpoint θ ht s).2
    have hj : -((Z s).re+((Z s).im+h θ s)*deriv (h θ) s/(1-k s*h θ s)) = -J θ s := by
      dsimp only [J]
      rw [mul_div_assoc,hratio θ ht s]
      ring
    rw [hj] at hd
    rw [hGeval θ ht s]
    simpa only [Complex.ofReal_neg] using! hd.ofReal_comp
  have hQd (θ : ℝ) (ht : θ∈D) : HasDerivAt Q (-G θ) θ :=
    continuous_map_hasDerivAt_of_pointwise Q (fun t => -G t) (-2*r) (2*r) hGcont.neg hQpoint θ ht
  have hGbound (θ : ℝ) (ht : θ∈D) : ‖G θ-b‖≤2*(R+3)*(1+2*K)*ε := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [ContinuousMap.sub_apply,hGeval θ ht s,hb s,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    change |J θ s-(Z s).re|≤2*(R+3)*(1+2*K)*ε
    have hhs : |h θ s|≤3*ε := by
      simpa only [h,dif_pos ht] using ((p ⟨θ,ht⟩).height s).trans
        (mul_le_mul_of_nonneg_left (he θ ht) (by norm_num))
    have hZ : |(Z s).im|≤R := (Complex.abs_im_le_norm _).trans
      (by dsimp only [Z]; rw [norm_mul,Complex.norm_conj,huβ s,one_mul]; exact hβbound s)
    have hnum : |(Z s).im+h θ s|≤R+3 := by
      have hh := (abs_add_le _ _).trans (add_le_add hZ hhs)
      exact hh.trans (by linarith)
    have hden : 0<(W θ s).re := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hWre θ ht s)
    dsimp only [J]
    rw [add_sub_cancel_left,abs_div,abs_mul,abs_of_pos hden]
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul hnum (hWim θ ht s) (abs_nonneg _) (by positivity : (0:ℝ)≤R+3)
    have hscale := mul_le_mul_of_nonneg_left (hWre θ ht s)
      (by positivity : (0:ℝ)≤2*(R+3)*(1+2*K)*ε)
    nlinarith only [hm,hscale]
  let E : C(AddCircle T,ℂ) →L[ℂ] CircleL2 T := ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  have hE : ‖E‖≤1 := by
    simpa [E,measureUnivNNReal] using
      (ContinuousMap.toLp_norm_le (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ))
  let φ : ℝ → ℝ := fun t => (inner ℂ ψ (E (Q t))).re
  let d : ℝ → ℝ := fun t => -(inner ℂ ψ (E (G t))).re
  have hφ (θ : ℝ) (ht : θ∈D) : HasDerivAt φ (d θ) θ := by
    have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ
      (((innerSL ℂ ψ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ
        ((E.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt θ (hQd θ ht)))
    simpa only [φ,d,Function.comp_def,ContinuousLinearMap.coe_restrictScalars',
      innerSL_apply_apply,Complex.reCLM_apply,map_neg,inner_neg_right,Complex.neg_re] using! hd
  have hφnear (θ : ℝ) (ht : θ∈D) : |d θ+q|≤|q|/2 := by
    have hqreal : (inner ℂ ψ (E b)).re=q := by
      simpa only [E,circleContinuousL2,Complex.ofReal_re] using congrArg Complex.re hpair
    have heq : d θ+q=-(inner ℂ ψ (E (G θ-b))).re := by
      simp only [d,map_sub,inner_sub_right,Complex.sub_re,hqreal]
      ring
    rw [heq,abs_neg]
    have hv := E.le_of_opNorm_le hE (G θ-b)
    calc
      _ ≤ ‖inner ℂ ψ (E (G θ-b))‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ψ‖*‖E (G θ-b)‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖*(2*(R+3)*(1+2*K)*ε) := mul_le_mul_of_nonneg_left
        (hv.trans (by simpa only [one_mul] using hGbound θ ht)) (norm_nonneg _)
      _ ≤ _ := hnear
  have hQzero : ‖Q 0‖≤3*δ := by
    apply (ContinuousMap.norm_le _ (by positivity)).mpr
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hQeval]
    simp only [h,dif_pos hzero,Complex.norm_real,Real.norm_eq_abs]
    simpa only [he₀] using (p ⟨0,hzero⟩).height s
  have hφzero : |φ 0|≤3*‖ψ‖*δ := by
    calc
      _ ≤ ‖inner ℂ ψ (E (Q 0))‖ := Complex.abs_re_le_norm _
      _ ≤ ‖ψ‖*‖E (Q 0)‖ := norm_inner_le_norm _ _
      _ ≤ ‖ψ‖*(3*δ) := mul_le_mul_of_nonneg_left
        ((E.le_of_opNorm_le hE _).trans (by simpa only [one_mul] using hQzero)) (norm_nonneg _)
      _ = _ := by ring
  obtain ⟨θ,hθ,hφzero⟩ := phase_root_on_small_interval φ d q r (3*‖ψ‖*δ) hq hr
    (by positivity) hφzero hsize hφ hφnear
  have hθD : θ∈D := by constructor <;> linarith [hθ.1,hθ.2]
  refine ⟨⟨θ,hθD⟩,(abs_le.mpr hθ),?_⟩
  have hv : circleConjugate T (circleSobolevCoordinate T 2 0 (p ⟨θ,hθD⟩).H)=
      circleSobolevCoordinate T 2 0 (p ⟨θ,hθD⟩).H := by
    rw [← circle_sobolev_conjugation_coordinate,(p ⟨θ,hθD⟩).real]
  apply Complex.ext
  · have hvQ : E (Q θ)=circleSobolevCoordinate T 2 0 (p ⟨θ,hθD⟩).H := by
      dsimp only [Q]
      rw [dif_pos hθD]
      exact (p ⟨θ,hθD⟩).value.symm
    change (inner ℂ ψ (circleSobolevCoordinate T 2 0 (p ⟨θ,hθD⟩).H)).re=0
    rw [← hvQ]
    exact hφzero
  · exact circle_inner_im_eq_zero_of_real T ψ _ hψ hv

/-- A sufficiently C1-close periodic unit-speed curve can be rotated by
an angle of the same order as its C1 error so that its actual real H2
normal height satisfies the prescribed real L2 phase condition. -/
private theorem periodic_normal_graph_phase_exists
    (T : ℝ) [Fact (0<T)] (β Tβ : ℝ → ℂ) (k ks : ℝ → ℝ)
    (hβsmooth : ContDiff ℝ ∞ β) (hβper : Function.Periodic β T)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s) (huβ : ∀ s, ‖Tβ s‖=1)
    (K K₁ : ℝ) (hK : 0≤K) (hK₁ : 0≤K₁)
    (hcurvature : ∀ s, |k s|≤K) (hcurvatureDerivative : ∀ s, |ks s|≤K₁)
    (b : C(AddCircle T,ℂ))
    (hb : ∀ s : ℝ, b (s:AddCircle T)=((conj (Tβ s)*β s).re:ℂ))
    (ψ : CircleL2 T) (hψ : circleConjugate T ψ=ψ)
    (hpair : inner ℂ ψ (circleContinuousL2 T b)≠0) :
    ∃ δ₀>0, ∃ C>0, ∀ (γ Tγ : ℝ → ℂ) (kγ : ℝ → ℝ) (δ : ℝ),
      ContDiff ℝ ∞ γ → Function.Periodic γ T →
      (∀ s, HasDerivAt γ (Tγ s) s) →
      (∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s) →
      (∀ s, ‖Tγ s‖=1) → Continuous kγ → Function.Periodic kγ T →
      0≤δ → δ<δ₀ → (∀ s, ‖γ s-β s‖≤δ) → (∀ s, ‖Tγ s-Tβ s‖≤δ) →
      ∃ θ : ℝ, ∃ χ h : ℝ → ℝ, ∃ hh : ContDiff ℝ ∞ h, ∃ hp : Function.Periodic h T,
        |θ|≤C*δ ∧ ContDiff ℝ ∞ χ ∧ Function.Periodic (fun s => χ s-s) T ∧
        (∀ s, Complex.exp ((-θ:ℝ)*I)*γ (χ s)=β s+I*(h s:ℂ)*Tβ s ∧
          |χ s-s|≤C*δ ∧ (1/4:ℝ)≤deriv χ s ∧ deriv χ s≤4) ∧
        ∃ H : CircleSobolevSpace T 2,
          circleSobolevConjugation T 2 H=H ∧
          circleSobolevCoordinate T 2 0 H=circleContinuousL2 T
            (periodicCircleFunction T (fun s => (h s:ℂ))
              (fun s => congrArg Complex.ofReal (hp s))
              (Complex.continuous_ofReal.comp hh.continuous)) ∧
          inner ℂ ψ (circleSobolevCoordinate T 2 0 H)=0 ∧
          ‖H‖≤C*(δ+Real.sqrt (T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2))) := by
  have hbconj : circleConjugate T (circleContinuousL2 T b)=circleContinuousL2 T b := by
    apply circle_conjugate_continuous_real T b
    intro x
    induction x using QuotientAddGroup.induction_on
    rename_i s
    rw [hb]
    exact Complex.conj_ofReal _
  let q : ℝ := (inner ℂ ψ (circleContinuousL2 T b)).re
  have hqpair : inner ℂ ψ (circleContinuousL2 T b)=(q:ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using circle_inner_im_eq_zero_of_real T ψ _ hψ hbconj
  have hq : q≠0 := by intro hz; apply hpair; rw [hqpair,hz,Complex.ofReal_zero]
  have hqabs : 0 < |q| := abs_pos.mpr hq
  obtain ⟨d₀,hd₀,C₀,hC₀,hentry⟩ := periodic_normal_graph_h2_entry T β Tβ k ks
    hβsmooth hβper hβ hTβ hk huβ K K₁ hK hK₁ hcurvature hcurvatureDerivative
  let βc := periodicCircleFunction T β hβper hβsmooth.continuous
  let R : ℝ := ‖βc‖+2
  have hR : 1≤R := by dsimp only [R]; linarith only [norm_nonneg βc]
  have hβbound (s : ℝ) : ‖β s‖≤R :=
    (βc.norm_coe_le_norm (s:AddCircle T)).trans (by dsimp only [R]; linarith)
  let J : ℝ := 1+12*(‖ψ‖+1)/|q|
  have hJ : 0<J := by dsimp only [J]; positivity
  have hJsize : 3*‖ψ‖≤|q|/2*J := by
    have heq : |q|/2*J=|q|/2+6*(‖ψ‖+1) := by
      dsimp only [J]
      field_simp [ne_of_gt hqabs]
      ring
    rw [heq]
    linarith [norm_nonneg ψ]
  let E : ℝ := 1+2*R*J
  let V : ℝ := 1+R*J
  let N : ℝ := 2*(R+3)*(1+2*K)
  have hE : 0<E := by dsimp only [E]; positivity
  have hV : 0<V := by dsimp only [V]; positivity
  have hN : 0≤N := by dsimp only [N]; positivity
  let δ₀ := min (1:ℝ) (min (d₀/E)
    (min ((1/4)/(E*(1+4*K))) ((|q|/2)/(‖ψ‖*N*E+1))))
  have hδ₀ : 0<δ₀ := by dsimp only [δ₀]; positivity
  let C : ℝ := 1+J+4*V+C₀*(V+1)
  have hC : 0<C := by dsimp only [C]; positivity
  have hCJ : J≤C := by
    dsimp only [C]
    nlinarith only [hV.le,mul_nonneg hC₀.le (by linarith only [hV.le] : (0:ℝ)≤V+1)]
  have hCV : 2*V≤C := by dsimp only [C]; nlinarith only [hJ.le,hV.le,mul_nonneg hC₀.le (by positivity : (0:ℝ)≤V+1)]
  have hCCV : C₀*V≤C := by dsimp only [C]; nlinarith only [hJ.le,hV.le,hC₀.le]
  have hCC : C₀≤C := by dsimp only [C]; nlinarith only [hJ.le,hV.le,mul_nonneg hC₀.le hV.le]
  refine ⟨δ₀,hδ₀,C,hC,?_⟩
  intro γ Tγ kγ δ hγsmooth hγper hγ hTγ huγ hkγ hkγper hδ hδlt hposition htangent
  let Zerr := Real.sqrt (T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2))
  have hZerr : 0≤Zerr := Real.sqrt_nonneg _
  have hδ₁ : δ≤1 := (hδlt.trans_le (min_le_left _ _)).le
  have hεδ : E*δ<d₀ := by
    have hlt : δ<d₀/E := hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hm := (lt_div_iff₀ hE).mp hlt
    nlinarith only [hm]
  have hεsmall : E*δ+K*(4*(E*δ))≤1/2 := by
    have hlt : δ<(1/4)/(E*(1+4*K)) := hδlt.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hm := (lt_div_iff₀ (by positivity : (0:ℝ)<E*(1+4*K))).mp hlt
    nlinarith only [hm]
  have hε₁ : E*δ≤1 := by
    have hp := mul_nonneg hK (mul_nonneg (by norm_num : (0:ℝ)≤4) (mul_nonneg hE.le hδ))
    nlinarith only [hεsmall,hp]
  have hnear : ‖ψ‖*(N*(E*δ))≤|q|/2 := by
    have hlt : δ<(|q|/2)/(‖ψ‖*N*E+1) := hδlt.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hm := (lt_div_iff₀ (by positivity : (0:ℝ)<‖ψ‖*N*E+1)).mp hlt
    nlinarith only [hm,hδ]
  have hγbound (s : ℝ) : ‖γ s‖≤R := by
    have hs := (norm_le_norm_sub_add (γ s) (β s)).trans
      (add_le_add (hposition s) (βc.norm_coe_le_norm (s:AddCircle T)))
    dsimp only [R]
    linarith
  have hangle_error (θ : ℝ) (s : ℝ) :
      ‖phaseRotation θ*γ s-β s‖≤δ+R*|θ| ∧
      ‖phaseRotation θ*Tγ s-Tβ s‖≤δ+R*|θ| := by
    have hr0 : phaseRotation 0=1 := by simp [phaseRotation]
    have hr : ‖phaseRotation θ-1‖≤|θ| := by simpa only [hr0,sub_zero] using phase_rotation_lipschitz θ 0
    constructor
    · calc
        _ = ‖(phaseRotation θ-1)*γ s+(γ s-β s)‖ := by congr 1; ring
        _ ≤ ‖(phaseRotation θ-1)*γ s‖+‖γ s-β s‖ := norm_add_le _ _
        _ ≤ |θ| * R+δ := add_le_add
          (by rw [norm_mul]; exact mul_le_mul hr (hγbound s) (norm_nonneg _) (abs_nonneg _))
          (hposition s)
        _ = _ := by ring
    · calc
        _ = ‖(phaseRotation θ-1)*Tγ s+(Tγ s-Tβ s)‖ := by congr 1; ring
        _ ≤ ‖(phaseRotation θ-1)*Tγ s‖+‖Tγ s-Tβ s‖ := norm_add_le _ _
        _ ≤ |θ|+δ := add_le_add
          (by rw [norm_mul,huγ s,mul_one]; exact hr) (htangent s)
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hR (abs_nonneg θ)]
  have hmake (θ : ℝ) (heθ : δ+R*|θ|<d₀) :
      Nonempty (PhaseProjection T (fun s => phaseRotation θ*γ s) β Tβ K
        (δ+R*|θ|) (C₀*((δ+R*|θ|)+Zerr))) := by
    have hrot : ContDiff ℝ ∞ (fun s => phaseRotation θ*γ s) := contDiff_const.mul hγsmooth
    have hrotper : Function.Periodic (fun s => phaseRotation θ*γ s) T := by
      intro s
      change phaseRotation θ*γ (s+T)=phaseRotation θ*γ s
      rw [hγper s]
    have hrotT (s : ℝ) : HasDerivAt (fun s => phaseRotation θ*Tγ s)
        (I*(kγ s:ℂ)*(phaseRotation θ*Tγ s)) s := by
      apply ((hTγ s).const_mul (phaseRotation θ)).congr_deriv
      ring
    obtain ⟨χ,h,hh,hp,hχ,hχp,hd,H,hHreal,hHvalue,hHbound⟩ :=
      hentry (fun s => phaseRotation θ*γ s) (fun s => phaseRotation θ*Tγ s)
        kγ (δ+R*|θ|) hrot hrotper (fun s => (hγ s).const_mul (phaseRotation θ))
        hrotT (fun s => by rw [norm_mul,phase_rotation_norm,huγ s,one_mul])
        hkγ hkγper (by positivity) heθ
        (fun s => (hangle_error θ s).1) (fun s => (hangle_error θ s).2)
    exact ⟨{
      χ := χ
      h := h
      hsmooth := hh
      hper := hp
      χsmooth := hχ
      χper := hχp
      graph := fun s => (hd s).1
      shift := fun s => (hd s).2.1
      height := fun s => (hd s).2.2.1
      dh := fun s => (hd s).2.2.2.1
      lower := fun s => (hd s).2.2.2.2.1
      upper := fun s => (hd s).2.2.2.2.2
      H := H
      real := hHreal
      value := hHvalue
      bound := hHbound }⟩
  by_cases hz : δ=0
  · have he0 : δ+R*|0|<d₀ := by simpa only [hz,abs_zero,mul_zero,add_zero] using hd₀
    let p := Classical.choice (hmake 0 he0)
    have hhzero : p.h=fun _ => (0:ℝ) := by
      funext s
      have hs := p.height s
      simp only [hz,abs_zero,mul_zero,add_zero] at hs
      exact abs_eq_zero.mp (le_antisymm hs (abs_nonneg _))
    have hvaluezero : circleSobolevCoordinate T 2 0 p.H=0 := by
      rw [p.value]
      have hc : p.heightCircle=0 := by
        apply ContinuousMap.ext
        intro x
        induction x using QuotientAddGroup.induction_on
        rename_i s
        change (p.h s:ℂ)=0
        rw [hhzero]
        rfl
      change circleContinuousL2 T p.heightCircle=0
      rw [hc]
      exact map_zero (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
    refine ⟨0,p.χ,p.h,p.hsmooth,p.hper,?_,p.χsmooth,p.χper,?_,p.H,p.real,p.value,?_,?_⟩
    · simp only [abs_zero,hz,mul_zero,le_refl]
    · intro s
      refine ⟨p.graph s,?_,p.lower s,p.upper s⟩
      have hs := p.shift s
      simpa only [hz,abs_zero,mul_zero,add_zero] using hs
    · rw [hvaluezero,inner_zero_right]
    · exact p.bound.trans (by
        change C₀*((δ+R*|0|)+Zerr)≤C*(δ+Zerr)
        simp only [abs_zero,mul_zero,add_zero]
        exact mul_le_mul_of_nonneg_right hCC (add_nonneg hδ hZerr))
  · have hδpos : 0<δ := lt_of_le_of_ne hδ (Ne.symm hz)
    let r := J*δ
    let ε := E*δ
    have hr : 0<r := mul_pos hJ hδpos
    have hε : 0<ε := mul_pos hE hδpos
    let D := Ioo (-2*r) (2*r)
    have heθ (θ : D) : δ+R*|(θ:ℝ)|≤ε := by
      have ht : |(θ:ℝ)|<2*r := by
        rw [abs_lt]
        constructor <;> linarith [θ.property.1,θ.property.2]
      have hm := mul_le_mul_of_nonneg_left ht.le (by linarith : (0:ℝ)≤R)
      dsimp only [ε,E,r] at *
      nlinarith only [hm]
    let p : (θ : D) → PhaseProjection T (fun s => phaseRotation θ*γ s) β Tβ K
        (δ+R*|(θ:ℝ)|) (C₀*((δ+R*|(θ:ℝ)|)+Zerr)) := fun θ =>
      Classical.choice (hmake θ ((heθ θ).trans_lt hεδ))
    obtain ⟨θ,hθ,hphase⟩ := phase_family_root T γ β Tγ Tβ k hγsmooth hβsmooth
      hγ hβ hTβ huγ huβ hγper hβper K R ε r δ hK hR hε hε₁ hr hδ
      hcurvature hεsmall hγbound hβbound
      (fun θ ht s => ((hangle_error θ s).2).trans (heθ ⟨θ,ht⟩))
      (fun θ => δ+R*|θ|) (fun θ => C₀*((δ+R*|θ|)+Zerr))
      (fun θ ht => heθ ⟨θ,ht⟩) (by simp) p b hb ψ hψ q hq hqpair
      ((mul_le_mul_of_nonneg_right hJsize hδ).trans_eq (by dsimp only [r]; ring)) hnear
    have heθV : δ+R*|(θ:ℝ)|≤V*δ := by
      have hm := mul_le_mul_of_nonneg_left hθ (by linarith : (0:ℝ)≤R)
      dsimp only [V,r] at *
      nlinarith only [hm]
    refine ⟨θ,(p θ).χ,(p θ).h,(p θ).hsmooth,(p θ).hper,?_,
      (p θ).χsmooth,(p θ).χper,?_,(p θ).H,(p θ).real,(p θ).value,hphase,?_⟩
    · exact hθ.trans (mul_le_mul_of_nonneg_right hCJ hδ)
    · intro s
      refine ⟨(p θ).graph s,?_,(p θ).lower s,(p θ).upper s⟩
      calc
        _ ≤ 2*(δ+R*|(θ:ℝ)|) := (p θ).shift s
        _ ≤ 2*(V*δ) := mul_le_mul_of_nonneg_left heθV (by norm_num : (0:ℝ)≤2)
        _ = (2*V)*δ := by ring
        _ ≤ C*δ := mul_le_mul_of_nonneg_right hCV hδ
    · apply (p θ).bound.trans
      change C₀*((δ+R*|(θ:ℝ)|)+Zerr)≤C*(δ+Zerr)
      calc
        _ ≤ C₀*(V*δ+Zerr) := mul_le_mul_of_nonneg_left (add_le_add heθV le_rfl) hC₀.le
        _ = (C₀*V)*δ+C₀*Zerr := by ring
        _ ≤ C*δ+C*Zerr := add_le_add (mul_le_mul_of_nonneg_right hCCV hδ)
          (mul_le_mul_of_nonneg_right hCC hZerr)
        _ = _ := by ring



open Complex MeasureTheory Set
open scoped Topology ContDiff ComplexConjugate

private theorem integral_cauchy_schwarz_const
    (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ s in (0:ℝ)..T, f s) ≤ Real.sqrt (T*(∫ s in (0:ℝ)..T, (f s)^2)) := by
  let J := ∫ s in (0:ℝ)..T, f s
  have hnonneg : 0 ≤ ∫ s in (0:ℝ)..T, (T*f s-J)^2 :=
    intervalIntegral.integral_nonneg hT.le (fun _ _ => sq_nonneg _)
  have hid : (∫ s in (0:ℝ)..T, (T*f s-J)^2) =
      T*(T*(∫ s in (0:ℝ)..T, (f s)^2)-J^2) := by
    calc
      _ = ∫ s in (0:ℝ)..T, T^2*(f s)^2-(2*T*J)*f s+J^2 := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = T*(T*(∫ s in (0:ℝ)..T, (f s)^2)-J^2) := by
        have hA : IntervalIntegrable (fun s => T^2*(f s)^2) volume 0 T := by
          simpa only [Pi.pow_apply] using ((hf.pow 2).const_mul (T^2)).intervalIntegrable 0 T
        have hB : IntervalIntegrable (fun s => (2*T*J)*f s) volume 0 T :=
          (hf.const_mul (2*T*J)).intervalIntegrable 0 T
        have hsum :
            (∫ s in (0:ℝ)..T, T^2*(f s)^2-(2*T*J)*f s+J^2) =
              (∫ s in (0:ℝ)..T, T^2*(f s)^2-(2*T*J)*f s)+
                (∫ _s in (0:ℝ)..T, J^2) := by
          simpa only [Pi.sub_apply] using
            intervalIntegral.integral_add (hA.sub hB) (intervalIntegrable_const (c := J^2))
        have hsub : (∫ s in (0:ℝ)..T, T^2*(f s)^2-(2*T*J)*f s) =
            (∫ s in (0:ℝ)..T, T^2*(f s)^2)-(∫ s in (0:ℝ)..T, (2*T*J)*f s) :=
          intervalIntegral.integral_sub hA hB
        rw [hsum,hsub,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero,smul_eq_mul]
        change T^2*(∫ s in (0:ℝ)..T, (f s)^2)-(2*T*J)*J+T*J^2 = _
        ring
  have hmul : 0 ≤ T*(T*(∫ s in (0:ℝ)..T, (f s)^2)-J^2) := hid ▸ hnonneg
  exact Real.le_sqrt_of_sq_le (sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hT).mp hmul))

private theorem tangent_periodic
    (γ t : ℝ → ℂ) (T : ℝ) (hγ : ∀ s, HasDerivAt γ (t s) s)
    (hp : Function.Periodic γ T) : Function.Periodic t T := by
  have ht : deriv γ = t := funext (fun s => (hγ s).deriv)
  rw [← ht]
  intro s
  have heq : (fun u => γ (u+T)) = γ := funext hp
  simpa only [deriv_comp_add_const] using congrArg (fun F => deriv F s) heq

private theorem periodic_bound_of_Icc
    {E : Type*} [NormedAddCommGroup E] (T δ : ℝ) (hT : 0 < T)
    (f : ℝ → E) (hp : Function.Periodic f T)
    (hb : ∀ s ∈ Icc (0:ℝ) T, ‖f s‖ ≤ δ) : ∀ s, ‖f s‖ ≤ δ := by
  intro s
  obtain ⟨u,hu,heq⟩ := hp.exists_mem_Ico₀ hT s
  rw [heq]
  exact hb u ⟨hu.1,hu.2.le⟩

private theorem aligned_curvature_c1_bound
    (T : ℝ) (hT : 0 < T) (β γ Tβ Tγ : ℝ → ℂ) (k kγ : ℝ → ℝ)
    (hk : Continuous k) (hkγ : Continuous kγ)
    (hβper : Function.Periodic β T) (hγper : Function.Periodic γ T)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s) (hγ : ∀ s, HasDerivAt γ (Tγ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hTγ : ∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s)
    (huβ : ∀ s, ‖Tβ s‖ = 1) (huγ : ∀ s, ‖Tγ s‖ = 1)
    (hpos : γ 0 = β 0) (htan : Tγ 0 = Tβ 0) :
    ∀ s, ‖γ s-β s‖ ≤ (T+1)*Real.sqrt (T*(∫ r in (0:ℝ)..T, (kγ r-k r)^2)) ∧
      ‖Tγ s-Tβ s‖ ≤ (T+1)*Real.sqrt (T*(∫ r in (0:ℝ)..T, (kγ r-k r)^2)) := by
  let Z := Real.sqrt (T*(∫ r in (0:ℝ)..T, (kγ r-k r)^2))
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hL1 : (∫ r in (0:ℝ)..T, |kγ r-k r|) ≤ Z := by
    simpa only [Z,sq_abs] using
      integral_cauchy_schwarz_const T hT (fun r => |kγ r-k r|) (hkγ.sub hk).abs
  have hcompare := aligned_frenet_comparison β γ Tβ Tγ k kγ T
    hk hkγ hβ hγ hTβ hTγ huβ huγ hpos htan
  have hsubint (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      (∫ r in (0:ℝ)..s, |kγ r-k r|) ≤ Z :=
    (intervalIntegral.integral_mono_interval le_rfl hs.1 hs.2
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      ((hkγ.sub hk).abs.intervalIntegrable 0 T)).trans hL1
  have hposition : ∀ s ∈ Icc (0:ℝ) T, ‖γ s-β s‖ ≤ (T+1)*Z := by
    intro s hs
    calc
      _ ≤ s*(∫ r in (0:ℝ)..s, |kγ r-k r|) := (hcompare s hs).2
      _ ≤ T*Z := mul_le_mul hs.2 (hsubint s hs)
        (intervalIntegral.integral_nonneg hs.1 (fun _ _ => abs_nonneg _)) hT.le
      _ ≤ (T+1)*Z := mul_le_mul_of_nonneg_right (by linarith : T ≤ T+1) hZ
  have htangent : ∀ s ∈ Icc (0:ℝ) T, ‖Tγ s-Tβ s‖ ≤ (T+1)*Z := by
    intro s hs
    exact ((hcompare s hs).1.trans (hsubint s hs)).trans
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : (1:ℝ) ≤ T+1) hZ)
  have hTβper := tangent_periodic β Tβ T hβ hβper
  have hTγper := tangent_periodic γ Tγ T hγ hγper
  have hp := periodic_bound_of_Icc T ((T+1)*Z) hT (fun s => γ s-β s)
    (fun s => by change γ (s+T)-β (s+T) = γ s-β s; rw [hγper s,hβper s]) hposition
  have ht := periodic_bound_of_Icc T ((T+1)*Z) hT (fun s => Tγ s-Tβ s)
    (fun s => by change Tγ (s+T)-Tβ (s+T) = Tγ s-Tβ s; rw [hTγper s,hTβper s]) htangent
  exact fun s => ⟨hp s,ht s⟩

private theorem unalign_graph
    (Q E z z₀ b g : ℂ) (hQ : Q ≠ 0) (hE : E ≠ 0)
    (h : E*(Q*(z-z₀)+b) = g) :
    z = (z₀-Q⁻¹*b)+(Q⁻¹*E⁻¹)*g := by
  rw [← h]
  field_simp [hQ,hE] <;> ring

private theorem positive_pair_transport {P : ℝ → ℝ → Prop} {Q : Prop}
    (h : ∃ a > 0, ∃ b > 0, P a b)
    (k : ∀ a, 0 < a → ∀ b, 0 < b → P a b → Q) : Q := by
  obtain ⟨a,ha,b,hb,hP⟩ := h
  exact k a ha b hb hP

set_option maxHeartbeats 1200000 in
/-- A small scale-invariant L2 curvature-profile error places a smooth
closed arclength-parametrized curve, after one Euclidean motion, in a real
normal graph satisfying the prescribed L2 phase condition. -/
theorem periodic_curvature_profile_entry
    (T : ℝ) [Fact (0<T)] (β Tβ : ℝ → ℂ) (k ks : ℝ → ℝ)
    (hβsmooth : ContDiff ℝ ∞ β) (hβper : Function.Periodic β T)
    (hβ : ∀ s, HasDerivAt β (Tβ s) s)
    (hTβ : ∀ s, HasDerivAt Tβ (I*(k s:ℂ)*Tβ s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s) (huβ : ∀ s, ‖Tβ s‖=1)
    (K K₁ : ℝ) (hK : 0≤K) (hK₁ : 0≤K₁)
    (hcurvature : ∀ s, |k s|≤K) (hcurvatureDerivative : ∀ s, |ks s|≤K₁)
    (b : C(AddCircle T,ℂ))
    (hb : ∀ s : ℝ, b (s:AddCircle T)=((conj (Tβ s)*β s).re:ℂ))
    (ψ : CircleL2 T) (hψ : circleConjugate T ψ=ψ)
    (hpair : inner ℂ ψ (circleContinuousL2 T b)≠0) :
    ∃ ε > 0, ∃ C > 0, ∀ (γ Tγ : ℝ → ℂ) (kγ : ℝ → ℝ),
      ContDiff ℝ ∞ γ → Function.Periodic γ T →
      (∀ s, HasDerivAt γ (Tγ s) s) →
      (∀ s, HasDerivAt Tγ (I*(kγ s:ℂ)*Tγ s) s) →
      (∀ s, ‖Tγ s‖=1) → Continuous kγ → Function.Periodic kγ T →
      T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2) < ε →
      ∃ (p₀ r : ℂ), ‖r‖ = 1 ∧ ∃ χ h : ℝ → ℝ,
        ∃ hh : ContDiff ℝ ∞ h, ∃ hp : Function.Periodic h T,
          ContDiff ℝ ∞ χ ∧ Function.Periodic (fun s => χ s-s) T ∧
          (∀ s, γ (χ s) = p₀+r*(β s+I*(h s:ℂ)*Tβ s) ∧
            |χ s-s| ≤ C*Real.sqrt (T*(∫ u in (0:ℝ)..T, (kγ u-k u)^2)) ∧
            (1/4:ℝ) ≤ deriv χ s ∧ deriv χ s ≤ 4) ∧
          ∃ H : CircleSobolevSpace T 2,
            circleSobolevConjugation T 2 H = H ∧
            circleSobolevCoordinate T 2 0 H = circleContinuousL2 T
              (periodicCircleFunction T (fun s => (h s:ℂ))
                (fun s => congrArg Complex.ofReal (hp s))
                (Complex.continuous_ofReal.comp hh.continuous)) ∧
            inner ℂ ψ (circleSobolevCoordinate T 2 0 H) = 0 ∧
            ‖H‖ ≤ C*Real.sqrt (T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2)) := by
  have hT : 0<T := Fact.out
  refine positive_pair_transport (periodic_normal_graph_phase_exists T β Tβ k ks
    hβsmooth hβper hβ hTβ hk huβ K K₁ hK hK₁ hcurvature hcurvatureDerivative
    b hb ψ hψ hpair) ?_
  intro δ₀ hδ₀ C₀ hC₀ hentry
  let A : ℝ := T+1
  have hA : 0<A := by dsimp only [A]; linarith only [hT]
  let ε : ℝ := (δ₀/A)^2
  let C : ℝ := C₀*(A+1)
  have hε : 0<ε := sq_pos_of_pos (div_pos hδ₀ hA)
  have hC : 0<C := mul_pos hC₀ (by linarith only [hA])
  refine ⟨ε,hε,C,hC,?_⟩
  intro γ Tγ kγ hγsmooth hγper hγ hTγ huγ hkγ hkγper hsmall
  let Eκ : ℝ := T*(∫ s in (0:ℝ)..T, (kγ s-k s)^2)
  let Z : ℝ := Real.sqrt Eκ
  let δ : ℝ := A*Z
  have hZ : 0≤Z := Real.sqrt_nonneg _
  have hδ : 0≤δ := mul_nonneg hA.le hZ
  have hroot : Z < δ₀/A := (Real.sqrt_lt' (div_pos hδ₀ hA)).mpr hsmall
  have hδlt : δ < δ₀ := by
    have hh := (lt_div_iff₀ hA).mp hroot
    change A*Z < δ₀
    nlinarith only [hh]
  let Q : ℂ := Tβ 0*conj (Tγ 0)
  have hQnorm : ‖Q‖=1 := by simp only [Q,norm_mul,Complex.norm_conj,huβ,huγ,one_mul]
  have hQne : Q ≠ 0 := by
    intro hz
    have h := hQnorm
    rw [hz,norm_zero] at h
    norm_num at h
  let γa : ℝ → ℂ := fun s => Q*(γ s-γ 0)+β 0
  let Ta : ℝ → ℂ := fun s => Q*Tγ s
  have hγaSmooth : ContDiff ℝ ∞ γa :=
    (contDiff_const.mul (hγsmooth.sub contDiff_const)).add contDiff_const
  have hγaPer : Function.Periodic γa T := by
    intro s
    change Q*(γ (s+T)-γ 0)+β 0 = Q*(γ s-γ 0)+β 0
    rw [hγper s]
  have hγa (s : ℝ) : HasDerivAt γa (Ta s) s :=
    (((hγ s).sub_const (γ 0)).const_mul Q).add_const (β 0)
  have hTa (s : ℝ) : HasDerivAt Ta (I*(kγ s:ℂ)*Ta s) s := by
    apply ((hTγ s).const_mul Q).congr_deriv
    dsimp only [Ta]
    ring
  have hua (s : ℝ) : ‖Ta s‖=1 := by simp only [Ta,norm_mul,hQnorm,huγ,one_mul]
  have hpos : γa 0 = β 0 := by simp only [γa,sub_self,mul_zero,zero_add]
  have htan : Ta 0 = Tβ 0 := by
    have hself : conj (Tγ 0)*Tγ 0=1 := by rw [Complex.conj_mul',huγ 0]; norm_num
    change (Tβ 0*conj (Tγ 0))*Tγ 0 = Tβ 0
    rw [mul_assoc,hself,mul_one]
  have hkcont : Continuous k := continuous_iff_continuousAt.mpr (fun s => (hk s).continuousAt)
  have hclose := aligned_curvature_c1_bound T hT β γa Tβ Ta k kγ hkcont hkγ
    hβper hγaPer hβ hγa hTβ hTa huβ hua hpos htan
  obtain ⟨θ,χ,h,hh,hp,_,hχ,hχper,hgraph,H,hHreal,hHvalue,hphase,hHbound⟩ :=
    hentry γa Ta kγ δ hγaSmooth hγaPer hγa hTa hua hkγ hkγper hδ hδlt
      (fun s => (hclose s).1) (fun s => (hclose s).2)
  let E : ℂ := Complex.exp ((-θ:ℝ)*I)
  have hEnorm : ‖E‖=1 := Complex.norm_exp_ofReal_mul_I (-θ)
  have hEne : E ≠ 0 := Complex.exp_ne_zero _
  let p₀ := γ 0-Q⁻¹*β 0
  let r := Q⁻¹*E⁻¹
  have hr : ‖r‖=1 := by simp only [r,norm_mul,norm_inv,hQnorm,hEnorm,inv_one,mul_one]
  have hcoef : C₀*A ≤ C := by dsimp only [C]; nlinarith only [hC₀.le]
  refine ⟨p₀,r,hr,χ,h,hh,hp,hχ,hχper,?_,H,hHreal,hHvalue,hphase,?_⟩
  · intro s
    refine ⟨unalign_graph Q E (γ (χ s)) (γ 0) (β 0) _ hQne hEne (hgraph s).1,?_,
      (hgraph s).2.2.1,(hgraph s).2.2.2⟩
    calc
      |χ s-s| ≤ C₀*δ := (hgraph s).2.1
      _ = (C₀*A)*Z := by dsimp only [δ]; ring
      _ ≤ C*Z := mul_le_mul_of_nonneg_right hcoef hZ
  · apply hHbound.trans
    change C₀*(δ+Z) ≤ C*Z
    exact le_of_eq (by dsimp only [δ,C]; ring)


end Lemniscate
