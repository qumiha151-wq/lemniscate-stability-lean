import Lemniscate.NormalGraphRotation
import Lemniscate.NormalGraphSobolevRemainder
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Adjoint-normalized rotation modulation of the normal-graph equation.

The correction has zero derivative at the equilibrium. Its two-point
remainder uses the already proved H2-H4 estimate and the H2 smoothness
of the normalized rotation field. No evolution or uniqueness theorem is
assumed here.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

def circleNormalGraphModulatedFlow (K : BackgroundJetOver C(AddCircle T, ℂ))
    (c : ℝ) (ψ : CircleL2 T) (f : CircleSobolevSpace T 4) : CircleL2 T :=
  circleNormalGraphFlow T K c f-
    circleNormalGraphRotationFunctional T ψ (circleNormalGraphFlow T K c f) •
      circleNormalGraphNormalizedRotation T K ψ
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))

private theorem normal_graph_modulation_difference
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (x y l u v : E) (a b : ℂ) :
    (x-a • u)-(y-b • v)-l =
      (x-y-l)-(a-b) • u-b • (u-v) := by
  simp only [sub_smul,smul_sub]
  abel

set_option maxHeartbeats 800000 in
/-- Rotation modulation preserves the equilibrium, the full Frechet
derivative, and the mixed H2-H4 tame estimate. On the same H2 ball its
values lie in the kernel of the adjoint neutral functional. -/
theorem circle_normal_graph_modulated_tame
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (ψ : CircleL2 T)
    (hpair : inner ℂ ψ (circleContinuousL2 T K.b) ≠ 0)
    (hzero : circleNormalGraphFlow T K c 0 = 0)
    (hneutral : ∀ f : CircleSobolevSpace T 4,
      circleNormalGraphRotationFunctional T ψ
        (circleNormalGraphDerivative T K c f) = 0) :
    circleNormalGraphModulatedFlow T K c ψ 0 = 0 ∧
      HasFDerivAt (circleNormalGraphModulatedFlow T K c ψ)
        (circleNormalGraphDerivative T K c) 0 ∧
      ∃ δ > 0, ∃ C > 0,
        (∀ f : CircleSobolevSpace T 4,
          ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
          circleNormalGraphRotationFunctional T ψ
            (circleNormalGraphModulatedFlow T K c ψ f) = 0) ∧
        ∀ f g : CircleSobolevSpace T 4,
          ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
          ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖ < δ →
          ‖circleNormalGraphModulatedFlow T K c ψ f-
              circleNormalGraphModulatedFlow T K c ψ g-
              circleNormalGraphDerivative T K c (f-g)‖ ≤
            C*((‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖+
                  ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 g)‖)*‖f-g‖+
              (‖f‖+‖g‖)*
                ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 (f-g))‖) := by
  let F := circleNormalGraphFlow T K c
  let L := circleNormalGraphDerivative T K c
  let ell := circleNormalGraphRotationFunctional T ψ
  let Z := circleNormalGraphNormalizedRotation T K ψ
  let S : CircleSobolevSpace T 4 →L[ℂ] CircleSobolevSpace T 2 :=
    (circleSobolevInclusion T 2).comp (circleSobolevInclusion T 3)
  let H₂ : CircleSobolevSpace T 4 → ℝ := fun f => ‖S f‖
  let N : CircleSobolevSpace T 4 → CircleL2 T := fun f => F f-L f
  let β : CircleSobolevSpace T 4 → ℂ := fun f => ell (F f)
  let Q (f g : CircleSobolevSpace T 4) :=
    (H₂ f+H₂ g)*‖f-g‖+(‖f‖+‖g‖)*H₂ (f-g)
  have hFzero : F 0 = 0 := hzero
  have hLzero : ∀ f, ell (L f) = 0 := hneutral
  have hmod (f : CircleSobolevSpace T 4) :
      circleNormalGraphModulatedFlow T K c ψ f = F f-β f • Z (S f) := rfl
  have hNzero : N 0 = 0 := by
    simp only [N,hFzero,map_zero,sub_zero]
  have hβ (f : CircleSobolevSpace T 4) : β f = ell (N f) := by
    simp only [β,N,map_sub,hLzero,sub_zero]
  obtain ⟨_,_,hZsmooth,_,hnormalize⟩ :=
    circle_normal_graph_rotation_normalization T K ψ hpair
  have hZsmooth' : ContDiffAt ℂ (⊤ : WithTop ℕ∞) Z 0 := hZsmooth
  have heqzero : circleNormalGraphModulatedFlow T K c ψ 0 = 0 := by
    rw [hmod]
    simp only [β,hFzero,map_zero,zero_smul,sub_zero]
  have hF : HasFDerivAt F L 0 := circle_normal_graph_hasFDerivAt T K c
  have hellL : ell.comp L = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    exact hLzero f
  have hβderiv : HasFDerivAt β (0 : CircleSobolevSpace T 4 →L[ℂ] ℂ) 0 := by
    have h := ell.hasFDerivAt.comp 0 hF
    rw [hellL] at h
    exact h
  have hZat : HasFDerivAt Z (fderiv ℂ Z 0) (S 0) := by
    simpa only [map_zero] using
      (hZsmooth'.differentiableAt (by simp)).hasFDerivAt
  have hZS := hZat.comp 0 S.hasFDerivAt
  have hcorrection : HasFDerivAt
      (fun f : CircleSobolevSpace T 4 => β f • Z (S f))
        (0 : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T) 0 := by
    apply (hβderiv.smul hZS).congr_fderiv
    apply ContinuousLinearMap.ext
    intro f
    change β 0 • ((fderiv ℂ Z 0).comp S) f+
      (0 : CircleSobolevSpace T 4 →L[ℂ] ℂ) f • Z (S 0) = 0
    simp only [β,hFzero,map_zero,ContinuousLinearMap.zero_apply,
      zero_smul,add_zero]
  have hmodderiv : HasFDerivAt (circleNormalGraphModulatedFlow T K c ψ) L 0 := by
    simpa only [sub_zero,circleNormalGraphModulatedFlow,F,β,Z,S,ell,Pi.sub_apply,
      ContinuousLinearMap.comp_apply] using! hF.sub hcorrection
  refine ⟨heqzero,hmodderiv,?_⟩
  obtain ⟨rN,hrN,CN,hCN,hNLR⟩ :=
    circle_normal_graph_sobolev_tame_remainder T K c
  have hZone : ContDiffAt ℂ 1 Z 0 := hZsmooth'.of_le le_top
  obtain ⟨LZ,s,hs,hLip⟩ := hZone.exists_lipschitzOnWith
  have hnormal : ∀ᶠ u : CircleSobolevSpace T 2 in 𝓝 0, ell (Z u) = 1 :=
    hnormalize.mono fun _ h => h.2.2
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hnormal)
  let δ : ℝ := min rN (min d 1)
  have hδ : 0 < δ := lt_min hrN (lt_min hd zero_lt_one)
  have hsmall {f : CircleSobolevSpace T 4} (hf : H₂ f < δ) :
      H₂ f < rN ∧ S f ∈ s ∧ ell (Z (S f)) = 1 ∧ H₂ f ≤ 1 := by
    have hfN : H₂ f < rN := lt_of_lt_of_le hf (min_le_left _ _)
    have hfd : H₂ f < d :=
      lt_of_lt_of_le hf ((min_le_right rN (min d 1)).trans (min_le_left d 1))
    have hf1 : H₂ f ≤ 1 :=
      (lt_of_lt_of_le hf ((min_le_right rN (min d 1)).trans (min_le_right d 1))).le
    have hfball : S f ∈ Metric.ball (0 : CircleSobolevSpace T 2) d := by
      simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hfd
    exact ⟨hfN,(hball hfball).1,(hball hfball).2,hf1⟩
  have hsmallzero : H₂ (0 : CircleSobolevSpace T 4) < δ := by
    simpa only [H₂,map_zero,norm_zero] using hδ
  have hNdiff (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖N f-N g‖ ≤ CN*Q f g := by
    have h := hNLR f g (hsmall hf).1 (hsmall hg).1
    change ‖F f-F g-L (f-g)‖ ≤ CN*Q f g at h
    have heq : N f-N g = F f-F g-L (f-g) := by
      simp only [N,map_sub]
      abel
    rw [heq]
    exact h
  have hNvalue (g : CircleSobolevSpace T 4) (hg : H₂ g < δ) :
      ‖N g‖ ≤ (2*CN)*H₂ g*‖g‖ := by
    calc
      ‖N g‖ = ‖N g-N 0‖ := by rw [hNzero,sub_zero]
      _ ≤ CN*Q g 0 := hNdiff g 0 hg hsmallzero
      _ = (2*CN)*H₂ g*‖g‖ := by
        simp only [Q,H₂,map_zero,norm_zero,add_zero,sub_zero]
        ring
  have hβdiff (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖β f-β g‖ ≤ ‖ell‖*(CN*Q f g) := by
    calc
      ‖β f-β g‖ = ‖ell (N f-N g)‖ := by rw [map_sub,← hβ f,← hβ g]
      _ ≤ ‖ell‖*‖N f-N g‖ := ell.le_opNorm _
      _ ≤ ‖ell‖*(CN*Q f g) :=
        mul_le_mul_of_nonneg_left (hNdiff f g hf hg) (norm_nonneg ell)
  have hβvalue (g : CircleSobolevSpace T 4) (hg : H₂ g < δ) :
      ‖β g‖ ≤ ‖ell‖*((2*CN)*H₂ g*‖g‖) := by
    rw [hβ g]
    exact (ell.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hNvalue g hg) (norm_nonneg ell))
  let A : ℝ := (LZ:ℝ)+1
  have hA : 0 < A := by dsimp only [A]; positivity
  have hLA : (LZ:ℝ) ≤ A := le_add_of_nonneg_right zero_le_one
  let M : ℝ := ‖Z 0‖+A+1
  have hM : 0 < M := by dsimp only [M]; positivity
  have hZdiff (f g : CircleSobolevSpace T 4) (hf : H₂ f < δ) (hg : H₂ g < δ) :
      ‖Z (S f)-Z (S g)‖ ≤ A*H₂ (f-g) := by
    have h : ‖Z (S f)-Z (S g)‖ ≤ (LZ:ℝ)*H₂ (f-g) := by
      simpa only [dist_eq_norm,H₂,map_sub] using
        hLip.dist_le_mul (S f) (hsmall hf).2.1 (S g) (hsmall hg).2.1
    exact h.trans (mul_le_mul_of_nonneg_right hLA (norm_nonneg (S (f-g))))
  have hZbound (f : CircleSobolevSpace T 4) (hf : H₂ f < δ) : ‖Z (S f)‖ ≤ M := by
    have h := hZdiff f 0 hf hsmallzero
    simp only [map_zero,sub_zero] at h
    calc
      ‖Z (S f)‖ ≤ ‖Z (S f)-Z 0‖+‖Z 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (Z (S f)-Z 0) (Z 0)
      _ ≤ A*H₂ f+‖Z 0‖ := add_le_add h le_rfl
      _ ≤ A+‖Z 0‖ := by
        simpa only [mul_one] using add_le_add
          (mul_le_mul_of_nonneg_left (hsmall hf).2.2.2 hA.le) le_rfl
      _ ≤ A+‖Z 0‖+1 := le_add_of_nonneg_right zero_le_one
      _ = M := by dsimp only [M]; ring
  let C : ℝ := CN*(1+‖ell‖*M+2*‖ell‖*A)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨δ,hδ,C,hC,?_,?_⟩
  · intro f hf
    change ell (circleNormalGraphModulatedFlow T K c ψ f) = 0
    rw [hmod,map_sub,map_smul,(hsmall hf).2.2.1]
    simp only [β,smul_eq_mul,mul_one,sub_self]
  · intro f g hf hg
    change ‖circleNormalGraphModulatedFlow T K c ψ f-
      circleNormalGraphModulatedFlow T K c ψ g-L (f-g)‖ ≤ C*Q f g
    have hR : 0 ≤ Q f g := by dsimp only [Q,H₂]; positivity
    have hR2 : (‖f‖+‖g‖)*H₂ (f-g) ≤ Q f g := by
      exact le_add_of_nonneg_left (by dsimp only [H₂]; positivity)
    have hgv : H₂ g*‖g‖ ≤ ‖f‖+‖g‖ := by
      calc
        H₂ g*‖g‖ ≤ 1*‖g‖ :=
          mul_le_mul_of_nonneg_right (hsmall hg).2.2.2 (norm_nonneg g)
        _ ≤ ‖f‖+‖g‖ := by simpa only [one_mul] using le_add_of_nonneg_left (norm_nonneg f)
    have hthird : (‖ell‖*((2*CN)*H₂ g*‖g‖))*(A*H₂ (f-g)) ≤
        (2*CN*‖ell‖*A)*Q f g := by
      calc
        (‖ell‖*((2*CN)*H₂ g*‖g‖))*(A*H₂ (f-g)) =
            (2*CN*‖ell‖*A)*(H₂ g*‖g‖)*H₂ (f-g) := by ring
        _ ≤ (2*CN*‖ell‖*A)*(‖f‖+‖g‖)*H₂ (f-g) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hgv (by positivity)) (norm_nonneg (S (f-g)))
        _ ≤ (2*CN*‖ell‖*A)*Q f g := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hR2
            (by positivity : (0:ℝ) ≤ 2*CN*‖ell‖*A)
    have heq : circleNormalGraphModulatedFlow T K c ψ f-
        circleNormalGraphModulatedFlow T K c ψ g-L (f-g) =
        (N f-N g)-(β f-β g) • Z (S f)-β g • (Z (S f)-Z (S g)) := by
      rw [hmod,hmod]
      have h := normal_graph_modulation_difference
        (F f) (F g) (L (f-g)) (Z (S f)) (Z (S g)) (β f) (β g)
      have hN : F f-F g-L (f-g) = N f-N g := by
        simp only [N,map_sub]
        abel
      simpa only [hN] using h
    calc
      ‖circleNormalGraphModulatedFlow T K c ψ f-
          circleNormalGraphModulatedFlow T K c ψ g-L (f-g)‖ =
          ‖(N f-N g)-(β f-β g) • Z (S f)-β g • (Z (S f)-Z (S g))‖ := congrArg norm heq
      _ ≤ ‖N f-N g‖+‖(β f-β g) • Z (S f)‖+
          ‖β g • (Z (S f)-Z (S g))‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ = ‖N f-N g‖+‖β f-β g‖*‖Z (S f)‖+
          ‖β g‖*‖Z (S f)-Z (S g)‖ := by rw [norm_smul,norm_smul]
      _ ≤ CN*Q f g+(‖ell‖*(CN*Q f g))*M+
          (‖ell‖*((2*CN)*H₂ g*‖g‖))*(A*H₂ (f-g)) := by
        exact add_le_add
          (add_le_add (hNdiff f g hf hg)
            (mul_le_mul (hβdiff f g hf hg) (hZbound f hf) (norm_nonneg _)
              (mul_nonneg (norm_nonneg ell) (mul_nonneg hCN.le hR))))
          (mul_le_mul (hβvalue g hg) (hZdiff f g hf hg) (norm_nonneg _) (by positivity))
      _ ≤ CN*Q f g+(‖ell‖*(CN*Q f g))*M+(2*CN*‖ell‖*A)*Q f g :=
        add_le_add le_rfl hthird
      _ = C*Q f g := by dsimp only [C]; ring

end Lemniscate
