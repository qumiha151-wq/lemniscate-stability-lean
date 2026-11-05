import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-! A two-point tame remainder estimate gives continuity on its domain,
without smallness of the full strong norm or openness of that domain. -/
namespace Lemniscate
open Filter Set
open scoped Topology

/-- The mixed strong/weak two-point remainder bound implies continuity
of the nonlinear map on the actual domain. No sign assumption on the
remainder constant, or smallness of the strong norm, is required. -/
theorem tame_nonlinear_continuousOn
    {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (D : E →L[𝕜] F) (S : E →L[𝕜] G) (A : Set E) (C : ℝ) (N : E → F)
    (htame : ∀ x ∈ A, ∀ y ∈ A,
      ‖N x-N y-D (x-y)‖ ≤ C*((‖S x‖+‖S y‖)*‖x-y‖+
        (‖x‖+‖y‖)*‖S (x-y)‖)) :
    ContinuousOn N A := by
  intro f hf
  let M : E → ℝ := fun g => ‖D‖*‖g-f‖+
    C*((‖S g‖+‖S f‖)*‖g-f‖+(‖g‖+‖f‖)*‖S (g-f)‖)
  have hd : Continuous (fun g : E => g-f) := continuous_id.sub continuous_const
  have h₁ : Continuous (fun g : E => ‖D‖*‖g-f‖) := continuous_const.mul hd.norm
  have h₂ : Continuous (fun g : E => (‖S g‖+‖S f‖)*‖g-f‖) :=
    (S.continuous.norm.add continuous_const).mul hd.norm
  have h₃ : Continuous (fun g : E => (‖g‖+‖f‖)*‖S (g-f)‖) :=
    (continuous_norm.add continuous_const).mul (S.continuous.comp hd).norm
  have hM : Continuous M := h₁.add (continuous_const.mul (h₂.add h₃))
  have hlim : Tendsto M (𝓝[A] f) (𝓝 0) := by
    have h : Tendsto M (𝓝[A] f) (𝓝 (M f)) :=
      hM.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [M,sub_self,map_zero,norm_zero,mul_zero,zero_add,add_zero] using h
  have hbound : ∀ᶠ g in 𝓝[A] f, ‖N g-N f‖ ≤ M g := by
    filter_upwards [self_mem_nhdsWithin] with g hg
    calc
      ‖N g-N f‖ ≤ ‖N g-N f-D (g-f)‖+‖D (g-f)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (N g-N f-D (g-f)) (D (g-f))
      _ ≤ C*((‖S g‖+‖S f‖)*‖g-f‖+(‖g‖+‖f‖)*‖S (g-f)‖)+‖D‖*‖g-f‖ :=
        add_le_add (htame g hg f hf) (D.le_opNorm (g-f))
      _ = M g := add_comm _ _
  have hzero : Tendsto (fun g => N g-N f) (𝓝[A] f) (𝓝 0) :=
    squeeze_zero_norm' hbound hlim
  change Tendsto N (𝓝[A] f) (𝓝 (N f))
  simpa only [sub_add_cancel,zero_add] using! hzero.add_const (N f)

end Lemniscate
