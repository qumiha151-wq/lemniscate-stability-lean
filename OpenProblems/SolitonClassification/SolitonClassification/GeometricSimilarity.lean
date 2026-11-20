import SolitonClassification.NormalizedSimilarity

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSimilarity.ReflectedArc

/-- Plane similarity and a freely chosen C¹ change of parameter on the
    lifted paths. Ignoring the named periods allows arbitrary finite covers. -/
structure GeometricSimilarity {L b T d : ℝ} (P : ZeroTurnExpander L b)
    (Q : ZeroTurnExpander T d) where
  parameter : ℝ → ℝ
  smooth : ContDiff ℝ 1 parameter
  scale : ℝ
  positive : 0<scale
  m : ℝ
  n : ℝ
  p : ℝ
  q : ℝ
  x : ℝ
  y : ℝ
  col₁ : m^2+p^2=scale^2
  col₂ : n^2+q^2=scale^2
  orthogonal : m*n+p*q=0
  first : ∀ s, Q.X (parameter s)=m*P.X s+n*P.Y s+x
  second : ∀ s, Q.Y (parameter s)=p*P.X s+q*P.Y s+y

theorem GeometricSimilarity.lifted {L b T d : ℝ} {P : ZeroTurnExpander L b}
    {Q : ZeroTurnExpander T d} (S : GeometricSimilarity P Q) :
    ∃ A : LiftedSimilarity P Q, A.a^2=S.scale^2 ∧ A.x=S.x ∧ A.y=S.y := by
  have param (s : ℝ) := (S.smooth.differentiable (by simp) s).hasDerivAt
  have coord (F : ℝ→ℝ) (hF : ContDiff ℝ ∞ F) (i j z : ℝ)
      (h : ∀ s, F (S.parameter s)=i*P.X s+j*P.Y s+z) (s : ℝ) :
      deriv F (S.parameter s)*deriv S.parameter s=i*deriv P.X s+j*deriv P.Y s := by
    have h₁ := ((hF.differentiable (by simp) _).hasDerivAt).comp s (param s)
    change HasDerivAt (fun s => F (S.parameter s)) _ _ at h₁
    rw [funext h] at h₁
    exact h₁.unique (((((P.X_smooth.differentiable (by simp) _).hasDerivAt).const_mul i).add
      (((P.Y_smooth.differentiable (by simp) _).hasDerivAt).const_mul j)).add_const z)
  have sq (s : ℝ) : (deriv S.parameter s)^2=S.scale^2 := by
    have h₁ := coord _ Q.X_smooth _ _ _ S.first s
    have h₂ := coord _ Q.Y_smooth _ _ _ S.second s
    calc
      _ = (deriv Q.X (S.parameter s)*deriv S.parameter s)^2+
          (deriv Q.Y (S.parameter s)*deriv S.parameter s)^2 := by
            linear_combination -(deriv S.parameter s)^2 * Q.unit_speed (S.parameter s)
      _ = _ := by
        rw [h₁,h₂]
        linear_combination (deriv P.X s)^2*S.col₁+(deriv P.Y s)^2*S.col₂+
          2*deriv P.X s*deriv P.Y s*S.orthogonal+S.scale^2*P.unit_speed s
  have nz (s : ℝ) : deriv S.parameter s≠0 := by
    intro e
    have w := sq s
    rw [e] at w
    nlinarith only [w,sq_pos_of_pos S.positive]
  have cont := S.smooth.continuous_deriv (by simp)
  have const (s : ℝ) : deriv S.parameter s=deriv S.parameter 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((sq s).trans (sq 0).symm) with h|h
    · exact h
    exfalso
    rcases lt_or_gt_of_ne (nz 0) with h0|h0
    · obtain ⟨t,ht⟩ := intermediate_value_univ 0 s cont (show (0:ℝ)∈Icc _ _ from ⟨h0.le,by linarith⟩)
      exact nz t ht
    · obtain ⟨t,ht⟩ := intermediate_value_univ s 0 cont (show (0:ℝ)∈Icc _ _ from ⟨by linarith,h0.le⟩)
      exact nz t ht
  have aff (s : ℝ) : S.parameter s=deriv S.parameter 0*s+S.parameter 0 := by
    have df (t : ℝ) : HasDerivAt S.parameter (deriv S.parameter 0) t := const t ▸ param t
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=s)
      (fun t _ => df t) (continuous_const.intervalIntegrable _ _)
    simp at H
    linarith
  refine ⟨{ a := deriv S.parameter 0, offset := S.parameter 0, m := S.m, n := S.n,
            p := S.p, q := S.q, x := S.x, y := S.y, regular := nz 0, area := ?_,
            first := fun s => aff s ▸ S.first s, second := fun s => aff s ▸ S.second s },
    sq 0,rfl,rfl⟩
  calc
    _ = (S.m^2+S.p^2)*(S.n^2+S.q^2)-(S.m*S.n+S.p*S.q)^2 := by ring
    _ = _ := by rw [S.col₁,S.col₂,S.orthogonal,← sq 0]; ring

theorem GeometricSimilarity.unique_normalization {L b T d : ℝ} {P : ZeroTurnExpander L b}
    {Q : ZeroTurnExpander T d} (S : GeometricSimilarity P Q) (hb : b≠0) :
    S.scale=1 ∧ S.x=0 ∧ S.y=0 := by
  obtain ⟨A,asq,hx,hy⟩ := S.lifted
  obtain ⟨a4,ax,ay⟩ := A.scale_and_centre hb
  have s4 : (S.scale^2)^2=1 := by rw [← asq]; linarith only [a4]
  have u : S.scale^2=1 := by nlinarith only [s4,sq_nonneg S.scale]
  exact ⟨by nlinarith only [u,S.positive],hx ▸ ax,hy ▸ ay⟩

end ClosedSimilarity.ReflectedArc
#print axioms ClosedSimilarity.ReflectedArc.GeometricSimilarity.unique_normalization
