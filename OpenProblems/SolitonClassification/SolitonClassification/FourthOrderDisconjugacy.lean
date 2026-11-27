import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Set
namespace SolitonClassification.CrossingMultiplicity

/-- Four distinct ordered zeros, with both boundary points allowed. -/
def FourZeros (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ s t u v : ℝ, a ≤ s ∧ s < t ∧ t < u ∧ u < v ∧ v ≤ b ∧
    f s = 0 ∧ f t = 0 ∧ f u = 0 ∧ f v = 0

private theorem rolle {f g : ℝ → ℝ} {a b l r : ℝ} (c : ContinuousOn f (Icc a b))
    (d : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x)
    (al : a ≤ l) (lr : l < r) (rb : r ≤ b) (hl : f l = 0) (hr : f r = 0) :
    ∃ x, l < x ∧ x < r ∧ g x = 0 := by
  obtain ⟨x,hx,hg⟩ := exists_hasDerivAt_eq_zero lr (c.mono (Icc_subset_Icc al rb)) (hl.trans hr.symm)
    (fun x hx => d x ⟨al.trans_lt hx.1,hx.2.trans_le rb⟩)
  exact ⟨x,hx.1,hx.2,hg⟩

private theorem bound_from_zero {f g : ℝ → ℝ} {a b M z : ℝ} (hz : z ∈ Icc a b)
    (fz : f z = 0) (c : ContinuousOn f (Icc a b))
    (d : ∀ x ∈ Ioo a b, HasDerivAt f (g x) x) (mp : 0 ≤ M)
    (bound : ∀ x ∈ Icc a b, |g x| ≤ M) : ∀ x ∈ Icc a b, |f x| ≤ M*(b-a) := by
  have diff {l r : ℝ} (al : a ≤ l) (lr : l < r) (rb : r ≤ b) :
      |f r-f l| ≤ M*(b-a) := by
    obtain ⟨u,hu,eq⟩ := exists_hasDerivAt_eq_slope f g lr (c.mono (Icc_subset_Icc al rb))
      (fun u hu => d u ⟨al.trans_lt hu.1,hu.2.trans_le rb⟩)
    rw [← (eq_div_iff (sub_ne_zero.mpr lr.ne')).mp eq,abs_mul,abs_of_nonneg (sub_nonneg.mpr lr.le)]
    exact mul_le_mul (bound u ⟨al.trans hu.1.le,hu.2.le.trans rb⟩) (by linarith)
      (sub_nonneg.mpr lr.le) mp
  intro x hx
  rcases lt_trichotomy x z with h | h | h
  · simpa only [fz,zero_sub,abs_neg] using diff hx.1 h hz.2
  · rw [h,fz,abs_zero]
    exact mul_nonneg mp (sub_nonneg.mpr (hz.1.trans hz.2))
  · simpa only [fz,sub_zero] using diff hz.1 h hx.2

/-- A scalar fourth-order differential inequality on a short interval is
    disconjugate: four distinct zeros force the whole function to vanish.
    The fourth derivative needs only the displayed pointwise bound. -/
theorem eq_zero_of_four_zeros {f g h j k : ℝ → ℝ} {a b C₀ C₁ C₂ C₃ : ℝ}
    (cf : ContinuousOn f (Icc a b)) (cg : ContinuousOn g (Icc a b))
    (ch : ContinuousOn h (Icc a b)) (cj : ContinuousOn j (Icc a b))
    (df : ∀x∈Ioo a b, HasDerivAt f (g x) x) (dg : ∀x∈Ioo a b, HasDerivAt g (h x) x)
    (dh : ∀x∈Ioo a b, HasDerivAt h (j x) x) (dj : ∀x∈Ioo a b, HasDerivAt j (k x) x)
    (p₀ : 0 ≤ C₀) (p₁ : 0 ≤ C₁) (p₂ : 0 ≤ C₂) (p₃ : 0 ≤ C₃)
    (bound : ∀ x ∈ Icc a b, |k x| ≤ C₀*|f x| + C₁*|g x| + C₂*|h x| + C₃*|j x|)
    (short : C₀*(b-a)^4 + C₁*(b-a)^3 + C₂*(b-a)^2 + C₃*(b-a) < 1)
    (zeros : FourZeros f a b) : ∀ x ∈ Icc a b, f x = 0 := by
  obtain ⟨s,t,u,v,as',st,tu,uv,vb,fs,ft,fu,fv⟩ := zeros
  have ab : a ≤ b := as'.trans (st.le.trans (tu.le.trans (uv.le.trans vb)))
  obtain ⟨x,sx,xt,gx⟩ := rolle cf df as' st (tu.le.trans (uv.le.trans vb)) fs ft
  obtain ⟨y,ty,yu,gy⟩ := rolle cf df (as'.trans st.le) tu (uv.le.trans vb) ft fu
  obtain ⟨z,uz,zv,gz⟩ := rolle cf df (as'.trans (st.le.trans tu.le)) uv vb fu fv
  obtain ⟨m,xm,my,hm⟩ := rolle cg dg (as'.trans sx.le) (xt.trans ty) (yu.le.trans (uv.le.trans vb)) gx gy
  obtain ⟨n,yn,nz,hn⟩ := rolle cg dg (as'.trans (st.le.trans ty.le)) (yu.trans uz) (zv.le.trans vb) gy gz
  obtain ⟨w,mw,wn,jw⟩ := rolle ch dh (by linarith) (my.trans yn) (by linarith) hm hn
  let F := fun r => C₀*|f r| + C₁*|g r| + C₂*|h r| + C₃*|j r|
  have cF : ContinuousOn F (Icc a b) :=
    (((continuousOn_const.mul cf.abs).add (continuousOn_const.mul cg.abs)).add
      (continuousOn_const.mul ch.abs)).add (continuousOn_const.mul cj.abs)
  obtain ⟨r,hr,maximal⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr ab) cF
  let M := F r
  let D := b-a
  have dp : 0 ≤ D := sub_nonneg.mpr ab
  have mp : 0 ≤ M := (abs_nonneg (k r)).trans (bound r hr)
  have bk (q : ℝ) (hq : q∈Icc a b) : |k q| ≤ M := (bound q hq).trans (maximal hq)
  have bj := bound_from_zero (show w∈Icc a b from ⟨by linarith,by linarith⟩) jw cj dj mp bk
  have bh := bound_from_zero (show m∈Icc a b from ⟨by linarith,by linarith⟩) hm ch dh (mul_nonneg mp dp) bj
  have bg := bound_from_zero (show x∈Icc a b from ⟨by linarith,by linarith⟩) gx cg dg
    (mul_nonneg (mul_nonneg mp dp) dp) bh
  have bf := bound_from_zero (show s∈Icc a b from ⟨as',by linarith⟩) fs cf df
    (mul_nonneg (mul_nonneg (mul_nonneg mp dp) dp) dp) bg
  have contraction : M ≤ M*(C₀*D^4 + C₁*D^3 + C₂*D^2 + C₃*D) := calc
    M ≤ C₀*(M*D*D*D*D) + C₁*(M*D*D*D) + C₂*(M*D*D) + C₃*(M*D) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left (bf r hr) p₀)
        (mul_le_mul_of_nonneg_left (bg r hr) p₁))
        (mul_le_mul_of_nonneg_left (bh r hr) p₂)) (mul_le_mul_of_nonneg_left (bj r hr) p₃)
    _ = _ := by ring
  have zero : M = 0 := by
    by_contra nz
    have impossible := mul_lt_mul_of_pos_left short (lt_of_le_of_ne mp (Ne.symm nz))
    change M*(C₀*D^4+C₁*D^3+C₂*D^2+C₃*D) < M*1 at impossible
    linarith
  intro q hq
  have hq' := bf q hq
  rw [zero] at hq'
  simpa using hq'

/-- The variable-coefficient equation version. No regularity of the
    coefficient functions beyond their pointwise bounds is assumed. -/
theorem linear_ode_eq_zero_of_four_zeros {f g h j k a₀ a₁ a₂ a₃ : ℝ → ℝ} {a b C₀ C₁ C₂ C₃ : ℝ}
    (cf : ContinuousOn f (Icc a b)) (cg : ContinuousOn g (Icc a b))
    (ch : ContinuousOn h (Icc a b)) (cj : ContinuousOn j (Icc a b))
    (df : ∀x∈Ioo a b, HasDerivAt f (g x) x) (dg : ∀x∈Ioo a b, HasDerivAt g (h x) x)
    (dh : ∀x∈Ioo a b, HasDerivAt h (j x) x) (dj : ∀x∈Ioo a b, HasDerivAt j (k x) x)
    (p₀ : 0 ≤ C₀) (p₁ : 0 ≤ C₁) (p₂ : 0 ≤ C₂) (p₃ : 0 ≤ C₃)
    (equation : ∀x∈Icc a b, k x = a₀ x*f x + a₁ x*g x + a₂ x*h x + a₃ x*j x)
    (coeff : ∀x∈Icc a b, |a₀ x| ≤ C₀ ∧ |a₁ x| ≤ C₁ ∧ |a₂ x| ≤ C₂ ∧ |a₃ x| ≤ C₃)
    (short : C₀*(b-a)^4 + C₁*(b-a)^3 + C₂*(b-a)^2 + C₃*(b-a) < 1)
    (zeros : FourZeros f a b) : ∀ x ∈ Icc a b, f x = 0 := by
  apply eq_zero_of_four_zeros cf cg ch cj df dg dh dj p₀ p₁ p₂ p₃ _ short zeros
  intro x hx
  rw [equation x hx]
  obtain ⟨h₀,h₁,h₂,h₃⟩:=coeff x hx
  have piece {v c C : ℝ} (h : |c|≤C) : |c*v|≤C*|v| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
  exact (abs_add_le ..).trans <| add_le_add ((abs_add_le ..).trans <| add_le_add
     ((abs_add_le ..).trans (add_le_add (piece h₀) (piece h₁))) (piece h₂)) (piece h₃)

end SolitonClassification.CrossingMultiplicity
#print axioms SolitonClassification.CrossingMultiplicity.eq_zero_of_four_zeros
#print axioms SolitonClassification.CrossingMultiplicity.linear_ode_eq_zero_of_four_zeros
