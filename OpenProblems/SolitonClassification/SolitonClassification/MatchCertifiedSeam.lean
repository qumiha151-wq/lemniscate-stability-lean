import SolitonClassification.CertifiedWindingChart

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set Filter
open scoped Topology
open ReflectedArc SolitonClassification.Reflected.Rectangle

/-- The centre-side data on the common section, in physical arclength.
    Each slice is the specified global solution emanating from the centre. -/
structure CentreChart (H E b₀ : ℝ) where
  time : Ici b₀ → ℝ
  angle : Ici b₀ → ℝ
  eps : Ici b₀ → Icc (0:ℝ) E
  transverse : Ici b₀ → ℝ
  contAngle : Continuous angle
  contEps : Continuous eps
  contImpact : Continuous transverse
  winding : ∀ B ≥ b₀, ∀ v : ℝ, ∃ b : Ici b₀, B ≤ (b:ℝ) ∧ v < angle b
  small : ∀ b, |transverse b| ≤ 0.001
  physical : ∀ b : Ici b₀, let s := time b
    let x := centreSlice b s
    0<s ∧ regular x ∧ 4≤root x/scale x ∧ 0≤along x ∧
      0<(eps b:ℝ) ∧ ReflectedArc.RadialLayer.eps (solution 1 ![0,(b:ℝ),0,0]) s=eps b ∧
      height x= -H ∧ sectionImpact x=transverse b ∧ hasAngle x (angle b)

/-- The winding argument produces matching chart parameters above every
prescribed centre marker. Both chart coordinates and the winding index refer
to this same match. -/
theorem CentreChart.arbitrarily_large_matches {H E b₀ : ℝ}
    (c : CentreChart H E b₀) (w : WindingChart H E) (B : ℝ) (hB : b₀≤B) :
    ∃ b : Ici b₀, B≤(b:ℝ) ∧ ∃ z : ChartDomain E, ∃ n : ℕ,
      z.2=c.eps b ∧ c.angle b=w.angle z+n*(2*Real.pi) ∧ c.transverse b=w.transverse z := by
  let i (b : ℝ) : Ici b₀ := ⟨max b₀ b,show b₀ ≤ max b₀ b from le_max_left b₀ b⟩
  have ci : Continuous i := (continuous_const.max continuous_id).subtype_mk _
  let y := projIcc (-1/4:ℝ) 1 (by norm_num)
  let j (p : ℝ × ℝ) : ChartDomain E := (y p.2,c.eps (i p.1))
  have cj : Continuous j := (continuous_projIcc.comp continuous_snd).prodMk
    (c.contEps.comp (ci.comp continuous_fst))
  obtain ⟨M,hm⟩ := w.bounded
  have p : 0<2*Real.pi := by positivity
  have cycle := unbounded_matching_markers b₀ (-1/4) 1 (2*Real.pi) M (by norm_num) p
    (fun b => c.angle (i b)) (fun b => c.transverse (i b)) (w.angle ∘ j) (w.transverse ∘ j)
    (fun B hB v => by
      obtain ⟨b,bb,h⟩ := c.winding B hB v
      have ib : i (b:ℝ) = b := Subtype.ext (max_eq_right (show b₀ ≤ (b:ℝ) from b.property))
      exact ⟨b,bb,by simpa only [ib] using h⟩)
    (fun _ _ _ _ => (((c.contAngle.comp (ci.comp continuous_fst)).sub
      (w.continuous_angle.comp cj)).prodMk ((w.continuous_transverse.comp cj).sub
      (c.contImpact.comp (ci.comp continuous_fst)))).continuousOn)
    (fun b _ z _ => hm (j (b,z)))
    (fun b _ => by
      have lo := w.left (c.eps (i b))
      have s := (abs_le.mp (c.small (i b))).1
      have pos : y (-1/4) = leftCurvature := Subtype.ext (by simp [y,leftCurvature])
      change w.transverse (y (-1/4),_) < _
      rw [pos]; linarith)
    (fun b _ => by
      have hi := w.right (c.eps (i b))
      have s := (abs_le.mp (c.small (i b))).2
      have pos : y 1 = rightCurvature := Subtype.ext (by simp [y,rightCurvature])
      change _ < w.transverse (y 1,_)
      rw [pos]; linarith)
  obtain ⟨b,bb,k,_,n,angle,hit⟩ := cycle B hB
  exact ⟨i b,bb.trans (le_max_right _ _),j (b,k),n,rfl,angle,hit⟩

theorem CentreChart.closes {H E b₀ : ℝ} (c : CentreChart H E b₀) (w : WindingChart H E) :
    ∀ B ≥ b₀, ∃ b ≥ B, ∃ L > (0:ℝ), Nonempty (ZeroTurnExpander L b) := by
  intro B hB
  obtain ⟨q,hq,z,n,eps,angle,hit⟩ := c.arbitrarily_large_matches w B hB
  obtain ⟨hs,xr,xb,xa,ep,ex,hx,ix,θx⟩ := c.physical q
  obtain ⟨Y,t,ht,v0,q0,yr,yb,ya,ey,hy,iy,θy⟩ := w.physical z (eps ▸ ep)
  let x := centreSlice q (c.time q)
  let f := solution 1 Y t
  have hscale : scale x = scale f := by
    have e : 1/(scale x)^4 = 1/(scale f)^4 := ex.trans ((congrArg Subtype.val eps.symm).trans ey.symm)
    rw [one_div,one_div,inv_inj] at e
    have sx : 0 < scale x := Real.rpow_pos_of_pos xr.1 _
    have sy : 0 < scale f := Real.rpow_pos_of_pos yr.1 _
    exact (pow_left_inj₀ sx.le sy.le (by decide : (4:ℕ)≠0)).mp e
  obtain ⟨U,w'⟩ := equal_phase θx θy n angle
  have closed := exact_physical_matching (b:=(q:ℝ)) hs ht v0 q0 xr yr xb yb xa ya
    hscale U w' (ix.trans (hit.trans iy.symm)) (hx.trans hy.symm)
  exact ⟨q,hq,4*(c.time q-t),by linarith,closed⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.CentreChart.closes
