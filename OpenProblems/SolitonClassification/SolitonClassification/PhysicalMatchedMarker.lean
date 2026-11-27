import SolitonClassification.MatchCertifiedSeam

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

private theorem joined_quarter {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
    (b : Ici B) (z : ChartDomain E) (n : ℕ) (eps : z.2 = c.eps b)
    (angle : c.angle b = w.angle z + n*(2*Real.pi))
    (impact : c.transverse b = w.transverse z) (Y : Phase) (t : ℝ)
    (ht : t<0) (v0 : Y 1=0) (q0 : Y 3=0)
    (readout : let y := solution 1 Y t
      regular y ∧ 4≤root y/scale y ∧ 0≤along y ∧
      RadialLayer.eps (solution 1 Y) t=z.2 ∧ height y= -H ∧
      sectionImpact y=w.transverse z ∧ hasAngle y (w.angle z)) :
    0<c.time b-t ∧ let y := solution 1 ![0,(b:ℝ),0,0] (c.time b-t)
      y 1=0 ∧ y 3=0 := by
  obtain ⟨hs,xr,xb,xa,ep,ex,hx,ix,θx⟩ := c.physical b
  obtain ⟨yr,yb,ya,ey,hy,iy,θy⟩ := readout
  let x := centreSlice b (c.time b)
  let y := solution 1 Y t
  have radius : scale x = scale y := by
    have e : 1/(scale x)^4 = 1/(scale y)^4 :=
      ex.trans ((congrArg Subtype.val eps.symm).trans ey.symm)
    rw [one_div,one_div,inv_inj] at e
    exact (pow_left_inj₀ (Real.rpow_pos_of_pos xr.1 _).le
      (Real.rpow_pos_of_pos yr.1 _).le (by decide : (4:ℕ)≠0)).mp e
  obtain ⟨sh,sl⟩ := equal_phase θx θy n angle
  have same : x=y := physical_state_injective xr yr xb yb xa ya radius sh sl
    (ix.trans (impact.trans iy.symm)) (hx.trans hy.symm)
  have hit : solution 1 ![0,(b:ℝ),0,0] (c.time b-t) = Y := by
    calc
      _ = solution 1 x (-t) := by
        rw [show c.time b-t = -t+c.time b by ring,translated_solution]
        rfl
      _ = solution 1 y (-t) := by rw [same]
      _ = Y := by rw [←translated_solution,neg_add_cancel,solution_zero]
  exact ⟨by linarith,hit ▸ v0,hit ▸ q0⟩

/-- A simultaneous phase and impact match at the same inverse physical
    radius supplies the two reflection conditions on the actual centre shot. -/
theorem matched_quarter {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
    (b : Ici B) (z : ChartDomain E) (n : ℕ) (eps : z.2 = c.eps b)
    (angle : c.angle b = w.angle z + n*(2*Real.pi))
    (impact : c.transverse b = w.transverse z) :
    ∃ l>0, let y := solution 1 ![0,(b:ℝ),0,0] l
      y 1=0 ∧ y 3=0 := by
  have ep := (c.physical b).2.2.2.2.1
  obtain ⟨Y,t,ht,hv,hq,rest⟩ := w.physical z (eps ▸ ep)
  exact ⟨_,joined_quarter c w b z n eps angle impact Y t ht hv hq rest⟩

/-- The two seam conditions hold at the sum of the first physical section
arclength and the arclength of this same certified seam realization. -/
theorem matched_quarter_at_flight {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
    (endArc : w.Flight) (b : Ici B) (z : ChartDomain E) (n : ℕ) (eps : z.2 = c.eps b)
    (angle : c.angle b = w.angle z + n*(2*Real.pi))
    (impact : c.transverse b = w.transverse z) :
    0 < endArc.length z ∧ 0<c.time b+endArc.length z ∧
      let y := solution 1 ![0,(b:ℝ),0,0] (c.time b+endArc.length z)
      y 1=0 ∧ y 3=0 := by
  have ep := (c.physical b).2.2.2.2.1
  obtain ⟨Y,ht,hv,hq,rest⟩ := endArc.realizes z (eps ▸ ep)
  refine ⟨by linarith,?_⟩
  simpa only [sub_neg_eq_add] using
    joined_quarter c w b z n eps angle impact Y (-endArc.length z) ht hv hq rest

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.matched_quarter
