import SolitonClassification.MatchCertifiedSeam

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set ReflectedArc

/-- A simultaneous phase and impact match at the same inverse physical
    radius supplies the two reflection conditions on the actual centre shot. -/
theorem matched_quarter {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
    (b : Ici B) (z : ChartDomain E) (n : ℕ) (eps : z.2 = c.eps b)
    (angle : c.angle b = w.angle z + n*(2*Real.pi))
    (impact : c.transverse b = w.transverse z) :
    ∃ l>0, let y := solution 1 ![0,(b:ℝ),0,0] l
      y 1=0 ∧ y 3=0 := by
  obtain ⟨hs,xr,xb,xa,ep,ex,hx,ix,θx⟩ := c.physical b
  obtain ⟨Y,t,ht,v0,q0,yr,yb,ya,ey,hy,iy,θy⟩ := w.physical z (eps ▸ ep)
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
  exact ⟨c.time b-t,by linarith,hit ▸ v0,hit ▸ q0⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.matched_quarter
