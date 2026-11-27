import SolitonClassification.ForceWindingArgument

noncomputable section
open MeasureTheory Set
namespace ClosedSimilarity.ForceWinding

def stressAngle (k v : ℝ→ℝ) (s : ℝ) := (rect ((k s)^2/2) (v s)).arg
def stressMass (k v : ℝ→ℝ) (s : ℝ) := (v s)^2+(k s)^4/4
def stressAngleRate (k v F : ℝ→ℝ) (s : ℝ) := (k s)^2*F s/(2*stressMass k v s)

theorem stressAngleD {k v F : ℝ→ℝ} {s:ℝ}
    (dk : HasDerivAt k (v s) s) (dv : HasDerivAt v (F s-(k s)^3/2) s)
    (nonzero : k s≠0 ∨ v s≠0) :
    HasDerivAt (stressAngle k v) (stressAngleRate k v F s-k s) s := by
  have sl : 0<(k s)^2/2 ∨ v s≠0 := nonzero.imp (fun h=>by positivity) id
  have ns : 0<(v s)^2+(k s)^4/4 := by
    rcases nonzero with h|h <;> positivity
  have h := argumentD ((dk.pow 2).div_const 2) dv sl
  apply h.congr_deriv
  simp only [Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,stressAngleRate,stressMass]
  have den : (k s^2/2)^2 +v s^2 = v s^2+k s^4/4 := by ring
  rw [den]
  set D : ℝ := v s^2+k s^4/4 with eqD
  field_simp [ns.ne'];rw [eqD];ring

theorem stress_integral {k v F : ℝ→ℝ} {u w:ℝ} (uw : u≤w)
    (dk : ∀s,HasDerivAt k (v s) s) (dv : ∀s,HasDerivAt v (F s-(k s)^3/2) s)
    (cF : Continuous F) (nonzero : ∀s∈Icc u w,k s≠0 ∨ v s≠0) :
    (∫s in u..w,k s) = stressAngle k v u-stressAngle k v w+
      (∫s in u..w,stressAngleRate k v F s) := by
  have ck : Continuous k := continuous_iff_continuousAt.mpr fun s=>(dk s).continuousAt
  have cv : Continuous v := continuous_iff_continuousAt.mpr fun s=>(dv s).continuousAt
  have cm : Continuous (stressMass k v) := ((cv.pow 2).add ((ck.pow 4).div_const 4))
  have cd : ContinuousOn (stressAngleRate k v F) (Icc u w) :=
    ((ck.pow 2).mul cF).continuousOn.div ((continuous_const.mul cm).continuousOn) (fun s hs=>by
      obtain h|h := nonzero s hs <;> dsimp [stressMass] <;> positivity)
  have integr := cd.intervalIntegrable_of_Icc uw (μ:=volume)
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=u) (b:=w)
    (fun s hs=>stressAngleD (dk s) (dv s) (nonzero s (by rwa [uIcc_of_le uw] at hs)))
    (integr.sub (ck.intervalIntegrable ..))
  rw [intervalIntegral.integral_sub integr (ck.intervalIntegrable ..)] at eq
  linarith only [eq]

/-- Every lobe bounded by upward and downward simple inflections has the
displayed signed-turn identity. Intermediate stresses may cross either axis. -/
theorem positive_lobe {k v F : ℝ→ℝ} {u w:ℝ} (uw : u<w)
    (dk : ∀s,HasDerivAt k (v s) s) (dv : ∀s,HasDerivAt v (F s-(k s)^3/2) s)
    (cF : Continuous F) (ku : k u=0) (kw : k w=0) (vu : 0<v u) (vw : v w<0)
    (kp : ∀s∈Ioo u w, 0<k s) :
    (∫s in u..w,k s) = Real.pi+(∫s in u..w,stressAngleRate k v F s) := by
  have ns (s:ℝ) (hs:s∈Icc u w) : k s≠0 ∨ v s≠0 := by
    obtain eq|lt := hs.1.eq_or_lt
    · subst s;exact Or.inr vu.ne'
    obtain eq|lt' := hs.2.eq_or_lt
    · subst s;exact Or.inr vw.ne
    exact Or.inl (kp s ⟨lt,lt'⟩).ne'
  have start : stressAngle k v u=Real.pi/2 := Complex.arg_eq_pi_div_two_iff.mpr (by simp [ku,vu])
  have stop : stressAngle k v w= -(Real.pi/2) := Complex.arg_eq_neg_pi_div_two_iff.mpr (by simp [kw,vw])
  rw [stress_integral uw.le dk dv cF ns,start,stop];ring

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.positive_lobe
