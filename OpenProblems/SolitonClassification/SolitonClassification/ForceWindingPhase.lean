import SolitonClassification.ForceWindingArgument
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open MeasureTheory Set Function
namespace ClosedSimilarity.ForceWinding

def supportMass (F H : ℝ→ℝ) (s : ℝ) := (F s)^2+(H s)^2

def spiralAngle (a b:ℝ) (θ F H : ℝ→ℝ) (s:ℝ) :=
  θ s+(rect (F s) (H s)).arg-b/(2*a)*Real.log (supportMass F H s)

theorem spiralAngleD {a b:ℝ} {k θ F H : ℝ→ℝ} {s:ℝ} (ap : 0<a)
    (dθ : HasDerivAt θ (k s) s)
    (dF : HasDerivAt F (k s*H s-b) s) (dH : HasDerivAt H (a-k s*F s) s)
    (pos : 0≤F s) (nc : F s≠0 ∨ H s≠0) :
    HasDerivAt (spiralAngle a b θ F H) ((a^2+b^2)*F s/(a*supportMass F H s)) s := by
  have mass : 0<supportMass F H s := by
    obtain h|h := nc <;> dsimp [supportMass] <;> positivity
  have arg := argumentD dF dH (nc.imp (fun x=>lt_of_le_of_ne pos (Ne.symm x)) id)
  have dm := (dF.pow 2).add (dH.pow 2)
  have dl := (((Real.hasDerivAt_log mass.ne').comp s dm).const_mul (b/(2*a)))
  apply ((dθ.add arg).sub dl).congr_deriv
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  change _=(a^2+b^2)*F s/(a*((F s)^2+(H s)^2))
  unfold supportMass at mass ⊢
  field_simp [mass.ne',ap.ne'];ring

/-- An exact turning formula over a centre-avoiding period of a closed
similarity profile with nonnegative elastic force and arbitrary pitch. -/
theorem turn_integral {a b L:ℝ} {k θ F H : ℝ→ℝ} (ap : 0<a) (lp : 0≤L)
    (dθ : ∀s,HasDerivAt θ (k s) s)
    (dF : ∀s,HasDerivAt F (k s*H s-b) s) (dH : ∀s,HasDerivAt H (a-k s*F s) s)
    (pos : ∀s∈Icc 0 L,0≤F s) (nc : ∀s∈Icc 0 L,F s≠0 ∨ H s≠0)
    (pf : Periodic F L) (ph : Periodic H L) :
    θ L-θ 0 = ∫s in 0..L,(a^2+b^2)*F s/(a*supportMass F H s) := by
  have cf : Continuous F := continuous_iff_continuousAt.mpr (fun s=>(dF s).continuousAt)
  have ch : Continuous H := continuous_iff_continuousAt.mpr (fun s=>(dH s).continuousAt)
  have cm : Continuous (supportMass F H) := (cf.pow 2).add (ch.pow 2)
  have rate : ContinuousOn (fun s=>(a^2+b^2)*F s/(a*supportMass F H s)) (Icc 0 L) :=
    (continuous_const.mul cf).continuousOn.div (continuous_const.mul cm).continuousOn (fun s hs=>by
      obtain x|x := nc s hs <;> dsimp [supportMass] <;> positivity)
  have eq := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=L)
    (fun s hs=>spiralAngleD ap (dθ s) (dF s) (dH s)
      (pos s (by rwa [uIcc_of_le lp] at hs)) (nc s (by rwa [uIcc_of_le lp] at hs)))
    (rate.intervalIntegrable_of_Icc lp)
  have pF : F L=F 0 := by simpa using pf 0
  have pH : H L=H 0 := by simpa using ph 0
  rw [eq]
  simp only [spiralAngle,supportMass,pF,pH]
  ring

end ClosedSimilarity.ForceWinding
#print axioms ClosedSimilarity.ForceWinding.turn_integral
