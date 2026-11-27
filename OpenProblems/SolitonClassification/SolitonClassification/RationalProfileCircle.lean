import SolitonClassification.RationalProfileField
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Polynomial.Roots

noncomputable section
open Complex Polynomial Set Filter
open scoped Topology Polynomial
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.RationalCurvature

def wave (w s : ℝ) : ℂ := exp (((w*s:ℝ):ℂ)*I)
def Matches (w:ℝ) (f:ℂ→ℂ) (g:ℝ→ℝ) := ∀s,f (wave w s)=(g s:ℂ)

theorem waveD (w s:ℝ) : HasDerivAt (wave w) ((w:ℂ)*I*wave w s) s := by
  have dz : HasDerivAt (fun t:ℝ=>((w*t:ℝ):ℂ)*I) ((w:ℂ)*I) s := by
    simpa only [id_eq,mul_one] using (((hasDerivAt_id s).const_mul w).ofReal_comp.mul_const I)
  apply ((Complex.hasDerivAt_exp _).comp s dz).congr_deriv
  dsimp [wave];ring

theorem along_euler {B:ℂ[X]} {f:ℂ→ℂ} {g:ℝ→ℝ} {w:ℝ}
    (r:RationalOn B f) (bn:∀s,B.eval (wave w s)≠0) (m:Matches w f g) :
    (∀s,HasDerivAt g (deriv g s) s) ∧ Matches w (euler ((w:ℂ)*I) f) (deriv g) := by
  have each (s:ℝ) : HasDerivAt g (deriv g s) s ∧ euler ((w:ℂ)*I) f (wave w s)=((deriv g s:ℝ):ℂ) := by
    have dc := ((r.differentiable (bn s)).hasDerivAt.comp s (waveD w s))
    have dm : HasDerivAt (fun u=>(g u:ℂ)) (euler ((w:ℂ)*I) f (wave w s)) s := by
      rw [show (fun u=>(g u:ℂ))=f ∘ wave w from funext (fun u=>(m u).symm)]
      apply dc.congr_deriv;unfold euler;ring
    have rr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s dm
    change HasDerivAt (fun u=>((g u:ℂ)).re) (euler ((w:ℂ)*I) f (wave w s)).re s at rr
    have realD := rr.differentiableAt.hasDerivAt
    exact ⟨realD,dm.unique realD.ofReal_comp⟩
  exact ⟨fun s=>(each s).1,fun s=>(each s).2⟩

private theorem infinite_wave {w:ℝ} (nw:w≠0) : (range (wave w)).Infinite := by
  intro finite
  have interval : Ioo (-1:ℝ) 1 ⊆ Complex.re '' range (wave w) := by
    intro x hx
    let t := Real.arccos x/w
    have wt : w*t=Real.arccos x := by dsimp [t];field_simp
    refine ⟨wave w t,⟨t,rfl⟩,?_⟩
    simp only [wave,wt,Complex.exp_mul_I,Complex.add_re,Complex.mul_re,Complex.cos_ofReal_re,
      Complex.sin_ofReal_re,Complex.sin_ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
      add_zero,Real.cos_arccos hx.1.le hx.2.le]
  exact (Set.Ioo_infinite (by norm_num : (-1:ℝ)<1)) ((finite.image _).subset interval)

theorem rational_identity_on_circle {w:ℝ} (nw:w≠0) {B:ℂ[X]} {f:ℂ→ℂ}
    (r:RationalOn B f) (bn:∀s,B.eval (wave w s)≠0) (zero:∀s,f (wave w s)=0) :
    ∀u,B.eval u≠0 → f u=0 := by
  obtain ⟨P,Q,m⟩:=r
  have sub : range (wave w)⊆{u | P.IsRoot u} := by
    rintro _ ⟨s,rfl⟩
    obtain ⟨n,e⟩:=m _ (bn s)
    exact (div_eq_zero_iff.mp (e.symm.trans (zero s))).resolve_right n
  have zz := P.eq_zero_of_infinite_isRoot ((infinite_wave nw).mono sub)
  intro u hu
  rw [(m u hu).2,zz];simp

end ClosedSimilarity.RationalCurvature
#print axioms ClosedSimilarity.RationalCurvature.rational_identity_on_circle
