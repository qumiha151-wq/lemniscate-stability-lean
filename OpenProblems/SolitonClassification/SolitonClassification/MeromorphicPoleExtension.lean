import SolitonClassification.MeromorphicPoleResonance

noncomputable section
open Complex Polynomial Filter Set
open scoped Topology Polynomial
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

private theorem six_values (c d e f g h:ℂ) :
    let P:=sixTerm c d e f g h
    P.coeff 0=c ∧ P.coeff 1=d ∧ P.coeff 2=e ∧ P.coeff 3=f ∧ P.coeff 4=g ∧ P.coeff 5=h := by
  simp [sixTerm,coeff_add,coeff_X_mul,coeff_C]

private theorem defect_four {c g h:ℂ} (root:c^2= -9) : X^4∣polyDefect (sixTerm c 0 0 0 g h) := by
  let P:=sixTerm c 0 0 0 g h
  obtain ⟨z0,z1,z2,z3,_,_⟩:=six_values c 0 0 0 g h
  change P.coeff 0=c at z0
  change P.coeff 1=0 at z1
  change P.coeff 2=0 at z2
  change P.coeff 3=0 at z3
  change X^4∣polyDefect P
  apply X_pow_dvd_iff.mpr
  intro j hj
  interval_cases j <;>
    simp only [polyDefect,coeff_add,coeff_polyStep,coeff_C_mul,pow_succ,pow_zero,one_mul,
      coeff_product0,coeff_product1,coeff_product2,coeff_product3,z0,z1,z2,z3] <;>
    norm_num;linear_combination (2/9)*c*root

private theorem leading_remainder {k:ℂ→ℂ} {x c g h:ℂ}
    (app:Approx x (-1) k (sixTerm c 0 0 0 g h)) :
    ∃R:ℂ→ℂ,AnalyticAt ℂ R x ∧ k=ᶠ[𝓝[≠] x] fun z=>c/(z-x)+(z-x)^3*R z := by
  obtain ⟨r,ar,eq⟩:=app
  refine ⟨fun z=>g+(z-x)*h+(z-x)^2*r z,by fun_prop,?_⟩
  filter_upwards [eq,eventually_mem_nhdsWithin] with z e nz
  have diff := sub_ne_zero.mpr nz
  rw [e]
  simp only [sixTerm,eval_add,eval_mul,eval_C,eval_X,zero_add,zpow_neg_one]
  field_simp;ring

/-- For the ordinary complex arclength equation with a positive real dilation
coefficient, every meromorphic pole is simple with square residue -9. There
are no constant, linear or quadratic terms in its regular Laurent part. -/
theorem pole_expansion {a b:ℝ} (ap:0<a) {x:ℂ} {k:ℂ→ℂ} (mk:MeromorphicAt k x)
    {n:ℤ} (ord:meromorphicOrderAt k x=(n:WithTop ℤ)) (pole:n<0)
    (germ:ordinaryResidual a b k=ᶠ[𝓝[≠] x] fun _=>0) :
    n= -1 ∧ ∃c:ℂ,c^2= -9 ∧ Jet k x (-1) c ∧
      (∃R:ℂ→ℂ,AnalyticAt ℂ R x ∧ k=ᶠ[𝓝[≠] x] fun z=>c/(z-x)+(z-x)^3*R z) ∧
      ∃G:ℂ→ℂ,AnalyticAt ℂ G x ∧ G x=0 ∧
        (fun z=>deriv (deriv k) z+2*(k z)^3/9)=ᶠ[𝓝[≠] x] G := by
  obtain ⟨c,nc,j⟩:=Jet.of_order mk ord
  obtain ⟨single,root⟩:=pole_order_and_symbol j nc pole germ
  subst n
  obtain ⟨d,e,f,g,h,approx⟩:=sixTerm_of_jet j
  have r := resonance_of_divides ((residual_approx (a:=(a:ℂ)) (b:=(b:ℂ)) approx).dvd_of_zero germ)
  obtain ⟨c0,c1,c2,c3,c4,c5⟩:=six_values c d e f g h
  rw [c0,c1,c2,c3,c4,c5] at r
  obtain ⟨root9,dz,ez,fz⟩ := pole_coefficients ap nc root r
  subst d;subst e;subst f
  obtain ⟨G,aG,zG,eqG⟩ := (defect_approx approx).extension_of_dvd (defect_four root9)
  refine ⟨rfl,c,root9,j,leading_remainder approx,G,aG,zG,?_⟩
  filter_upwards [eqG] with z eq
  calc
    _ = deriv (deriv k) z+(2/9:ℂ)*k z^3 := by ring
    _ = _ := eq

theorem residue_values {c:ℂ} (sq:c^2= -9) : c=3*I ∨ c= -(3*I) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [sq,mul_pow,I_sq];norm_num

theorem pole_extension {a b:ℝ} (ap:0<a) {x:ℂ} {k:ℂ→ℂ} (mk:MeromorphicAt k x)
    {n:ℤ} (ord:meromorphicOrderAt k x=(n:WithTop ℤ)) (pole:n<0)
    (germ:ordinaryResidual a b k=ᶠ[𝓝[≠] x] fun _=>0) :
    n= -1 ∧ ∃c:ℂ,c^2= -9 ∧ Jet k x (-1) c ∧
      ∃G:ℂ→ℂ,AnalyticAt ℂ G x ∧ G x=0 ∧
        (fun z=>deriv (deriv k) z+2*(k z)^3/9)=ᶠ[𝓝[≠] x] G := by
  obtain ⟨sn,c,c9,j,_,G,hG,zG,eq⟩:=pole_expansion ap mk ord pole germ
  exact ⟨sn,c,c9,j,G,hG,zG,eq⟩

end ClosedSimilarity.MeromorphicCurvature
#print axioms ClosedSimilarity.MeromorphicCurvature.pole_expansion
#print axioms ClosedSimilarity.MeromorphicCurvature.pole_extension
