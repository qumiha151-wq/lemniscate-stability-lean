import SolitonClassification.LowBendingProfileRigidity

noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve
open MeasureTheory
variable (c : ClosedUnitFrenetCurve)

/-- The centered support law can be tested about any point in the plane. -/
def lowBendingRecenter (x₀ y₀ : ℝ) : ClosedUnitFrenetCurve :=
  { c with
    x:=fun s => c.x s-x₀, y:=fun s => c.y s-y₀
    dx:=fun s => (c.dx s).sub_const x₀, dy:=fun s => (c.dy s).sub_const y₀
    periodic_x:=fun s => congrArg (fun z => z-x₀) (c.periodic_x s)
    periodic_y:=fun s => congrArg (fun z => z-y₀) (c.periodic_y s) }

/-- The actual constant-curvature curve, in its own arclength coordinate,
is a translated parametrized circle with the signed angular speed K. -/
theorem low_bending_circle_parametrization (K : ℝ) (kn : K≠0) (hk : ∀s,c.k s=K) :
    ∃ O A : ℂ, A≠0 ∧ ∀s:ℝ, (c.x s:ℂ)+(c.y s:ℂ)*Complex.I=
      O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  let p := c.lowBendingCurve
  let k : ℂ := (K:ℂ)*Complex.I
  have nz : k≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr kn) Complex.I_ne_zero
  have nt : p.tangent 0≠0 := by
    intro h
    have n := p.tangent_unit 0
    simp [h] at n
  let A := p.tangent 0/k
  refine ⟨p.curve 0-A,A,div_ne_zero nt nz,?_⟩
  intro s
  have mean : (∫ z in 0..s,p.curvature z)=K*s := by
    change (∫ z in 0..s,c.k z)=K*s
    simp_rw [hk]
    simp [mul_comm]
  have tang := p.tangent_eq_exp_integral_curvature 0 s
  rw [mean] at tang
  have dh (z : ℝ) : HasDerivAt (fun t => p.curve t-p.tangent t/k) 0 z := by
    apply ((p.curve_deriv z).sub ((p.tangent_deriv z).div_const k)).congr_deriv
    have eq : p.curvature z=K := hk z
    rw [eq]
    have prod : (K:ℂ)*(Complex.I*p.tangent z)=p.tangent z*k := by dsimp only [k]; ring
    rw [prod]
    simp [nz]
  have f := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=s)
    (fun z _ => dh z) (intervalIntegrable_const (c:=(0:ℂ)))
  rw [intervalIntegral.integral_zero] at f
  change (0:ℂ)= (p.curve s-p.tangent s/k)-(p.curve 0-p.tangent 0/k) at f
  rw [tang] at f
  change p.curve s=(p.curve 0-p.tangent 0/k)+(p.tangent 0/k)*Complex.exp (((K*s:ℝ):ℂ)*Complex.I)
  linear_combination -f

/-- Independent classification of the complete low-bending sublevel for
closed dilating/rotating profiles, allowing any similarity center. -/
theorem low_bending_only_singly_covered_circles (a b x₀ y₀ : ℝ)
    (shape : ∀s, c.positionForce s=
      -a*(-(c.x s-x₀)*c.ty s+(c.y s-y₀)*c.tx s)-
       b*((c.x s-x₀)*c.tx s+(c.y s-y₀)*c.ty s))
    (cap : c.period*(∫ s in 0..c.period,c.k s^2)≤4*Real.pi^2+36) :
    ∃ (K : ℝ) (O A : ℂ), (K*c.period=2*Real.pi ∨ K*c.period= -(2*Real.pi)) ∧
      A≠0 ∧ ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*Complex.I=O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  let g := c.lowBendingRecenter x₀ y₀
  have law (s : ℝ) : g.force s= -a*g.normalSupport s-b*g.tangentSupport s := by
    have hs := shape s
    rw [c.positionForce_eq] at hs
    exact hs
  obtain ⟨K,tr,hk⟩ := g.low_bending_similarity_rigidity a b law cap
  have kn : K≠0 := by
    intro eq
    rcases tr with pos|neg <;> rw [eq,zero_mul] at * <;> linarith [Real.pi_pos]
  obtain ⟨O,A,nz,rep⟩ := c.low_bending_circle_parametrization K kn hk
  exact ⟨K,O,A,tr,nz,rep⟩

/-- The same conclusion directly from an arbitrary infinitesimal similarity
generator, including an arbitrary constant translation. -/
theorem low_bending_all_similarity_generators (a b vx vy : ℝ)
    (law : ∀s, c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s)
    (cap : c.period*(∫ s in 0..c.period,c.k s^2)≤4*Real.pi^2+36) :
    ∃ (K : ℝ) (O A : ℂ), (K*c.period=2*Real.pi ∨ K*c.period= -(2*Real.pi)) ∧
      A≠0 ∧ ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*Complex.I=O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg a,sq_nonneg b]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s => by
      simpa [ha,hb] using law s))
  · let x₀ := (-a*vx-b*vy)/(a^2+b^2)
    let y₀ := (b*vx-a*vy)/(a^2+b^2)
    apply c.low_bending_only_singly_covered_circles a b x₀ y₀ _ cap
    intro s
    rw [law]
    dsimp only [normalSupport,tangentSupport,x₀,y₀]
    field_simp [zero]
    ring

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.low_bending_all_similarity_generators
