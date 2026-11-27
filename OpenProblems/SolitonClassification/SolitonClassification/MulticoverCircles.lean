import SolitonClassification.LowBendingCircles
import SolitonClassification.MulticoverSlice

noncomputable section
open Set MeasureTheory
namespace ClosedSimilarity.ClosedUnitFrenetCurve
variable (c : ClosedUnitFrenetCurve)

/-- An actual similarity law makes the normalized bending product stationary.
The strict spatial bound forces equality in the mean-curvature inequality. -/
theorem multicover_curvature_rigidity (a b : ℝ)
    (shape : ∀s, c.force s= -a*c.normalSupport s-b*c.tangentSupport s)
    (six : 6≤|∫ s in 0..c.period,c.k s|)
    (cap : Real.sqrt (c.period*(∫ s in 0..c.period,c.k s^2))≤|∫ s in 0..c.period,c.k s|+3/5) :
    ∃ K : ℝ, K*c.period=(∫s in 0..c.period,c.k s) ∧ ∀s,c.k s=K := by
  let p := c.lowBendingCurve
  let z := c.lowBendingSupport a b shape
  let L := c.period
  let S := ∫s in 0..L,c.k s
  let B := ∫s in 0..L,c.k s^2
  have lp : 0<L := c.period_pos
  have pos : 0≤L*B := mul_nonneg lp.le (intervalIntegral.integral_nonneg_of_forall lp.le (fun s=>sq_nonneg _))
  have pe : 2*p.energy*p.period=L*B := by
    change 2*(B/2)*L=L*B
    ring
  have bo : z.bending=2*p.energy := by
    change B=2*(B/2)
    ring
  have fs : ∀s,p.force s=z.force s := shape
  have j : (∫s in 0..p.period,p.curvature s*p.force s)=a*p.period := by
    simp_rw [fs]
    exact z.integral_k_force
  have ds : p.dissipation=a*p.energy := by
    unfold LowBending.ClosedFrenetCurve.dissipation
    simp_rw [fs]
    change z.forceSquare=a*p.energy
    rw [z.forceSquare_eq,bo]
    ring
  have rates := p.multi_bending_slice
  change |S|≤Real.sqrt (2*p.energy*p.period) ∧
    (6≤|S| → |S|<Real.sqrt (2*p.energy*p.period) → Real.sqrt (2*p.energy*p.period)≤|S|+3/5 →
      p.energy*(∫s in 0..p.period,p.curvature s*p.force s)<p.period*p.dissipation) at rates
  rw [pe] at rates
  have eq : |S|=Real.sqrt (L*B) := by
    apply le_antisymm rates.1
    by_contra! greater
    have loss := rates.2 six greater cap
    rw [j,ds] at loss
    linarith only [loss]
  have floor : L*B=S^2 := by
    have h := Real.sq_sqrt pos
    rw [←eq,sq_abs] at h
    exact h.symm
  let K := S/L
  have mean : L*K=S := by dsimp [K];field_simp [lp.ne']
  have split := (LowBending.BendingSublevel.centered_moments c.continuous_k mean.symm).2.1
  change B=L*K^2+(∫s in 0..L,(c.k s-K)^2) at split
  have zero : (∫s in 0..L,(c.k s-K)^2)=0 := by
    apply (mul_eq_zero.mp (show L*(∫s in 0..L,(c.k s-K)^2)=0 by
      rw [←mean] at floor
      linarith only [floor,congrArg (fun x : ℝ=>L*x) split])).resolve_left lp.ne'
  have on := ClosedSimilarity.continuous_nonneg_zero_of_integral_zero lp
    ((c.continuous_k.sub continuous_const).pow 2) (fun s _=>sq_nonneg (c.k s-K)) zero
  refine ⟨K,(mul_comm K L).trans mean,?_⟩
  intro s
  obtain ⟨t,ht,h⟩ := c.periodic_k.exists_mem_Ico₀ c.period_pos s
  rw [h]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (on t ⟨ht.1,ht.2.le⟩))

/-- At any nonzero signed turning number the only self-similar solutions in
this explicit sublevel are circles with exactly that signed covering number.
Translations, dilations and rotations are all allowed in the generator. -/
theorem multicover_all_similarity_generators (a b vx vy : ℝ) {n : ℤ} (hn : n≠0)
    (law : ∀s, c.positionForce s= -a*c.normalSupport s-b*c.tangentSupport s+
      vx*c.ty s-vy*c.tx s)
    (turn : (∫s in 0..c.period,c.k s)=(n:ℝ)*(2*Real.pi))
    (cap : Real.sqrt (c.period*(∫s in 0..c.period,c.k s^2))≤|(n:ℝ)| * (2*Real.pi)+3/5) :
    ∃ (K : ℝ) (O A : ℂ), K*c.period=(n:ℝ)*(2*Real.pi) ∧ A≠0 ∧
      ∀s:ℝ,(c.x s:ℂ)+(c.y s:ℂ)*Complex.I=O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  by_cases zero : a^2+b^2=0
  · have ha : a=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    have hb : b=0 := by nlinarith only [zero,sq_nonneg b,sq_nonneg a]
    exact False.elim (c.no_closed_translator_position_force vx vy (fun s=>by simpa [ha,hb] using law s))
  let x₀ := (-a*vx-b*vy)/(a^2+b^2)
  let y₀ := (b*vx-a*vy)/(a^2+b^2)
  let g := c.lowBendingRecenter x₀ y₀
  have shape (s : ℝ) : g.force s= -a*g.normalSupport s-b*g.tangentSupport s := by
    have eq := law s
    rw [c.positionForce_eq] at eq
    rw [show g.force s=c.force s from rfl,eq]
    dsimp only [normalSupport,tangentSupport,g,lowBendingRecenter,x₀,y₀]
    field_simp [zero]
    ring
  have ab : |∫s in 0..g.period,g.k s|=|(n:ℝ)| * (2*Real.pi) := by
    change |∫s in 0..c.period,c.k s|=_
    rw [turn,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
  have mag : (1:ℝ)≤|(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have six : 6≤|∫s in 0..g.period,g.k s| := by
    rw [ab]
    nlinarith only [mul_le_mul_of_nonneg_right mag (by positivity : 0≤2*Real.pi),Real.pi_gt_three]
  obtain ⟨K,m,hk⟩ := g.multicover_curvature_rigidity a b shape six (ab.symm ▸ cap)
  have out : K*c.period=(n:ℝ)*(2*Real.pi) := m.trans turn
  have kn : K≠0 := by
    intro kz
    exact (mul_ne_zero (Int.cast_ne_zero.mpr hn) (by positivity : 2*Real.pi≠0)) (by simpa [kz] using out.symm)
  obtain ⟨O,A,nz,eq⟩ := c.low_bending_circle_parametrization K kn hk
  exact ⟨K,O,A,out,nz,eq⟩

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.multicover_all_similarity_generators

