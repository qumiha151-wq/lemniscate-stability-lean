import LengthGrowth.ActualFlow.DefectPhysicalRate

noncomputable section
open MeasureTheory Set Filter Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

def initialLengthEnvelope : ℝ := (2*c.length 0)^4+4*(2*c.normalizedProduct 0)^2+1

theorem bending_envelope_linear (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) {t : ℝ} (ht : 0≤t) :
    c.length t^4≤c.initialLengthEnvelope*(1+t) := by
  let A := (2*c.length 0)^4
  let B := 4*(2*c.normalizedProduct 0)^2
  have an : 0≤A := by dsimp [A]; positivity
  have bn : 0≤B := by dsimp [B]; positivity
  change c.length t^4≤(A+B+1)*(1+t)
  rcases c.bending_explicit_length hf initial ht with h|h
  · have ap : c.length t^4≤A := pow_le_pow_left₀ (c.length_pos ht).le h 4
    nlinarith only [ap,bn,ht,mul_nonneg an ht,mul_nonneg bn ht]
  · change c.length t^4≤B*t at h
    nlinarith only [h,an,bn,ht,mul_nonneg an ht]

/-- Uniform entry into arbitrarily small curvature oscillation, using only
the actual physical flow and the initial defect bound. -/
theorem bending_defect_tendsto_zero (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) :
    Tendsto (fun t => 2*c.normalizedProduct t-4*Real.pi^2) atTop (𝓝 0) := by
  let D := fun t => 2*c.normalizedProduct t-4*Real.pi^2
  let M := c.initialLengthEnvelope
  let K := (8*Real.pi^2/1000000)/M
  have mp : 0<M := by dsimp [M,initialLengthEnvelope]; positivity
  have kp : 0<K := by dsimp only [K]; positivity
  have km : K*M=8*Real.pi^2/1000000 := by dsimp only [K]; field_simp
  have cD : ContinuousOn D (Ici 0) := (continuousOn_const.mul c.normalizedProduct_continuousOn).sub continuousOn_const
  have dn (s : ℝ) (hs : 0≤s) : 0≤D s := by
    have low : 2*Real.pi^2≤c.normalizedProduct s := c.sharp_energy_length hs
    dsimp only [D]; linarith only [low]
  have da (s t : ℝ) (hs : 0≤s) (st : s≤t) : D t≤D s := by
    dsimp only [D]; linarith only [c.bending_product_antitone hf initial hs (hs.trans st) st]
  have dd (s : ℝ) (hs : 0<s) : HasDerivAt D
      (2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s)) s :=
    ((c.normalizedProduct_hasDerivAt_normal hf hs).const_mul 2).sub_const (4*Real.pi^2)
  have logBound {t : ℝ} (ht : 0≤t) (dp : 0<D t) :
      D t+K*(D t)^2*Real.log (1+t)≤D 0 := by
    let A := K*(D t)^2
    let W := fun s => D s+A*Real.log (1+s)
    have cp : ∀s∈Icc 0 t, 0<1+s := fun s hs => by linarith only [hs.1]
    have cw : ContinuousOn W (Icc 0 t) := (cD.mono Icc_subset_Ici_self).add
      (continuousOn_const.mul ((continuousOn_const.add continuousOn_id).log (fun s hs => (cp s hs).ne')))
    have dw (s : ℝ) (hs : s∈Ioo 0 t) : HasDerivAt W
        (2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s)+A*(1/(1+s))) s := by
      exact (dd s hs.1).add (((((hasDerivAt_id s).const_add 1).log (by linarith only [hs.1] : 1+s≠0))).const_mul A)
    have sign (s : ℝ) (hs : s∈Ioo 0 t) :
        2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s)+A*(1/(1+s))≤0 := by
      let e := c.length s*c.dissipation s-c.energy s*c.lengthRate s
      have side := da s t hs.1.le hs.2.le
      have pos : 4*Real.pi^2<2*c.normalizedProduct s := by
        change 2*c.normalizedProduct t-4*Real.pi^2≤2*c.normalizedProduct s-4*Real.pi^2 at side
        change 0<2*c.normalizedProduct t-4*Real.pi^2 at dp
        linarith
      have cap := c.bending_sublevel_invariant hf initial hs.1.le
      have rate := c.quantitative_bending_gap hs.1.le pos cap
      change (4*Real.pi^2/1000000)*(D s)^2≤(c.length s)^4*e at rate
      have ep : 0≤e := (sub_pos.mpr (c.bending_rate_strict hs.1.le pos cap)).le
      have lc := c.bending_envelope_linear hf initial hs.1.le
      have en := mul_le_mul_of_nonneg_right lc ep
      change c.length s^4*e≤M*(1+s)*e at en
      have scale := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dp.le side 2)
        (show 0≤4*Real.pi^2/1000000 by positivity)
      have a : A≤2*e*(1+s) := by
        apply le_of_mul_le_mul_right (a:=M) _ mp
        change K*D t^2*M≤2*e*(1+s)*M
        rw [show K*D t^2*M=(K*M)*D t^2 by ring,km]
        linarith only [scale,rate,en]
      have small : A/(1+s)≤2*e := (div_le_iff₀ (cp s ⟨hs.1.le,hs.2.le⟩)).mpr a
      dsimp only [e] at small
      rw [show A*(1/(1+s))=A/(1+s) by ring]
      linarith only [small]
    have mon : AntitoneOn W (Icc 0 t) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) cw
      · rw [interior_Icc]; exact fun s hs => (dw s hs).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]; intro s hs; rw [(dw s hs).deriv]; exact sign s hs
    have bound := mon (left_mem_Icc.mpr ht) (right_mem_Icc.mpr ht) ht
    simpa only [W,A,add_zero,Real.log_one,mul_zero] using bound
  apply Metric.tendsto_atTop.mpr
  intro ε eps
  let b := K*ε^2
  have bp : 0<b := mul_pos kp (sq_pos_of_pos eps)
  let z := (D 0+1)/b
  refine ⟨Real.exp z,fun t ht => ?_⟩
  have tp := (Real.exp_pos z).trans_le ht
  change dist (D t) 0<ε
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (dn t tp.le)]
  by_contra! bad
  have bound := logBound tp.le (eps.trans_le bad)
  have log : z≤Real.log (1+t) := by
    calc z=Real.log (Real.exp z) := (Real.log_exp _).symm
         _≤_ := Real.log_le_log (Real.exp_pos _) (by linarith only [ht])
  have nn : 0≤Real.log (1+t) := Real.log_nonneg (by linarith)
  have sq := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ eps.le bad 2) kp.le) nn
  have vz : b*z=D 0+1 := by dsimp only [z]; field_simp
  have comp := mul_le_mul_of_nonneg_left log bp.le
  change b*Real.log (1+t)≤K*D t^2*Real.log (1+t) at sq
  linarith only [vz,comp,sq,bound,dn t tp.le]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.bending_defect_tendsto_zero
