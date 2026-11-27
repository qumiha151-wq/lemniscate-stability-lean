import LengthGrowth.ActualFlow.MulticoverWinding
import LengthGrowth.ActualFlow.DefectAttraction
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem multicover_envelope (hf : c.IsNormalFEF)
    (turn : 6≤c.initialAbsoluteTurning) (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) {t : ℝ} (ht : 0≤t) :
    c.length t^4≤c.initialLengthEnvelope*(1+t) := by
  let A := (2*c.length 0)^4
  let B := 4*(2*c.normalizedProduct 0)^2
  have an : 0≤A := by dsimp [A]; positivity
  have bn : 0≤B := by dsimp [B]; positivity
  change c.length t^4≤(A+B+1)*(1+t)
  rcases c.multicover_explicit_length hf turn initial ht with h|h
  · have ap : c.length t^4≤A := pow_le_pow_left₀ (c.length_pos ht).le h 4
    nlinarith only [ap,bn,ht,mul_nonneg an ht,mul_nonneg bn ht]
  · change c.length t^4≤B*t at h
    nlinarith only [h,an,bn,ht,mul_nonneg an ht]


def multicoverOscillation (t:ℝ):=2*c.normalizedProduct t-c.initialAbsoluteTurning^2

theorem multicover_floor {t:ℝ} (ht:0≤t) : c.initialAbsoluteTurning≤c.rootBending t := by
  unfold initialAbsoluteTurning
  rw [←c.signedCurvature_eq_initial ht]
  exact (c.regularPositionAt ht).multicover_slice.1

theorem multicover_gap (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) {s : ℝ} (hs : 0<s) :
    c.initialAbsoluteTurning^4/1000*c.multicoverOscillation s≤
      c.length s^4*(c.length s*c.dissipation s-c.energy s*c.lengthRate s) := by
  have h := (c.regularPositionAt hs.le).multicover_dissipation
  change |materialSignedCurvature (c.position s) c.period|≤c.rootBending s ∧
    (6≤|materialSignedCurvature (c.position s) c.period| → |materialSignedCurvature (c.position s) c.period|<c.rootBending s →
    c.rootBending s≤|materialSignedCurvature (c.position s) c.period|+3/5 →
    |materialSignedCurvature (c.position s) c.period|^4/1000*(c.rootBending s^2-|materialSignedCurvature (c.position s) c.period|^2)<
    c.length s^4*(c.length s*c.dissipation s-c.energy s*c.lengthRate s)) at h
  rw [c.signedCurvature_eq_initial hs.le] at h
  rw [←show c.initialAbsoluteTurning=|materialSignedCurvature (c.position 0) c.period| from rfl] at h
  unfold multicoverOscillation
  rw [←c.rootBending_sq hs.le]
  rcases lt_or_eq_of_le h.1 with hi|eq
  · exact (h.2 turn hi (c.multicover_sublevel_invariant hf turn initial hs.le)).le
  rw [eq,sub_self,mul_zero]
  have nonpos:=(c.multicover_product_antitone hf turn initial).derivWithin_nonpos (x:=s)
  rw [derivWithin_of_mem_nhds (Ici_mem_nhds hs),(c.normalizedProduct_hasDerivAt_normal hf hs).deriv] at nonpos
  exact mul_nonneg (by positivity) (by linarith only [nonpos])

def multicoverDecayExponent := c.initialAbsoluteTurning^4/(500*c.initialLengthEnvelope)

theorem multicover_power_decay (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) {t:ℝ} (ht:0≤t) :
    c.multicoverOscillation t*(1+t)^c.multicoverDecayExponent≤c.multicoverOscillation 0 := by
  let D:=c.multicoverOscillation
  let K:=c.multicoverDecayExponent
  let B:=c.initialLengthEnvelope
  have bp : 0<B:=by dsimp [B,initialLengthEnvelope];positivity
  have kb : K*B=c.initialAbsoluteTurning^4/500:=by change c.initialAbsoluteTurning^4/(500*B)*B=_;field_simp [bp.ne']
  let W:=fun s=>D s*(1+s)^K
  have pos {s:ℝ} (hs:0≤s):0<1+s:=by linarith
  have contD : ContinuousOn D (Ici 0):=(continuousOn_const.mul c.normalizedProduct_continuousOn).sub continuousOn_const
  have cw : ContinuousOn W (Ici 0):=contD.mul ((continuousOn_const.add continuousOn_id).rpow_const (fun _ hs=>Or.inl (pos hs).ne'))
  let e:=fun s=>c.length s*c.dissipation s-c.energy s*c.lengthRate s
  have dw (s:ℝ) (hs:0<s) : HasDerivAt W ((-2*e s)*(1+s)^K+D s*(K*(1+s)^(K-1))) s:=by
    have d : HasDerivAt D (-2*e s) s:=by
      apply (((c.normalizedProduct_hasDerivAt_normal hf hs).const_mul 2).sub_const (c.initialAbsoluteTurning^2)).congr_deriv
      dsimp [e];ring
    have power:=((hasDerivAt_id s).const_add 1).rpow_const (p:=K) (Or.inl (pos hs.le).ne')
    simpa only [W,Pi.mul_def,id_eq,mul_one,one_mul] using d.mul power
  have anti : AntitoneOn W (Ici 0):=by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) cw
    · rw [interior_Ici];exact fun s hs=>(dw s hs).differentiableAt.differentiableWithinAt
    rw [interior_Ici]
    intro s hs
    have ht0 : 0<s:=hs
    rw [(dw s ht0).deriv]
    have nd:=(c.multicover_product_antitone hf turn initial).derivWithin_nonpos (x:=s)
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht0),(c.normalizedProduct_hasDerivAt_normal hf ht0).deriv] at nd
    have ep : 0≤e s:=by dsimp [e];linarith only [nd]
    have gap:=c.multicover_gap hf turn initial ht0
    have en:=mul_le_mul_of_nonneg_right (c.multicover_envelope hf turn initial ht0.le) ep
    change c.initialAbsoluteTurning^4/1000*D s≤c.length s^4*e s at gap
    change c.length s^4*e s≤B*(1+s)*e s at en
    have ineq : D s*K≤2*e s*(1+s):=by
      apply le_of_mul_le_mul_right (a:=B) _ bp
      rw [mul_assoc,kb]
      linarith only [gap,en]
    have fac : (1+s)^K=(1+s)^(K-1)*(1+s):=by
      simpa only [sub_add_cancel,Real.rpow_one] using (Real.rpow_add (pos ht0.le) (K-1) 1)
    rw [fac]
    nlinarith only [mul_le_mul_of_nonneg_right ineq (Real.rpow_nonneg (pos ht0.le).le (K-1))]
  simpa [W,D,K] using anti self_mem_Ici ht ht

theorem multicover_oscillation_limit (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) :
    Tendsto c.multicoverOscillation atTop (𝓝 0) := by
  have hp : 0<c.multicoverDecayExponent:=by
    have m : 0<c.initialAbsoluteTurning:=by linarith
    unfold multicoverDecayExponent initialLengthEnvelope
    positivity
  have lim : Tendsto (fun t:ℝ=>c.multicoverOscillation 0/(1+t)^c.multicoverDecayExponent) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hp).comp (tendsto_const_nhds.add_atTop tendsto_id))
  apply squeeze_zero' _ _ lim
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have b:=pow_le_pow_left₀ (abs_nonneg _) (c.multicover_floor ht) 2
    rwa [c.rootBending_sq ht,←sub_nonneg] at b
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (by linarith : (0:ℝ)<1+t) _)).mpr
      (c.multicover_power_decay hf turn initial ht)
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_power_decay
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_oscillation_limit
