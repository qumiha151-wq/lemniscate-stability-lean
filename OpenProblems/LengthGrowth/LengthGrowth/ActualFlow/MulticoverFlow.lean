import LengthGrowth.ActualFlow.MulticoverSlice
import LengthGrowth.ActualFlow.DefectFlowSublevel
import LengthGrowth.ActualFlow.CubicHalfThreshold
import LengthGrowth.ActualFlow.EventualCurvatureSign

noncomputable section
open Set Filter Topology MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

def initialAbsoluteTurning : ℝ:=|materialSignedCurvature (c.position 0) c.period|

private theorem physical_slice {s : ℝ} (hs : 0≤s) :
    c.initialAbsoluteTurning≤c.rootBending s ∧
    (6≤c.initialAbsoluteTurning → c.initialAbsoluteTurning<c.rootBending s →
    c.rootBending s≤c.initialAbsoluteTurning+3/5 →
    c.energy s*c.lengthRate s<c.length s*c.dissipation s) := by
  unfold initialAbsoluteTurning
  rw [←c.signedCurvature_eq_initial hs]
  exact (c.regularPositionAt hs).multicover_slice

theorem multicover_sublevel_invariant (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) {t:ℝ} (ht:0≤t) :
    c.rootBending t≤c.initialAbsoluteTurning+3/5 := by
  let M:=c.initialAbsoluteTurning
  have hM : 0<M:=by dsimp only [M];linarith
  have initial' : 2*c.normalizedProduct 0≤(M+3/5)^2:=by
    rw [←c.rootBending_sq (le_refl 0)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) initial 2
  have cap : 2*c.normalizedProduct t≤(M+3/5)^2:=by
    apply LengthGrowth.DefectFour.sublevel_forward (U:=fun s=>2*c.normalizedProduct s)
      ht (continuousOn_const.mul c.normalizedProduct_continuousOn) initial'
    intro s hs eq
    have eq' : c.rootBending s=M+3/5:=by
      have rs:=c.rootBending_sq hs
      have nn : 0≤c.rootBending s:=Real.sqrt_nonneg _
      change 2*c.normalizedProduct s=(M+3/5)^2 at eq
      nlinarith only [eq,rs,nn,hM]
    have strict:=(c.physical_slice hs).2 turn (by rw [eq'];dsimp only [M];linarith) eq'.le
    exact ⟨2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s),by linarith only [strict],
      (c.normalizedProduct_right_derivative hf hs).const_mul 2⟩
  rw [←c.rootBending_sq ht] at cap
  change c.rootBending t≤M+3/5
  nlinarith only [cap,hM]

theorem multicover_product_antitone (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) : AntitoneOn c.normalizedProduct (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _) c.normalizedProduct_continuousOn
  · rw [interior_Ici]
    exact fun t ht=>(c.normalizedProduct_hasDerivAt_normal hf ht).differentiableAt.differentiableWithinAt
  rw [interior_Ici]
  intro t ht
  have pos : 0<t:=ht
  have hd:=c.normalizedProduct_hasDerivAt_normal hf pos
  rw [hd.deriv]
  rcases lt_or_eq_of_le (c.physical_slice pos.le).1 with above|floor
  · exact sub_nonpos.mpr ((c.physical_slice pos.le).2 turn above
      (c.multicover_sublevel_invariant hf turn initial pos.le)).le
  have floor' : c.initialAbsoluteTurning^2=2*c.normalizedProduct t:=by rw [floor,c.rootBending_sq pos.le]
  have hmin : IsLocalMin c.normalizedProduct t:=by
    filter_upwards [lt_mem_nhds pos] with x hx
    have b:=pow_le_pow_left₀ (abs_nonneg _) (c.physical_slice (le_of_lt hx)).1 2
    rw [c.rootBending_sq (le_of_lt hx),floor'] at b
    linarith only [b]
  exact (hmin.hasDerivAt_eq_zero hd).le

theorem multicover_explicit_length (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning)
    (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5) {t:ℝ} (ht:0≤t) :
    c.length t≤2*c.length 0 ∨ c.length t^4≤4*(2*c.normalizedProduct 0)^2*t := by
  by_cases short : c.length t≤2*c.length 0
  · exact Or.inl short
  right
  have half : c.length t/2∈Icc (c.length 0) (c.length t) :=
    ⟨by linarith,by linarith [c.length_pos ht]⟩
  obtain ⟨s,hs,eq⟩ := intermediate_value_Icc ht (c.length_continuousOn.mono Icc_subset_Ici_self) half
  have sec := c.secant_sq_le_energy_drop hf hs.1 hs.2
  rw [show c.length t-c.length s=c.length s by linarith only [eq]] at sec
  have sq : c.length s^2≤t*c.energy s^2 := by
    nlinarith only [sec,mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg (c.energy t)),
      mul_nonneg hs.1 (sq_nonneg (c.energy s))]
  have anti := c.multicover_product_antitone hf turn initial self_mem_Ici hs.1 hs.1
  have asq := pow_le_pow_left₀ (c.normalizedProduct_nonneg s) anti 2
  have prod : c.length s^4≤t*(c.normalizedProduct 0)^2 := by
    have b := mul_le_mul_of_nonneg_left asq ht
    unfold normalizedProduct at b
    change c.length s^4≤t*(c.energy 0*c.length 0)^2
    linarith only [b,mul_le_mul_of_nonneg_right sq (sq_nonneg (c.length s))]
  rw [eq] at prod
  linarith only [prod]


end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_product_antitone
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_explicit_length
