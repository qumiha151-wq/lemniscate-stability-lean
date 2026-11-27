import LengthGrowth.ActualFlow.DefectLengthSpeed
import LengthGrowth.ActualFlow.MulticoverAttraction
import LengthGrowth.ActualFlow.MulticoverDisk

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

def multiLowerSpeed (t:ℝ):=2*c.initialAbsoluteTurning^4/(1+Real.sqrt (c.multicoverOscillation t))^4

private theorem lower_speed {s:ℝ} (hs:0≤s)
    (turn : 6≤c.initialAbsoluteTurning) (e : 0≤c.length s*c.dissipation s-c.energy s*c.lengthRate s) :
    c.multiLowerSpeed s≤4*(c.length s^3*c.lengthRate s)+8*(c.length s^4*(c.length s*c.dissipation s-c.energy s*c.lengthRate s)):=by
  let g:=c.regularPositionAt hs
  let p:=g.closedFrenetCurve
  let S:=materialSignedCurvature (c.position s) c.period
  let M:=c.initialAbsoluteTurning
  let L:=c.length s
  let E:=c.energy s
  let D:=c.dissipation s
  let j:=c.lengthRate s
  let F:=1+Real.sqrt (c.multicoverOscillation s)
  let U:=2*c.normalizedProduct s
  let Y:=L^4*(L*D-E*j)
  let A:=L^3*j
  have sum : (∫x in 0..p.period,p.curvature x)=S:=by
    simp_rw [show ∀x,p.curvature x=curvature g.position (g.arclengthInverse x) from g.closedFrenetCurve_curvature]
    exact g.integral_comp_inverse (curvature_smooth g.smooth g.regular).continuous
  have Mabs : |S|=M:=by dsimp only [S,M,initialAbsoluteTurning];rw [c.signedCurvature_eq_initial hs]
  have nz : S≠0:=by intro eq;rw [eq,abs_zero] at Mabs;dsimp only [M] at Mabs;linarith
  have en : p.energy=E:=g.closedFrenetCurve_energy
  have di : p.dissipation=D:=g.closedFrenetCurve_dissipation
  have leq : p.period=L:=rfl
  have eql : S^2=M^2:=by rw [←Mabs,sq_abs]
  have eq4 : S^4=M^4:=by rw [show S^4=(S^2)^2 by ring,eql];ring
  have nn : 0≤2*p.energy*p.period-S^2:=by
    rw [en,leq,eql]
    have b:=pow_le_pow_left₀ (abs_nonneg _) (c.multicover_floor hs) 2
    rw [c.rootBending_sq hs] at b
    change 0≤2*E*L-M^2
    change M^2≤2*(E*L) at b
    linarith only [b]
  have disk:=p.winding_dissipation sum nz nn
  rw [en,di,leq,eq4,eql] at disk
  have diff : 2*E*L-M^2=c.multicoverOscillation s:=by unfold multicoverOscillation normalizedProduct;ring
  rw [diff] at disk
  change M^4*E≤2*D*L^4*F^4 at disk
  have fl : 0<F:=by dsimp [F];positivity
  have scaled:=mul_le_mul_of_nonneg_right disk (c.length_pos hs).le
  have loss : U*(M^4/(2*F^4))≤U*A+2*Y:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<2*F^4)).mpr
    dsimp only [U,normalizedProduct,Y,A,E,L,D,j] at scaled ⊢
    linarith only [scaled]
  have x1 : 1≤U:=by
    have g1:=c.multicover_floor hs
    have sq:=pow_le_pow_left₀ (abs_nonneg _) g1 2
    rw [c.rootBending_sq hs] at sq
    change 1≤2*c.normalizedProduct s
    nlinarith only [turn,sq,sq_nonneg (c.initialAbsoluteTurning-6)]
  have yn : 0≤Y:=mul_nonneg (pow_nonneg (c.length_pos hs).le _) e
  have lower : M^4/(2*F^4)≤A+2*Y:=by
    apply le_of_mul_le_mul_left (a:=U) _ (by linarith only [x1])
    nlinarith only [loss,mul_le_mul_of_nonneg_right x1 yn]
  change 2*M^4/F^4≤4*A+8*Y
  rw [show 2*M^4/F^4=4*(M^4/(2*F^4)) by field_simp [fl.ne'];ring]
  linarith only [lower]

private theorem low_speed_monotone (ha : AntitoneOn c.normalizedProduct (Ici 0))
    {s t:ℝ} (hs:0≤s) (st:s≤t) : c.multiLowerSpeed s≤c.multiLowerSpeed t:=by
  unfold multiLowerSpeed
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_right
  apply Real.sqrt_le_sqrt
  unfold multicoverOscillation
  linarith only [ha hs (hs.trans st) st]

theorem multi_length_window (hf : c.IsNormalFEF) (turn : 6≤c.initialAbsoluteTurning) (initial : c.rootBending 0≤c.initialAbsoluteTurning+3/5)
    {T t η : ℝ} (hT : 0≤T) (st : T<t) (hp : 0<η) :
    let H := c.normalizedProduct
    let S := fun x => c.length x^4
    let B := c.initialLengthEnvelope*(1+t)
    c.multiLowerSpeed T*(t-T)-8*B*(H T-H t) ≤ S t-S T ∧
    S t-S T ≤ (2*(2*H T)^2+4*η)*(t-T)+(2*H 0/η)*B*(H T-H t) := by
  let H := c.normalizedProduct
  let S := fun x => c.length x^4
  let e := fun s => c.length s*c.dissipation s-c.energy s*c.lengthRate s
  let A := fun s => c.length s^3*c.lengthRate s
  let B := c.initialLengthEnvelope*(1+t)
  let C := (2*H 0/η)*B
  have mpos : 0<c.initialLengthEnvelope := by dsimp [initialLengthEnvelope]; positivity
  have sub : Icc T t⊆Ici 0 := fun _ hx => hT.trans hx.1
  have hC : ContinuousOn H (Icc T t) := c.normalizedProduct_continuousOn.mono sub
  have sC : ContinuousOn S (Icc T t) := (c.length_continuousOn.pow 4).mono sub
  have ppos (x : ℝ) (hx : x∈Ioo T t) : 0<x := hT.trans_lt hx.1
  have dS (x : ℝ) (hx : x∈Ioo T t) : HasDerivAt S (4*A x) x := by
    apply ((c.length_hasDerivAt_normal hf (ppos x hx)).pow 4).congr_deriv
    dsimp [A]; ring
  have dH (x : ℝ) (hx : x∈Ioo T t) : HasDerivAt H (-e x) x := by
    apply (c.normalizedProduct_hasDerivAt_normal hf (ppos x hx)).congr_deriv
    dsimp only [e]; ring
  have ha := c.multicover_product_antitone hf turn initial
  have point (x : ℝ) (hx : x∈Ioo T t) :
      c.multiLowerSpeed T ≤ 4*A x-8*B*(-e x) ∧
      4*A x+C*(-e x) ≤ 2*(2*H T)^2+4*η := by
    have xp := ppos x hx
    have he : 0≤e x := by
      have nn := ha.derivWithin_nonpos (x:=x)
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds xp),(dH x hx).deriv] at nn
      linarith
    have hi := (c.physical_speed_window xp.le hp he).2
    have lo:=c.lower_speed xp.le turn he
    let Y := c.length x^4*e x
    change c.multiLowerSpeed x≤4*A x+8*Y at lo
    change A x≤(2*H x)^2/2+η+(2*H x)*Y/(4*η) at hi
    have nY : 0≤Y := mul_nonneg (pow_nonneg (c.length_pos xp.le).le _) he
    have lten := c.multicover_envelope hf turn initial xp.le
    have cap : Y≤B*e x := mul_le_mul_of_nonneg_right
      (lten.trans (mul_le_mul_of_nonneg_left (by linarith only [hx.2] : 1+x≤1+t) mpos.le)) he
    have low:=c.low_speed_monotone ha hT hx.1.le
    have ub : H x≤H T := ha hT xp.le hx.1.le
    have initub : H x≤H 0 := ha self_mem_Ici xp.le xp.le
    have grow := mul_le_mul initub cap nY (c.normalizedProduct_nonneg 0)
    have sq := pow_le_pow_left₀ (c.normalizedProduct_nonneg x) ub 2
    constructor
    · linarith only [low,lo,cap]
    · have rhs : (2*H x)*Y/(4*η)≤C*e x/4 := by
        dsimp only [C]
        apply (div_le_div_iff₀ (by positivity : 0<4*η) (by norm_num : (0:ℝ)<4)).mpr
        field_simp [hp.ne']; linarith only [grow]
      linarith only [hi,sq,rhs]
  have cc1 := sC.sub (hC.const_mul (8*B))
  have cc2 := sC.add (hC.const_mul C)
  obtain ⟨x,hx,eq1⟩ := exists_hasDerivAt_eq_slope (fun x => S x-8*B*H x)
    (fun x => 4*A x-8*B*(-e x)) st cc1 (fun x hx => (dS x hx).sub ((dH x hx).const_mul (8*B)))
  obtain ⟨y,hy,eq2⟩ := exists_hasDerivAt_eq_slope (fun x => S x+C*H x)
    (fun x => 4*A x+C*(-e x)) st cc2 (fun x hx => (dS x hx).add ((dH x hx).const_mul C))
  have l := (le_div_iff₀ (sub_pos.mpr st)).mp (eq1 ▸ (point x hx).1)
  have u := (div_le_iff₀ (sub_pos.mpr st)).mp (eq2 ▸ (point y hy).2)
  change c.multiLowerSpeed T*(t-T)-8*B*(H T-H t) ≤ S t-S T ∧
      S t-S T≤(2*(2*H T)^2+4*η)*(t-T)+C*(H T-H t)
  constructor <;> linarith only [l,u]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multi_length_window
