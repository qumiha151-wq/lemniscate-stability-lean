import LengthGrowth.ActualFlow.DefectLengthSpeed

noncomputable section
open Set
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem length_fourth_window (hf : c.IsNormalFEF) (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36)
    {T t η : ℝ} (hT : 0≤T) (st : T<t) (hp : 0<η) :
    let H := c.normalizedProduct
    let S := fun x => c.length x^4
    let B := c.initialLengthEnvelope*(1+t)
    32*Real.pi^4*(t-T)-8*B*(H T-H t) ≤ S t-S T ∧
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
  have ha := c.bending_product_antitone hf initial
  have point (x : ℝ) (hx : x∈Ioo T t) :
      32*Real.pi^4 ≤ 4*A x-8*B*(-e x) ∧
      4*A x+C*(-e x) ≤ 2*(2*H T)^2+4*η := by
    have xp := ppos x hx
    have he : 0≤e x := by
      have nn := ha.derivWithin_nonpos (x:=x)
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds xp),(dH x hx).deriv] at nn
      linarith
    obtain ⟨lo,hi⟩ := c.physical_speed_window xp.le hp he
    let Y := c.length x^4*e x
    change 2*Real.pi^2*(2*H x)-2*Y≤A x at lo
    change A x≤(2*H x)^2/2+η+(2*H x)*Y/(4*η) at hi
    have nY : 0≤Y := mul_nonneg (pow_nonneg (c.length_pos xp.le).le _) he
    have lten := c.bending_envelope_linear hf initial xp.le
    have cap : Y≤B*e x := mul_le_mul_of_nonneg_right
      (lten.trans (mul_le_mul_of_nonneg_left (by linarith only [hx.2] : 1+x≤1+t) mpos.le)) he
    have low : 2*Real.pi^2≤H x := c.sharp_energy_length xp.le
    have ub : H x≤H T := ha hT xp.le hx.1.le
    have initub : H x≤H 0 := ha self_mem_Ici xp.le xp.le
    have grow := mul_le_mul initub cap nY (c.normalizedProduct_nonneg 0)
    have sq := pow_le_pow_left₀ (c.normalizedProduct_nonneg x) ub 2
    constructor
    · nlinarith only [lo,cap,mul_le_mul_of_nonneg_left low (sq_nonneg Real.pi)]
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
  change 32*Real.pi^4*(t-T)-8*B*(H T-H t) ≤ S t-S T ∧
      S t-S T≤(2*(2*H T)^2+4*η)*(t-T)+C*(H T-H t)
  constructor <;> linarith only [l,u]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.length_fourth_window
