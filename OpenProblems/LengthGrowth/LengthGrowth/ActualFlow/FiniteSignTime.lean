import LengthGrowth.ActualFlow.FiniteSignGrowth
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem linear_length_cap (hf : c.IsNormalFEF) {t : ℝ} (ht : 0≤t) :
    c.length t≤(c.length 0+c.energy 0+1)*(1+t) := by
  have h:=c.secant_sq_le_energy_drop hf (s:=0) le_rfl ht
  simp only [sub_zero] at h
  have he:=c.energy_nonneg 0
  have hL:=c.length_nonneg 0
  by_contra! hn
  have hmore : c.energy 0*(1+t)<c.length t-c.length 0 := by nlinarith [mul_nonneg hL ht]
  have hsq:=mul_self_lt_mul_self (by positivity : 0≤c.energy 0*(1+t)) hmore
  nlinarith only [hsq,h,mul_nonneg ht (sq_nonneg (c.energy t)),mul_nonneg ht (sq_nonneg (c.energy 0)),
    sq_nonneg (c.energy 0*t),sq_nonneg (c.energy 0)]

private theorem root_product_time_cap (hf : c.IsNormalFEF) {T K : ℝ} (hT : 0≤T) (hK : 0≤K)
    (barrier : AntitoneOn (fun t => Real.sqrt (c.normalizedProduct t)+(K/2)*Real.log (c.energy t)) (Ici T)) :
    ∃ C : ℝ, 0<C ∧ ∀ t≥T, Real.sqrt (c.normalizedProduct t) ≤ C*(1+Real.log (1+t)) := by
  let A := c.length 0+c.energy 0+1
  have ha : 0<A := by dsimp [A]; positivity [c.length_pos (t:=0) le_rfl,c.energy_pos (t:=0) le_rfl]
  let W := Real.sqrt (c.normalizedProduct T)+(K/2)*Real.log (c.energy T)+(K/2)*Real.log A
  let C := |W|+K+1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht
  have ht0:=hT.trans ht
  have he:=c.energy_pos ht0
  have hgeom:=c.sharp_energy_length ht0
  have hprod : 1≤c.energy t*c.length t := by nlinarith only [hgeom,Real.pi_gt_three]
  have hi : (c.energy t)⁻¹ ≤ A*(1+t) := by
    apply le_trans _ (c.linear_length_cap hf ht0)
    rw [inv_eq_one_div,div_le_iff₀ he]
    linarith only [hprod]
  have hlog:=Real.log_le_log (inv_pos.mpr he) hi
  rw [Real.log_inv,Real.log_mul ha.ne' (by positivity : 1+t≠0)] at hlog
  have hbar:=barrier (Set.mem_Ici.mpr (le_rfl : T≤T)) (Set.mem_Ici.mpr ht) ht
  have m:=mul_le_mul_of_nonneg_left hlog (by positivity : 0≤K/2)
  have hl:=Real.log_nonneg (show 1≤1+t by linarith)
  have bound : Real.sqrt (c.normalizedProduct t)≤W+(K/2)*Real.log (1+t) := by
    dsimp [W]; linarith
  dsimp [C]
  nlinarith only [bound,le_abs_self W,mul_nonneg (abs_nonneg W) hl,
    mul_nonneg hK hl,hK,hl]

theorem nodal_log_quarter_length (hf : c.IsNormalFEF) {T K : ℝ}
    (hT : 0≤T) (hK : 0≤K)
    (hs : ∀t>T, NodalSliceBound (c.energy t) (c.length t) (c.dissipation t) K) :
    ∃ C : ℝ, 0<C ∧ ∀t≥T, c.length t ≤ C*fourthRoot (1+t)*(1+Real.log (1+t)) := by
  obtain ⟨B,hB,bound⟩ := c.root_product_time_cap hf hT hK (c.nodal_log_energy_barrier hf hT hK hs)
  let C := 2*(B+c.length T)
  have hL:=c.length_pos hT
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht
  have ht0:=hT.trans ht
  have hr : 1≤fourthRoot (1+t) := by
    simpa [fourthRoot] using fourthRoot_mono (show (1:ℝ)≤1+t by linarith)
  have hg:=Real.log_nonneg (show 1≤1+t by linarith)
  have hC : 0≤C := by dsimp [C]; positivity
  by_cases low : c.length t≤2*c.length T
  · apply low.trans
    calc
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C*fourthRoot (1+t) := by nlinarith only [mul_nonneg hC (sub_nonneg.mpr hr)]
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hC (fourthRoot_nonneg (1+t))) hg]
  · have hh : c.length t/2∈Icc (c.length T) (c.length t) :=
      ⟨by linarith,by linarith [c.length_pos ht0]⟩
    obtain ⟨s,hst,heq⟩:=intermediate_value_Icc ht (c.length_continuousOn.mono (fun _ hx => hT.trans hx.1)) hh
    have hs0:=hT.trans hst.1
    have hsec:=c.secant_sq_le_energy_drop hf hs0 hst.2
    have h₁ : c.length s^2≤t*c.energy s^2 := by
      nlinarith only [heq,hsec,mul_nonneg (sub_nonneg.mpr hst.2) (sq_nonneg (c.energy t)),
        mul_nonneg hs0 (sq_nonneg (c.energy s)),congrArg (fun a:ℝ=>a^2) heq]
    have h₄ : c.length s^4≤(1+t)*(c.normalizedProduct s)^2 := by
      unfold normalizedProduct
      nlinarith only [mul_le_mul_of_nonneg_right h₁ (sq_nonneg (c.length s)),
        sq_nonneg (c.energy s*c.length s)]
    have hp0 : 0≤c.normalizedProduct s := (mul_pos (c.energy_pos hs0) (c.length_pos hs0)).le
    have hp : c.length s≤fourthRoot (1+t)*Real.sqrt (c.normalizedProduct s) := by
      by_contra! hh
      have high:=pow_lt_pow_left₀ hh (mul_nonneg (fourthRoot_nonneg _) (Real.sqrt_nonneg _)) (by decide : 4≠0)
      rw [mul_pow,fourthRoot_pow_four (by linarith)] at high
      rw [show Real.sqrt (c.normalizedProduct s)^4=c.normalizedProduct s^2 by
        rw [show (4:Nat)=2*2 from rfl,pow_mul,Real.sq_sqrt hp0]] at high
      exact (not_lt_of_ge h₄) high
    have hlog:=Real.log_le_log (by positivity : 0<1+s) (show 1+s≤1+t by linarith [hst.2])
    have hbd := (bound s hst.1).trans (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hB.le :
       B*(1+Real.log (1+s))≤B*(1+Real.log (1+t)))
    have hup:=hp.trans (mul_le_mul_of_nonneg_left hbd (fourthRoot_nonneg _))
    dsimp [C]
    nlinarith only [heq,hup,mul_nonneg (mul_nonneg hL.le (fourthRoot_nonneg (1+t))) (show 0≤1+Real.log (1+t) by linarith)]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.nodal_log_quarter_length
