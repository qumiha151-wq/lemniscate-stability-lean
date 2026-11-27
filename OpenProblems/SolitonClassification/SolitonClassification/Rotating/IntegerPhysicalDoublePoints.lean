import SolitonClassification.Rotating.IntegerGlobalChartLabels
import SolitonClassification.Rotating.IntegerPhysicalHull

namespace SolitonClassification.Rotating.IntegerTarget.GlobalCount
noncomputable section
open Set

/-- Reparametrizing a period and applying an injective map of the image
preserves the exhaustive two-pair description. -/
theorem TwoCrossingPairs.transport {f : ℝ→ℝ×ℝ} {T : ℝ} (z : TwoCrossingPairs f T)
    (M : (ℝ×ℝ)→ℝ×ℝ) (inj : Function.Injective M) (e : ℝ≃ℝ) (order : StrictMono e)
    (lower : e (-T) = -T) (upper : e T=T) :
    Nonempty (TwoCrossingPairs (fun s => M (f (e s))) T) := by
  let p := fun k:Fin 2 => (e.symm (z.pair k).1,e.symm (z.pair k).2)
  refine ⟨⟨p,?_,?_,?_,?_⟩⟩
  · intro k
    obtain ⟨l,m,r⟩ := z.inside k
    change -T≤e.symm _ ∧ e.symm _<e.symm _ ∧ e.symm _<T
    refine ⟨order.le_iff_le.mp ?_,order.lt_iff_lt.mp ?_,order.lt_iff_lt.mp ?_⟩
    · simpa only [lower,e.apply_symm_apply] using l
    · simpa only [e.apply_symm_apply] using m
    · simpa only [upper,e.apply_symm_apply] using r
  · intro k
    simpa [p] using congrArg M (z.coincide k)
  · intro eq
    apply z.distinct
    apply inj
    simpa [p] using eq
  · intro s t hs st ht eq
    have l := order.monotone hs
    have r := order ht
    rw [lower] at l
    rw [upper] at r
    obtain ⟨k,hk⟩ := z.exhaustive l (order st) r (inj eq)
    have hx := congrArg Prod.fst hk
    have hy := congrArg Prod.snd hk
    exact ⟨k,Prod.ext (by change s=e.symm _;rw [←hx];simp) (by change t=e.symm _;rw [←hy];simp)⟩

end
end SolitonClassification.Rotating.IntegerTarget.GlobalCount

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open GlobalCount NormalEvolution Real

theorem planarSimilarity_injective {r : ℝ} (hr : 0<r) (θ : ℝ) : Function.Injective (planarSimilarity r θ) := by
  rintro ⟨x,y⟩ ⟨u,v⟩ same
  have A := congrArg Prod.fst same
  have B := congrArg Prod.snd same
  change r*(cos θ*x-sin θ*y)=r*(cos θ*u-sin θ*v) at A
  change r*(sin θ*x+cos θ*y)=r*(sin θ*u+cos θ*v) at B
  have ax := mul_left_cancel₀ hr.ne' A
  have by' := mul_left_cancel₀ hr.ne' B
  have unit := sin_sq_add_cos_sq θ
  apply Prod.ext
  · change x=u
    linear_combination cos θ*ax+sin θ*by'-(x-u)*unit
  · change y=v
    linear_combination -sin θ*ax+cos θ*by'-(y-v)*unit

/-- Every physical time slice has a material interval of precisely one
period whose ordered coincident pairs are exhaustively the two double points. -/
theorem physical_two_double_points (P : Seed) {T : ℝ} (len : P.L=2*T)
    (z : TwoCrossingPairs (fun s => (P.I.x s,P.I.y s)) T) (t : ℝ) :
    ∃shift : ℝ, Nonempty (TwoCrossingPairs (fun s => (normalX P t (s+shift),normalY P t (s+shift))) T) := by
  let τ := logClock t
  let g := physicalField P
  let ρ := scalarFlowEquiv g τ
  let shift := ρ.symm (-T)+T
  let e : ℝ≃ℝ := ⟨fun s => ρ (s+shift), fun v => ρ.symm v-shift,
    by intro s;simp, by intro v;simp⟩
  have strict : StrictMono (scalarFlow g τ) := strictMono_of_deriv_pos
    (fun x => scalarFlow_spatial_derivative_pos g τ x)
  have order : StrictMono e := fun x y h => strict (by linarith : x+shift<y+shift)
  have lower : e (-T)= -T := by
    change ρ (-T+(ρ.symm (-T)+T))= -T
    rw [show -T+(ρ.symm (-T)+T)=ρ.symm (-T) by ring,ρ.apply_symm_apply]
  have upper : e T=T := by
    have period := normalParameter_period_add P τ (ρ.symm (-T))
    change ρ (ρ.symm (-T)+P.L)=ρ (ρ.symm (-T))+P.L at period
    rw [ρ.apply_symm_apply,len] at period
    change ρ (T+(ρ.symm (-T)+T))=T
    rw [show T+(ρ.symm (-T)+T)=ρ.symm (-T)+2*T by ring,period]
    ring
  refine ⟨shift,?_⟩
  exact z.transport (planarSimilarity (dilationScale t) (P.b*τ))
    (planarSimilarity_injective (dilationScale_pos t) _) e order lower upper

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.physical_two_double_points

