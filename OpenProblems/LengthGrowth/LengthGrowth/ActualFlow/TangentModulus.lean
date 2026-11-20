import LengthGrowth.ActualFlow.MacroscopicTangentChord
import LengthGrowth.ActualFlow.TurningExcursions

noncomputable section
open Set Function MeasureTheory
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- On subintervals short in the chosen increasing one-period coordinate,
the two endpoint tangents remain within a fixed chord distance. Each
slice may choose its own coordinate. -/
def HasQuarterTurnModulus (p : PeriodicRegularPosition) (η : ℝ) : Prop :=
  ∃ φ : ℝ→ℝ,StrictMono φ ∧ (∀x,φ (x+p.length)=φ x+1) ∧
    ∀x y : ℝ,x≤y → φ y-φ x≤η → ‖p.closedFrenetCurve.tangent y-p.closedFrenetCurve.tangent x‖<Real.sin (1/4)

theorem turning_count_of_modulus (p : PeriodicRegularPosition) {m : ℕ} {η : ℝ}
    (hp : 0<η) (modu : p.HasQuarterTurnModulus η) (ex : p.HasTurningExcursions m) :
    (m:ℝ)≤1/η := by
  classical
  let P:=Real.sqrt (2*(materialEnergy p.position p.period*p.length))
  let h:=p.length/P
  have pp:0<P:=Real.sqrt_pos.mpr (by positivity [p.material_energy_pos,p.length_pos])
  have hh:0<h:=div_pos p.length_pos pp
  have span:h*P=p.length:=div_mul_cancel₀ _ pp.ne'
  have mono : StrictMono (fun v:ℝ=>h*v) := fun _ _ hx=>mul_lt_mul_of_pos_left hx hh
  let scale : (ℝ×ℝ) ↪ (ℝ×ℝ) := ⟨fun I=>(h*I.1,h*I.2), by
    rintro ⟨i,j⟩ ⟨q,r⟩ eq
    exact Prod.ext (mono.injective (congrArg Prod.fst eq)) (mono.injective (congrArg Prod.snd eq))⟩
  obtain ⟨a,U,card,arcs,dis⟩:=ex
  obtain ⟨φ,ord,per,osc⟩:=modu
  have good (I) (hi:I∈U.map scale) :
      h*a≤I.1 ∧ I.1<I.2 ∧ I.2≤h*a+p.closedFrenetCurve.period ∧
        1/4≤|∫s in I.1..I.2,p.closedFrenetCurve.curvature s| := by
    obtain ⟨J,hJ,rfl⟩:=Finset.mem_map.mp hi
    obtain ⟨ax,xy,yb,turn⟩:=arcs J hJ
    change 1/4≤|∫s in J.1..J.2,p.scaledArclengthCurvature h s| at turn
    rw [p.turning_on_scaled_interval] at turn
    refine ⟨mono.monotone ax,mono xy,?_,turn⟩
    change h*J.2≤h*a+p.length
    rw [←span,←mul_add]
    exact mono.monotone yb
  have sep (I) (hi:I∈U.map scale) (J) (hj:J∈U.map scale) (ne:I≠J) :
      Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2) := by
    obtain ⟨K,hk,rfl⟩:=Finset.mem_map.mp hi
    obtain ⟨V,hv,rfl⟩:=Finset.mem_map.mp hj
    apply Ioo_disjoint_Ioo.mpr
    have ex:=Ioo_disjoint_Ioo.mp (dis K hk V hv (fun he=>ne (congrArg scale he)))
    change min (h*K.2) (h*V.2) ≤ max (h*K.1) (h*V.1)
    simpa only [mono.monotone.map_min,mono.monotone.map_max] using mono.monotone ex
  have bd:=p.closedFrenetCurve.packing_le_inverse_modulus (a:=h*a)
    (by norm_num : (0:ℝ)<1/4) (by linarith [Real.pi_gt_three] : (1/4:ℝ)<Real.pi)
    hp ord per osc (U.map scale) good sep
  simpa only [Finset.card_map,card] using bd

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.turning_count_of_modulus
