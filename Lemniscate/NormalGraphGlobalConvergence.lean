import Lemniscate.PeriodicCjTranslation
import Lemniscate.PeriodicCjRescaling
import Lemniscate.PhysicalNormalization
import Mathlib.Analysis.Complex.Trigonometric

/-! Convergence of the actual uncentered normalized curve in every C^j
norm, from one solution whose Sobolev representatives all tend to zero. -/
noncomputable section
namespace Lemniscate
open Complex Filter Set
open scoped ContDiff Topology BigOperators NNReal ENNReal

variable (T : ℝ) [Fact (0 < T)]

private theorem global_graph_height_identification
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n))
    (hw : ∀ n (s : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n s) =
      circleSobolevCoordinate T 2 0 (u ⟨(s:ℝ),s.property.le⟩))
    (j : ℕ) (s : Ioi (0:ℝ)) :
    circleSobolevClassicalJet T j (w (j+1) s) 0 =
      circleSobolevH1Embedding T (circleSobolevInclusion T 1
        (u (Real.toNNReal (s:ℝ)))) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T (circleSobolevClassicalJet T j (w (j+1) s) 0) =
    circleContinuousL2 T (circleSobolevH1Embedding T
      (circleSobolevInclusion T 1 (u (Real.toNNReal (s:ℝ)))))
  rw [circle_sobolev_classical_jet_l2,circle_sobolev_h1_embedding_l2]
  change circleSobolevCoordinate T (j+1) 0 (w (j+1) s) =
    circleSobolevCoordinate T 2 0 (u (Real.toNNReal (s:ℝ)))
  have hs : Real.toNNReal (s:ℝ) = ⟨(s:ℝ),s.property.le⟩ := by
    exact Real.toNNReal_of_nonneg s.property.le
  rw [hs]
  exact hw (j+1) s

set_option maxHeartbeats 800000 in
/-- The original normalized curve, including its fixed center divided by
the expanding scale, converges in every standard C^j norm. The height is
the actual continuous representative of the one H2 solution; compatibility
and uniqueness of continuous representatives identify all higher jets.
The physical clock is exactly log(1+30t/a^4)/30. -/
theorem normal_graph_global_cj_convergence
    (β ν : ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hν : ContDiff ℝ ∞ ν)
    (hβper : Function.Periodic β T) (hνper : Function.Periodic ν T)
    (u : C(ℝ≥0,CircleSobolevSpace T 2))
    (w : ∀ n : ℕ, C(Ioi (0:ℝ),CircleSobolevSpace T n))
    (hw : ∀ n (s : Ioi (0:ℝ)), circleSobolevCoordinate T n 0 (w n s) =
      circleSobolevCoordinate T 2 0 (u ⟨(s:ℝ),s.property.le⟩))
    (hwzero : ∀ n, Tendsto (w n) atTop (𝓝 0))
    (θ : ℝ → ℝ) (θlim : ℝ) (hθ : Tendsto θ atTop (𝓝 θlim))
    (ρ : ℝ → ℝ) (hρ : Tendsto ρ atTop atTop) (p₀ : ℂ)
    (a : ℝ) (ha : 0 < a) :
    let h : ℝ → C(AddCircle T,ℂ) := fun s =>
      circleSobolevH1Embedding T (circleSobolevInclusion T 1 (u (Real.toNNReal s)))
    let E : ℝ → ℝ → ℂ := fun t x => p₀/(ρ t:ℂ)+
      Complex.exp ((θ (normalizedTime a t):ℂ)*I)*
        (β (Real.sqrt 2*x)+h (normalizedTime a t) ((Real.sqrt 2*x:AddCircle T))*
          ν (Real.sqrt 2*x))-
        Complex.exp ((θlim:ℂ)*I)*β (Real.sqrt 2*x)
    ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j (E t)) atTop (𝓝 0) := by
  let h : ℝ → C(AddCircle T,ℂ) := fun s =>
    circleSobolevH1Embedding T (circleSobolevInclusion T 1 (u (Real.toNNReal s)))
  let E : ℝ → ℝ → ℂ := fun t x => p₀/(ρ t:ℂ)+
    Complex.exp ((θ (normalizedTime a t):ℂ)*I)*
      (β (Real.sqrt 2*x)+h (normalizedTime a t) ((Real.sqrt 2*x:AddCircle T))*
        ν (Real.sqrt 2*x))-
      Complex.exp ((θlim:ℂ)*I)*β (Real.sqrt 2*x)
  change ∀ j : ℕ, Tendsto (fun t => periodicCjNorm j (E t)) atTop (𝓝 0)
  have hσ : Tendsto (normalizedTime a) atTop atTop := by
    obtain ⟨r,hr⟩ := physical_normalization a ha
    exact hr.2.2.2.2
  let S : ℝ → Ioi (0:ℝ) := fun t =>
    ⟨max 1 (normalizedTime a t),by
      change (0:ℝ) < max 1 (normalizedTime a t)
      exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _)⟩
  have hSreal : Tendsto (fun t => (S t:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun t => le_max_right 1 (normalizedTime a t)) hσ
  have hS : Tendsto S atTop atTop := tendsto_Ioi_atTop.mpr hSreal
  let z : Ioi (0:ℝ) → ℂ := fun s => Complex.exp ((θ (s:ℝ):ℂ)*I)
  let zlim : ℂ := Complex.exp ((θlim:ℂ)*I)
  have hz : ∀ s, ‖z s‖ = 1 := fun s => Complex.norm_exp_ofReal_mul_I (θ (s:ℝ))
  have hzlim : Tendsto (fun t => z (S t)) atTop (𝓝 zlim) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hθ.comp hSreal)).mul_const I)
  have hzdiff : Tendsto (fun t => ‖z (S t)-zlim‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (hzlim.sub (tendsto_const_nhds (x := zlim))).norm
  have hcinv : Tendsto (fun t => (ρ t)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp hρ
  have hc : Tendsto (fun t => ‖p₀/(ρ t:ℂ)‖) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := p₀)).mul
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hcinv)
    simpa only [Function.comp_def,Complex.ofReal_inv,div_eq_mul_inv,
      Complex.ofReal_zero,mul_zero,norm_zero]
      using hh.norm
  let B : C(AddCircle T,ℂ) := ⟨hβper.lift,hβ.continuous.quotient_lift _⟩
  let N : C(AddCircle T,ℂ) := ⟨hνper.lift,hν.continuous.quotient_lift _⟩
  let E₀ : Ioi (0:ℝ) → ℝ → ℂ := fun s x =>
    z s*(β x+h (s:ℝ) (x:AddCircle T)*ν x)-zlim*β x
  have hbounded (s : Ioi (0:ℝ)) :
      BddAbove (Set.range (fun x : ℝ => ‖E₀ s (Real.sqrt 2*x)‖)) := by
    let J : C(AddCircle T,ℂ) := (z s) • (B+h (s:ℝ)*N)-zlim • B
    refine ⟨‖J‖,?_⟩
    rintro _ ⟨x,rfl⟩
    change ‖J ((Real.sqrt 2*x:AddCircle T))‖ ≤ ‖J‖
    exact J.norm_coe_le_norm _
  intro j
  have horder : (j : WithTop ℕ∞) < (∞ : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)
  obtain ⟨C,hC,hestimate⟩ := normal_graph_cj_estimate T j β ν
    (hβ.of_le horder.le) (hν.of_le horder.le) hβper hνper
  let M : ℝ := (max 1 |Real.sqrt 2|)^j
  have hbase (s : Ioi (0:ℝ)) :
      periodicCjNorm j (fun x => E₀ s (Real.sqrt 2*x)) ≤
        M*C*(‖w (j+1) s‖+‖z s-zlim‖) := by
    have hid := global_graph_height_identification T u w hw j s
    have he := (hestimate (w (j+1) s) (z s) zlim (hz s)).2.2
    change periodicCjNorm j (fun x => z s*(β x+
      circleSobolevClassicalJet T j (w (j+1) s) 0 (x:AddCircle T)*ν x)-zlim*β x) ≤ _ at he
    rw [hid] at he
    change periodicCjNorm j (E₀ s) ≤ C*(‖w (j+1) s‖+‖z s-zlim‖) at he
    have hM : 0 ≤ M := by dsimp only [M]; positivity
    have hr := (periodic_cj_norm_rescaling j (E₀ s) (Real.sqrt 2)
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))).2
    exact hr.trans ((mul_le_mul_of_nonneg_left he hM).trans_eq (by ring))
  have hwlim : Tendsto (fun t => ‖w (j+1) (S t)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,norm_zero] using ((hwzero (j+1)).comp hS).norm
  have hmajor : Tendsto (fun t => ‖p₀/(ρ t:ℂ)‖+
      M*C*(‖w (j+1) (S t)‖+‖z (S t)-zlim‖)) atTop (𝓝 0) := by
    simpa only [zero_add,mul_zero,add_zero] using hc.add ((hwlim.add hzdiff).const_mul (M*C))
  apply squeeze_zero' ?_ ?_ hmajor
  · exact Eventually.of_forall fun t => Finset.sum_nonneg fun i _ =>
      Real.sSup_nonneg (by rintro _ ⟨x,rfl⟩; exact norm_nonneg _)
  · filter_upwards [hσ.eventually (eventually_ge_atTop (1:ℝ))] with t ht
    have hSt : (S t:ℝ) = normalizedTime a t := max_eq_right ht
    have hE : E t = fun x => p₀/(ρ t:ℂ)+E₀ (S t) (Real.sqrt 2*x) := by
      funext x
      dsimp only [E,E₀,z]
      rw [hSt]
      ring
    rw [hE]
    exact (periodic_cj_norm_translation j (fun x => E₀ (S t) (Real.sqrt 2*x))
      (p₀/(ρ t:ℂ)) (hbounded (S t))).trans
        (add_le_add (le_refl _) (hbase (S t)))

end Lemniscate
