import Lemniscate.NormalGraphFlowVariation
import Lemniscate.BernoulliArclengthFrame
import Lemniscate.BernoulliSobolevLinearization
import Lemniscate.NormalGraphClassicalRepresentation

/-! On classical real graph data, the Sobolev normal-graph equation is the
actual geometric equation over the Bernoulli lemniscate. The parameter x is
sqrt(2) times physical arclength. The Frenet and support data come from the
explicit curve and its actual integral coordinate.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 1600000 in
theorem bernoulli_classical_graph_equation (e : ℝ ≃o ℝ)
    (he : ∀ u, e u = ∫ t in (0:ℝ)..u, Real.sqrt 2*‖bernoulliVelocity t‖)
    (q p : C(AddCircle T, ℂ))
    (hq : ∀ x : ℝ, q (x:AddCircle T) = (bernoulliProfileQ (e.symm x):ℂ))
    (hp : ∀ x : ℝ, p (x:AddCircle T) = (bernoulliProfileP (e.symm x):ℂ))
    (H : Fin 5 → C(AddCircle T, ℂ))
    (hreal : ∀ j x, ((H j x).re:ℂ) = H j x)
    (hderiv : ∀ j : Fin 4, HasCircleDeriv T (H j.castSucc) (H j.succ))
    (f : CircleSobolevSpace T 4)
    (hjet : ∀ j : Fin 4, circleSobolevContinuousJet T f j = H j.castSucc)
    (hfourth : circleSobolevCoordinate T 4 4 f = circleContinuousL2 T (H 4))
    (hdomain : f ∈ circleNormalGraphDomain T (circleBernoulliBackground T q p))
    (hregular : ∀ x : ℝ,
      0 < 1-3*bernoulliProfileQ (e.symm x)*(H 0 (x:AddCircle T)).re) :
    let φ : ℝ → ℝ := fun s => e.symm (Real.sqrt 2*s)
    let Γ := bernoulliCurve ∘ φ
    let n : ℝ → ℂ := fun s =>
      I*(bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ))
    let k : ℝ → ℝ := fun s => 3*bernoulliProfileQ (φ s)
    let Z := circleNormalGraphCoordinates T f
    let R := normalGraphRationalFlow (circleBernoulliBackground T q p) (15/2)
      ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • H 4⟩
    circleNormalGraphFlow T (circleBernoulliBackground T q p) (15/2) f =
        circleContinuousL2 T R ∧
      ∀ x : ℝ, R (x:AddCircle T) =
        ((normalGraphFlowRHS Γ n k
          (fun s => (H 0 ((Real.sqrt 2*s):AddCircle T)).re)
          (15/2) (x/Real.sqrt 2):ℝ):ℂ) := by
  let d : ℝ → ℝ := fun s => Real.sqrt 2*s
  let φ : ℝ → ℝ := fun s => e.symm (d s)
  let Γ := bernoulliCurve ∘ φ
  let t : ℝ → ℂ := fun s =>
    bernoulliVelocity (φ s)/(‖bernoulliVelocity (φ s)‖:ℂ)
  let n : ℝ → ℂ := fun s => I*t s
  let Q := bernoulliProfileQ ∘ φ
  let P := bernoulliProfileP ∘ φ
  let k : ℝ → ℝ := fun s => 3*Q s
  let ks : ℝ → ℝ := fun s => 3*Real.sqrt 2*P s
  let kss : ℝ → ℝ := fun s => -6*(Q s)^3
  let ksss : ℝ → ℝ := fun s => -18*Real.sqrt 2*(Q s)^2*P s
  let F : Fin 5 → ℝ → ℝ := fun j x => (H j (x:AddCircle T)).re
  let h : ℝ → ℝ := fun s => F 0 (d s)
  let h₁ : ℝ → ℝ := fun s => Real.sqrt 2*F 1 (d s)
  let h₂ : ℝ → ℝ := fun s => 2*F 2 (d s)
  let h₃ : ℝ → ℝ := fun s => 2*Real.sqrt 2*F 3 (d s)
  let h₄ : ℝ → ℝ := fun s => 4*F 4 (d s)
  let K := circleBernoulliBackground T q p
  let Z := circleNormalGraphCoordinates T f
  let R := normalGraphRationalFlow K (15/2) ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • H 4⟩
  have hframe := bernoulli_arclength_frame e he
  have hD (j : Fin 4) (x : ℝ) :
      HasDerivAt (F j.castSucc) (F j.succ x) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hderiv j x)
  have hd (s : ℝ) : HasDerivAt d (Real.sqrt 2) s := by
    simpa only [d,id_eq,mul_one] using (hasDerivAt_id s).const_mul (Real.sqrt 2)
  have hh (s : ℝ) : HasDerivAt h (h₁ s) s := by
    convert! (hD 0 (d s)).comp s (hd s) using 1
    change Real.sqrt 2*F 1 (d s) = F 1 (d s)*Real.sqrt 2
    ring
  have hh₁ (s : ℝ) : HasDerivAt h₁ (h₂ s) s := by
    convert! ((hD 1 (d s)).comp s (hd s)).const_mul (Real.sqrt 2) using 1
    change 2*F 2 (d s) = Real.sqrt 2*(F 2 (d s)*Real.sqrt 2)
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring
  have hh₂ (s : ℝ) : HasDerivAt h₂ (h₃ s) s := by
    convert! ((hD 2 (d s)).comp s (hd s)).const_mul 2 using 1
    change 2*Real.sqrt 2*F 3 (d s) = 2*(F 3 (d s)*Real.sqrt 2)
    ring
  have hh₃ (s : ℝ) : HasDerivAt h₃ (h₄ s) s := by
    convert! ((hD 3 (d s)).comp s (hd s)).const_mul (2*Real.sqrt 2) using 1
    change 4*F 4 (d s) = (2*Real.sqrt 2)*(F 4 (d s)*Real.sqrt 2)
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] <;> ring
  have hreg (s : ℝ) : 0 < 1-k s*h s := hregular (d s)
  have hZ : Z = ![H 0,((Real.sqrt 2:ℝ):ℂ) • H 1,
      (2:ℂ) • H 2,((2*Real.sqrt 2:ℝ):ℂ) • H 3] := by
    dsimp only [Z]
    rw [circle_normal_graph_coordinates]
    funext j
    fin_cases j <;> simp [hjet]
  obtain ⟨hL2,hpoint⟩ := circle_normal_graph_flow_classical_representation T K (15/2)
    f (H 4) hfourth hdomain
  refine ⟨hL2,?_⟩
  intro x
  let s := x/Real.sqrt 2
  let Kr : NormalGraphBackgroundJet :=
    ⟨k s,ks s,kss s,ksss s,(conj (t s)*Γ s).im,(conj (t s)*Γ s).re⟩
  let Jr : NormalGraphHeightJet := ⟨h s,h₁ s,h₂ s,h₃ s,h₄ s⟩
  have hroot : Real.sqrt (2:ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hscale : d s = x := by
    dsimp only [d,s]
    field_simp [hroot] <;> ring
  have hposition := (hframe s).2.2.2.2.2.2.2.2.1
  have hposre : (conj (t s)*Γ s).re = Real.sqrt 2*Q s*P s := by
    have hr := congrArg Complex.re hposition
    simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      sub_zero,add_zero] using hr
  have hposim : (conj (t s)*Γ s).im = -(Q s)^3 := by
    have hi := congrArg Complex.im hposition
    simpa only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,mul_one,
      zero_add,add_zero] using hi
  have hqx : q (x:AddCircle T) = (Q s:ℂ) := by
    simpa only [Q,φ,Function.comp_def,hscale] using hq x
  have hpx : p (x:AddCircle T) = (P s:ℂ) := by
    simpa only [P,φ,Function.comp_def,hscale] using hp x
  have hK :
      (⟨K.k (x:AddCircle T),K.ks (x:AddCircle T),K.kss (x:AddCircle T),
          K.ksss (x:AddCircle T),K.eta (x:AddCircle T),K.b (x:AddCircle T)⟩ :
        BackgroundJetOver ℂ) =
      ⟨(Kr.k:ℂ),(Kr.ks:ℂ),(Kr.kss:ℂ),(Kr.ksss:ℂ),(Kr.eta:ℂ),(Kr.b:ℂ)⟩ := by
    dsimp only [K,Kr,circleBernoulliBackground,k,ks,kss,ksss]
    rw [hposre,hposim]
    simp only [ContinuousMap.smul_apply,ContinuousMap.neg_apply,ContinuousMap.pow_apply,
      ContinuousMap.mul_apply,smul_eq_mul,hqx,hpx]
    push_cast <;> congr 1 <;> ring
  have hJ :
      (⟨Z 0 (x:AddCircle T),Z 1 (x:AddCircle T),Z 2 (x:AddCircle T),
          Z 3 (x:AddCircle T),4*H 4 (x:AddCircle T)⟩ : HeightJetOver ℂ) =
      ⟨(Jr.h:ℂ),(Jr.hs:ℂ),(Jr.hss:ℂ),(Jr.hsss:ℂ),(Jr.hssss:ℂ)⟩ := by
    simp only [hZ,Jr,h,h₁,h₂,h₃,h₄,F,hscale,
      Matrix.cons_val_zero,Matrix.cons_val,Matrix.head_cons,Matrix.tail_cons,
      ContinuousMap.smul_apply,smul_eq_mul]
    push_cast
    simp only [hreal] <;> congr 1 <;> ring
  have hactualJet : normalGraphFlowRHS Γ n k h (15/2) s =
      normalGraphJetFlow Kr (15/2) Jr := by
    have ha := normal_graph_flow_quasilinear Γ t n k ks kss ksss h h₁ h₂ h₃ h₄
      (fun u => (hframe u).1)
      (fun u => (hframe u).2.2.1)
      (fun u => (hframe u).2.2.2.1)
      (fun u => (hframe u).2.2.2.2.1)
      (fun u => (hframe u).2.2.2.2.2.1)
      (fun u => (hframe u).2.2.2.2.2.2.1)
      hh hh₁ hh₂ hh₃ (fun u => (hframe u).2.1) (fun _ => rfl) hreg (15/2) s
    exact ha.trans (normal_graph_jet_quasilinear Kr (15/2) Jr (hreg s)).symm
  have hactual : normalGraphFlowRHS Γ n k h (15/2) s =
      normalGraphRationalFlow Kr (15/2) Jr :=
    hactualJet.trans (normal_graph_rational_flow_real Kr (15/2) Jr (hreg s)).symm
  have hcast := normal_graph_rational_flow_ofReal Kr (15/2) Jr
  change normalGraphRationalFlow (R := ℂ)
      ⟨(Kr.k:ℂ),(Kr.ks:ℂ),(Kr.kss:ℂ),(Kr.ksss:ℂ),(Kr.eta:ℂ),(Kr.b:ℂ)⟩ (15/2)
      ⟨(Jr.h:ℂ),(Jr.hs:ℂ),(Jr.hss:ℂ),(Jr.hsss:ℂ),(Jr.hssss:ℂ)⟩ =
        ((normalGraphRationalFlow Kr (15/2) Jr:ℝ):ℂ) at hcast
  change R (x:AddCircle T) = ((normalGraphFlowRHS Γ n k h (15/2) s:ℝ):ℂ)
  rw [hpoint (x:AddCircle T),hK,hJ]
  exact hcast.trans (congrArg Complex.ofReal hactual.symm)

end Lemniscate
