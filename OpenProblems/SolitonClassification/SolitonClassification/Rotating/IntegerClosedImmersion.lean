import SolitonClassification.Rotating.IntegerWindingSeam

/-! A winding-one solution of the support shooting equation gives an actual
smooth regular plane curve with signed total curvature -2π. -/
namespace SolitonClassification.Rotating.IntegerTarget
noncomputable section
open Set Filter
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

structure WindingOneImmersion (b L : ℝ) where
  x : ℝ → ℝ
  y : ℝ → ℝ
  k : ℝ → ℝ
  theta : ℝ → ℝ
  smoothX : ContDiff ℝ (⊤ : ℕ∞) x
  smoothY : ContDiff ℝ (⊤ : ℕ∞) y
  periodX : Function.Periodic x L
  periodY : Function.Periodic y L
  angleDerivative : ∀s, HasDerivAt theta (k s) s
  turning : ∀s, theta (s+L)=theta s-2*Real.pi
  tangentX : ∀s, HasDerivAt x (Real.cos (theta s)) s
  tangentY : ∀s, HasDerivAt y (Real.sin (theta s)) s
  speed : ∀s, deriv x s^2+deriv y s^2=1
  curvature : ∀s, deriv x s*deriv (deriv y) s-deriv y s*deriv (deriv x) s=k s
  soliton : ∀s, deriv (deriv k) s+(k s)^3/2=
    -(x s*(-deriv y s)+y s*deriv x s)-b*(x s*deriv x s+y s*deriv y s)

theorem immersion_of_matched_arc {T : ℝ} (hT : 0<T) (z : ℝ→State)
    (hd : ∀s∈Icc (-T) T, HasDerivAt z (field (z s)) s)
    (hm : z T=z (-T)+angleVector (-2*Real.pi)) :
    ∃ I : WindingOneImmersion (z 0 4) (2*T), I.k 0=z 0 0 ∧
      I.x 0*deriv I.x 0+I.y 0*deriv I.y 0=z 0 3 := by
  obtain ⟨Z,hZ,dZ,agrees,hol⟩ := extend_matched_segment hT z hd hm
  have hz : Z 0=z 0 := agrees 0 ⟨by linarith, hT.le⟩
  have dz (i : Fin 6) (s : ℝ) : HasDerivAt (fun u => Z u i) (field (Z s) i) s := by
    exact ((ContinuousLinearMap.proj i : State→L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt s (dZ s))
  have cb (s : ℝ) : Z s 4=z 0 4 := by
    have df (u : ℝ) : HasDerivAt (fun t => Z t 4) 0 u := dz 4 u
    have eq := is_const_of_deriv_eq_zero (fun u => (df u).differentiableAt) (fun u => (df u).deriv) s 0
    simpa only [hz] using eq
  let k := fun s => Z s 0
  let v := fun s => 8*Z s 1
  let p := fun s => Z s 2
  let q := fun s => Z s 3
  let th := fun s => Z s 5
  let x := ClosedSimilarity.profileX p q th
  let y := ClosedSimilarity.profileY p q th
  have dk (s : ℝ) : HasDerivAt k (v s) s := dz 0 s
  have dv (s : ℝ) : HasDerivAt v (-(k s)^3/2-p s-z 0 4*q s) s := by
    convert! (dz 1 s).const_mul 8 using 1
    dsimp [field,k,p,q]
    rw [cb]
    ring
  have dp (s : ℝ) : HasDerivAt p (-k s*q s) s := dz 2 s
  have dq (s : ℝ) : HasDerivAt q (1+k s*p s) s := dz 3 s
  have dt (s : ℝ) : HasDerivAt th (k s) s := dz 5 s
  have per (i : Fin 6) (hi : i≠5) : Function.Periodic (fun s => Z s i) (2*T) := by
    intro s
    simpa [angleVector,hi] using congrFun (hol s) i
  have ht (s : ℝ) : th (s+2*T)=th s-2*Real.pi := by
    have h := congrFun (hol s) 5
    simpa [th,angleVector,sub_eq_add_neg] using h
  obtain ⟨px,py⟩ := ClosedSimilarity.profile_periodic p q th (2*T) (-1)
    (per 2 (by decide)) (per 3 (by decide)) (fun s => by simpa [sub_eq_add_neg] using ht s)
  have cs (i : Fin 6) : ContDiff ℝ (⊤ : ℕ∞) (fun s => Z s i) :=
    (contDiff_apply ℝ ℝ i).comp hZ
  have sp : ContDiff ℝ (⊤ : ℕ∞) p := cs 2
  have sq : ContDiff ℝ (⊤ : ℕ∞) q := cs 3
  have st : ContDiff ℝ (⊤ : ℕ∞) th := cs 5
  have dx (s : ℝ) : HasDerivAt x (Real.cos (th s)) s :=
    ClosedSimilarity.profileX_hasDerivAt k p q th s (dp s) (dq s) (dt s)
  have dy (s : ℝ) : HasDerivAt y (Real.sin (th s)) s :=
    ClosedSimilarity.profileY_hasDerivAt k p q th s (dp s) (dq s) (dt s)
  refine ⟨⟨x,y,k,th,(sq.mul st.cos).sub (sp.mul st.sin),(sq.mul st.sin).add (sp.mul st.cos),
    px,py,dt,ht,dx,dy,?_,?_,?_⟩,congrFun hz 0,?_⟩
  · exact fun s => ClosedSimilarity.profile_unit_speed k p q th s (dp s) (dq s) (dt s)
  · exact ClosedSimilarity.profile_signed_curvature k p q th dp dq dt
  · intro s
    rw [(dx s).deriv,(dy s).deriv]
    exact ClosedSimilarity.profile_soliton_equation _ k v p q th dk dv s
  · change x 0*deriv x 0+y 0*deriv y 0=z 0 3
    rw [(dx 0).deriv,(dy 0).deriv]
    exact (ClosedSimilarity.tangent_support p q th 0).trans (congrFun hz 3)

end
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.immersion_of_matched_arc
