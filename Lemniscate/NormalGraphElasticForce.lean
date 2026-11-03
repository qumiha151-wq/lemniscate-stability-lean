import Lemniscate.NormalGraphGeometry
import Lemniscate.NormalGraphJetLinearization

/-! The exact elastic force of an actual normal graph equals its finite-jet
expression. Spatial derivatives of the metric and curvature numerators are
proved from the Frenet data; no variation or linearization formula is assumed. -/
noncomputable section
namespace Lemniscate
open Complex
open scoped ComplexConjugate

private theorem normal_graph_scalar_second
    (H H₁ H₂ N N₁ N₂ : ℝ → ℝ)
    (hH : ∀ u, HasDerivAt H (H₁ u) u)
    (hH₁ : ∀ u, HasDerivAt H₁ (H₂ u) u)
    (hN : ∀ u, HasDerivAt N (N₁ u) u)
    (hN₁ : ∀ u, HasDerivAt N₁ (N₂ u) u)
    (hpos : ∀ u, 0 < H u) (s : ℝ) :
    let r : ℝ → ℝ := fun u => (Real.sqrt (H u))⁻¹
    r s*deriv (fun u => r u*deriv (fun v => N v*(r v)^3) u) s =
      N₂ s*(r s)^5-(7/2:ℝ)*N₁ s*H₁ s*(r s)^7-
      (3/2:ℝ)*N s*H₂ s*(r s)^7+(9/2:ℝ)*N s*(H₁ s)^2*(r s)^9 := by
  let r : ℝ → ℝ := fun u => (Real.sqrt (H u))⁻¹
  have hr (u : ℝ) : HasDerivAt r (-(1/2:ℝ)*H₁ u*(r u)^3) u := by
    have hg0 : Real.sqrt (H u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hpos u))
    convert! ((hH u).sqrt (ne_of_gt (hpos u))).inv hg0 using 1 <;>
      dsimp only [r] <;> field_simp [hg0] <;> ring
  have hκ (u : ℝ) : HasDerivAt (fun v => N v*(r v)^3)
      (N₁ u*(r u)^3-(3/2:ℝ)*N u*H₁ u*(r u)^5) u := by
    convert! HasDerivAt.mul (hN u) ((hr u).pow 3) using 1 <;>
      simp only [Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  let L : ℝ → ℝ := fun u => N₁ u*(r u)^4-(3/2:ℝ)*N u*H₁ u*(r u)^6
  have hfirst : (fun u => r u*deriv (fun v => N v*(r v)^3) u) = L := by
    funext u
    rw [(hκ u).deriv]
    dsimp only [L]
    ring
  have hL (u : ℝ) : HasDerivAt L
      (N₂ u*(r u)^4-(7/2:ℝ)*N₁ u*H₁ u*(r u)^6-
        (3/2:ℝ)*N u*H₂ u*(r u)^6+(9/2:ℝ)*N u*(H₁ u)^2*(r u)^8) u := by
    have hd0 := HasDerivAt.mul (hN₁ u) ((hr u).pow 4)
    have hd1 := HasDerivAt.mul
      (HasDerivAt.mul ((hN u).const_mul (3/2:ℝ)) (hH₁ u)) ((hr u).pow 6)
    convert! HasDerivAt.sub hd0 hd1 using 1 <;>
      simp only [L,Pi.mul_apply,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  change r s*deriv (fun u => r u*deriv (fun v => N v*(r v)^3) u) s = _
  rw [hfirst,(hL s).deriv]
  ring

theorem normal_graph_elastic_force
    (β t n : ℝ → ℂ) (k ks kss ksss h h₁ h₂ h₃ h₄ : ℝ → ℝ)
    (hβ : ∀ s, HasDerivAt β (t s) s)
    (ht : ∀ s, HasDerivAt t ((k s:ℂ)*n s) s)
    (hn : ∀ s, HasDerivAt n (-(k s:ℂ)*t s) s)
    (hk : ∀ s, HasDerivAt k (ks s) s)
    (hks : ∀ s, HasDerivAt ks (kss s) s)
    (hkss : ∀ s, HasDerivAt kss (ksss s) s)
    (hh : ∀ s, HasDerivAt h (h₁ s) s)
    (hh₁ : ∀ s, HasDerivAt h₁ (h₂ s) s)
    (hh₂ : ∀ s, HasDerivAt h₂ (h₃ s) s)
    (hh₃ : ∀ s, HasDerivAt h₃ (h₄ s) s)
    (htunit : ∀ s, ‖t s‖ = 1) (hnormal : ∀ s, n s = I*t s)
    (hregular : ∀ s, 0 < 1-k s*h s) (c s : ℝ) :
    let γ := normalGraphCurve β n h
    let K : NormalGraphBackgroundJet :=
      ⟨k s,ks s,kss s,ksss s,(conj (t s)*β s).im,(conj (t s)*β s).re⟩
    let J : NormalGraphHeightJet := ⟨h s,h₁ s,h₂ s,h₃ s,h₄ s⟩
    arclengthDerivative γ (arclengthDerivative γ (planarSignedCurvature γ)) s+
      (1/2:ℝ)*(planarSignedCurvature γ s)^3+c*planarNormalSupport γ s =
        normalGraphJetForce K c J := by
  let γ := normalGraphCurve β n h
  let A : ℝ → ℝ := fun u => 1-k u*h u
  let A₁ : ℝ → ℝ := fun u => -ks u*h u-k u*h₁ u
  let A₂ : ℝ → ℝ := fun u => -kss u*h u-2*ks u*h₁ u-k u*h₂ u
  let H : ℝ → ℝ := fun u => (A u)^2+(h₁ u)^2
  let H₁ : ℝ → ℝ := fun u => 2*A u*A₁ u+2*h₁ u*h₂ u
  let H₂ : ℝ → ℝ := fun u =>
    2*(A₁ u)^2+2*A u*A₂ u+2*(h₂ u)^2+2*h₁ u*h₃ u
  let N : ℝ → ℝ := fun u =>
    k u*(A u)^2+A u*h₂ u+ks u*h u*h₁ u+2*k u*(h₁ u)^2
  let N₁ : ℝ → ℝ := fun u =>
    ks u*(A u)^2+2*k u*A u*A₁ u+A₁ u*h₂ u+A u*h₃ u+
      kss u*h u*h₁ u+3*ks u*(h₁ u)^2+ks u*h u*h₂ u+4*k u*h₁ u*h₂ u
  let N₂ : ℝ → ℝ := fun u =>
    kss u*(A u)^2+4*ks u*A u*A₁ u+2*k u*(A₁ u)^2+2*k u*A u*A₂ u+
      A₂ u*h₂ u+2*A₁ u*h₃ u+A u*h₄ u+ksss u*h u*h₁ u+
      4*kss u*(h₁ u)^2+2*kss u*h u*h₂ u+11*ks u*h₁ u*h₂ u+
      ks u*h u*h₃ u+4*k u*(h₂ u)^2+4*k u*h₁ u*h₃ u
  let b : ℝ → ℝ := fun u => (conj (t u)*β u).re
  let eta : ℝ → ℝ := fun u => (conj (t u)*β u).im
  let P : ℝ → ℝ := fun u => A u*(eta u+h u)-b u*h₁ u
  let r : ℝ → ℝ := fun u => (Real.sqrt (H u))⁻¹
  let K : ℝ → NormalGraphBackgroundJet :=
    fun u => ⟨k u,ks u,kss u,ksss u,eta u,b u⟩
  let J : ℝ → NormalGraphHeightJet := fun u => ⟨h u,h₁ u,h₂ u,h₃ u,h₄ u⟩
  have hA (u : ℝ) : HasDerivAt A (A₁ u) u := by
    convert! ((hk u).mul (hh u)).const_sub 1 using 1 <;> dsimp only [A,A₁] <;> ring
  have hA₁ (u : ℝ) : HasDerivAt A₁ (A₂ u) u := by
    have hd := HasDerivAt.sub
      (HasDerivAt.mul (HasDerivAt.neg (hks u)) (hh u))
      (HasDerivAt.mul (hk u) (hh₁ u))
    convert! hd using 1 <;> simp only [A₁,A₂,Pi.mul_apply,Pi.neg_apply] <;> ring
  have hH (u : ℝ) : HasDerivAt H (H₁ u) u := by
    convert! HasDerivAt.add ((hA u).pow 2) ((hh₁ u).pow 2) using 1 <;>
      simp only [H,H₁,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  have hH₁ (u : ℝ) : HasDerivAt H₁ (H₂ u) u := by
    have hd0 := HasDerivAt.mul ((hA u).const_mul 2) (hA₁ u)
    have hd1 := HasDerivAt.mul ((hh₁ u).const_mul 2) (hh₂ u)
    convert! HasDerivAt.add hd0 hd1 using 1 <;> dsimp only [H₁,H₂] <;> ring
  have hN (u : ℝ) : HasDerivAt N (N₁ u) u := by
    have hd0 := HasDerivAt.mul (hk u) ((hA u).pow 2)
    have hd1 := HasDerivAt.mul (hA u) (hh₂ u)
    have hd2 := HasDerivAt.mul (HasDerivAt.mul (hks u) (hh u)) (hh₁ u)
    have hd3 := HasDerivAt.mul ((hk u).const_mul 2) ((hh₁ u).pow 2)
    have hd := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add hd0 hd1) hd2) hd3
    convert! hd using 1 <;>
      simp only [N,N₁,Pi.mul_apply,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  have hN₁ (u : ℝ) : HasDerivAt N₁ (N₂ u) u := by
    have hd0 := HasDerivAt.mul (hks u) ((hA u).pow 2)
    have hd1 := HasDerivAt.mul
      (HasDerivAt.mul ((hk u).const_mul 2) (hA u)) (hA₁ u)
    have hd2 := HasDerivAt.mul (hA₁ u) (hh₂ u)
    have hd3 := HasDerivAt.mul (hA u) (hh₃ u)
    have hd4 := HasDerivAt.mul (HasDerivAt.mul (hkss u) (hh u)) (hh₁ u)
    have hd5 := HasDerivAt.mul ((hks u).const_mul 3) ((hh₁ u).pow 2)
    have hd6 := HasDerivAt.mul (HasDerivAt.mul (hks u) (hh u)) (hh₂ u)
    have hd7 := HasDerivAt.mul
      (HasDerivAt.mul ((hk u).const_mul 4) (hh₁ u)) (hh₂ u)
    have hd := HasDerivAt.add
      (HasDerivAt.add
        (HasDerivAt.add
          (HasDerivAt.add
            (HasDerivAt.add
              (HasDerivAt.add (HasDerivAt.add hd0 hd1) hd2) hd3) hd4) hd5) hd6) hd7
    convert! hd using 1 <;>
      simp only [N₁,N₂,Pi.mul_apply,Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat] <;> ring
  have hHpos (u : ℝ) : 0 < H u := by
    have ha : 0 < (A u)^2 := sq_pos_of_pos (hregular u)
    dsimp only [H]
    nlinarith only [ha,sq_nonneg (h₁ u)]
  have hgeometry (u : ℝ) :=
    normal_graph_geometry β t n k ks h h₁ h₂ hβ ht hn hk hh hh₁ htunit hnormal u
  have hspeed (u : ℝ) : ‖deriv γ u‖ = Real.sqrt (H u) := (hgeometry u).2.2.1
  have hcurvature : planarSignedCurvature γ = fun u => N u*(r u)^3 := by
    funext u
    rw [(hgeometry u).2.2.2.1]
    simp only [N,r,H,A,div_eq_mul_inv,inv_pow]
  have hsupport (u : ℝ) : planarNormalSupport γ u = P u*r u := by
    rw [(hgeometry u).2.2.2.2.1]
    simp only [P,r,H,A,b,eta,div_eq_mul_inv]
  have hD (f : ℝ → ℝ) : arclengthDerivative γ f = fun u => r u*deriv f u := by
    funext u
    dsimp only [arclengthDerivative]
    rw [hspeed u]
    simp only [r,div_eq_mul_inv,mul_comm]
  have hsecond := normal_graph_scalar_second H H₁ H₂ N N₁ N₂ hH hH₁ hN hN₁ hHpos s
  change arclengthDerivative γ (arclengthDerivative γ (planarSignedCurvature γ)) s+
      (1/2:ℝ)*(planarSignedCurvature γ s)^3+c*planarNormalSupport γ s =
        normalGraphJetForce (K s) c (J s)
  rw [hD,hD,hcurvature]
  change r s*deriv (fun u => r u*deriv (fun v => N v*(r v)^3) u) s+
      (1/2:ℝ)*(N s*(r s)^3)^3+c*planarNormalSupport γ s = _
  rw [hsecond,hsupport s]
  change (N₂ s*(r s)^5-(7/2:ℝ)*N₁ s*H₁ s*(r s)^7-
      (3/2:ℝ)*N s*H₂ s*(r s)^7+(9/2:ℝ)*N s*(H₁ s)^2*(r s)^9)+
      (1/2:ℝ)*(N s*(r s)^3)^3+c*(P s*r s) =
    N₂ s*(r s)^5-(7/2:ℝ)*N₁ s*H₁ s*(r s)^7-
      (3/2:ℝ)*N s*H₂ s*(r s)^7+(9/2:ℝ)*N s*(H₁ s)^2*(r s)^9+
      (1/2:ℝ)*(N s)^3*(r s)^9+c*P s*r s
  ring

end Lemniscate
