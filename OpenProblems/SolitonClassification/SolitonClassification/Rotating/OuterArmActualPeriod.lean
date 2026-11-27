import SolitonClassification.Rotating.OuterArmMultiplicity
import Mathlib.Data.Nat.ModEq
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace SolitonClassification.Rotating.ArmCount

private theorem ordinary_transport {A B : Type*} {Y W : A→ℂ} {X V : B→ℂ} {p : ℂ}
    (e : A ≃ B) (position : ∀a,X (e a)=Y a) (velocity : ∀a,V (e a)=W a)
    (h : Ordinary Y W p) : Ordinary X V p := by
  obtain ⟨a,b,ne,ha,hb,allp,transv⟩ := h
  refine ⟨e a,e b,fun eq=>ne (e.injective eq), (position a).trans ha,(position b).trans hb,?_,?_⟩
  · intro u hu
    obtain ⟨v,rfl⟩ := e.surjective u
    exact (allp v ((position v).symm.trans hu)).imp (congrArg e) (congrArg e)
  · simpa only [velocity] using transv

private def residue {d m : ℕ} (hd : 0<d) (i : Fin d) : Fin d := ⟨(m*i.val)%d,Nat.mod_lt _ hd⟩

private theorem residue_inj {d m : ℕ} (hd : 0<d) (cop : d.Coprime m) :
    Function.Injective (residue (m:=m) hd) := by
  intro i j eq
  have h : Nat.ModEq d (m*i.val) (m*j.val) := congrArg Fin.val eq
  have fij : Nat.ModEq d i.val j.val := Nat.ModEq.cancel_left_of_coprime cop h
  change i.val%d=j.val%d at fij
  exact Fin.ext (by simpa only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using fij)

private def joinLabel {d : ℕ} {L : ℝ} (lp : 0<L)
    (v : Fin d × Ico (0:ℝ) L) : Ico (0:ℝ) ((d:ℝ)*L) :=
  ⟨v.1.val*L+v.2.val, by
    constructor
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) lp.le) v.2.2.1
    · have le : (v.1.val:ℝ)+1≤d := by exact_mod_cast v.1.isLt
      linarith only [mul_le_mul_of_nonneg_right le lp.le,v.2.2.2]⟩

private theorem join_bijective {d : ℕ} {L : ℝ} (lp : 0<L) :
    Function.Bijective (joinLabel (d:=d) lp) := by
  constructor
  · rintro ⟨i,u⟩ ⟨j,v⟩ eq
    have val : (i.val:ℝ)*L+u.val=j.val*L+v.val := congrArg Subtype.val eq
    have ii : i=j := by
      apply Fin.ext
      rcases lt_trichotomy i.val j.val with h|h|h
      · have le : (i.val:ℝ)+1≤j.val := by exact_mod_cast h
        linarith only [mul_le_mul_of_nonneg_right le lp.le,u.2.2,v.2.1,val]
      · exact h
      · have le : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast h
        linarith only [mul_le_mul_of_nonneg_right le lp.le,v.2.2,u.2.1,val]
    subst j; exact Prod.ext rfl (Subtype.ext (add_left_cancel val))
  · intro y
    let i := ⌊y.val/L⌋₊
    have le : (i:ℝ)≤y.val/L := Nat.floor_le (div_nonneg y.2.1 lp.le)
    have lt : y.val/L<(i:ℝ)+1 := Nat.lt_floor_add_one _
    have id : i<d := by
      have yl := (div_lt_iff₀ lp).mpr y.2.2
      exact_mod_cast le.trans_lt yl
    have lo := (le_div_iff₀ lp).mp le
    have hi := (div_lt_iff₀ lp).mp lt
    refine ⟨(⟨i,id⟩,⟨y.val-(i:ℝ)*L,by constructor <;> linarith only [lo,hi]⟩),Subtype.ext ?_⟩
    change (i:ℝ)*L+(y.val-i*L)=y.val; ring

private theorem period_power {X : ℝ→ℂ} {w : ℂ} {L : ℝ} (step : ∀s,X (s+L)=w*X s)
    (n : ℕ) (s : ℝ) : X ((n:ℝ)*L+s)=w^n*X s := by
  induction n with
  | zero => simp
  | succ n h =>
    rw [Nat.cast_succ,show ((n:ℝ)+1)*L+s=(n*L+s)+L by ring,step,h,pow_succ]; ring

/-- Applied directly to an actual differentiable profile on the half-open
interval of length dL, including its true velocity vectors and every label. -/
theorem many_ordinary_on_period {X : ℝ→ℂ} {L : ℝ} {d m : ℕ} (hd : 0<d) (lp : 0<L)
    (cop : d.Coprime m) (smooth : Differentiable ℝ X)
    (monodromy : ∀s,X (s+L)=zeta d ^ m*X s)
    (arms : Arms (fun u : Ico (0:ℝ) L=>X u) (fun u : Ico (0:ℝ) L=>deriv X u)) :
    ∃S : Finset ℂ,S.card=d*(d/200) ∧ ∀y∈S,
      Ordinary (fun u : Ico (0:ℝ) ((d:ℝ)*L)=>X u) (fun u : Ico (0:ℝ) ((d:ℝ)*L)=>deriv X u) y := by
  classical
  let perm := Equiv.ofBijective (residue (m:=m) hd) ⟨residue_inj hd cop,
    Finite.surjective_of_injective (residue_inj hd cop)⟩
  let join := Equiv.ofBijective (joinLabel (d:=d) lp) (join_bijective lp)
  let order := Equiv.prodCongr perm.symm (Equiv.refl (Ico (0:ℝ) L))
  let e := order.trans join
  have ds (s : ℝ) : deriv X (s+L)=zeta d^m*deriv X s := by
    have lhs : HasDerivAt (fun t=>X (t+L)) (deriv X (s+L)) s := by
      simpa [Function.comp_def] using (smooth (s+L)).hasDerivAt.scomp s ((hasDerivAt_id s).add_const L)
    rw [show (fun t=>X (t+L))=(fun t=>zeta d^m*X t) from funext monodromy] at lhs
    exact lhs.unique ((smooth s).hasDerivAt.const_mul _)
  have root_step (j : ℕ) : zeta d ^ (j%d)=zeta d^j := by
    have dn : (d:ℂ)≠0 := by exact_mod_cast hd.ne'
    have hp : (zeta d)^d=1 := by
      rw [zeta,←Complex.exp_nat_mul,show (d:ℂ)*(2*Real.pi*Complex.I/d)=2*Real.pi*Complex.I by field_simp,
        Complex.exp_two_pi_mul_I]
    calc
      _ = zeta d^(j%d)*((zeta d)^d)^(j/d) := by rw [hp,one_pow,mul_one]
      _ = _ := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
  have eqn (Y : ℝ→ℂ) (hs : ∀s,Y (s+L)=zeta d^m*Y s) (i : Fin d × Ico (0:ℝ) L) :
      Y (e i)=copies (fun u : Ico (0:ℝ) L=>Y u) d i := by
    change Y ((↑(perm.symm i.1).val:ℝ)*L+i.2.val)=zeta d^i.1.val*Y i.2.val
    rw [period_power hs,←pow_mul]
    have h := congrArg Fin.val (perm.apply_symm_apply i.1)
    change (m*(perm.symm i.1).val)%d=i.1.val at h
    rw [← h,root_step]
  obtain ⟨S,card,good⟩ := arms.many_ordinary hd
  exact ⟨S,card,fun y hy=>ordinary_transport e (eqn X monodromy) (eqn (deriv X) ds) (good y hy)⟩

end SolitonClassification.Rotating.ArmCount
#print axioms SolitonClassification.Rotating.ArmCount.many_ordinary_on_period
