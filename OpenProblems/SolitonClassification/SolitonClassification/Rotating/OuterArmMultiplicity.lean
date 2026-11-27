import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Complex
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
namespace SolitonClassification.Rotating.ArmCount

/-- Rotation through x full turns. -/
def rot (x : ℝ) : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I*(x:ℂ))
def zeta (d : ℕ) : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I/(d:ℂ))
def copies {A : Type*} (Z : A→ℂ) (d : ℕ) (t : Fin d × A) : ℂ := zeta d ^ t.1.val * Z t.2

theorem zeta_norm (d : ℕ) : ‖zeta d‖=1 := by
  rw [zeta,Complex.norm_exp]
  simp [Complex.div_natCast_re,Complex.mul_re,Complex.mul_im]

theorem rot_fraction (m d : ℕ) : rot ((m:ℝ)/d)=zeta d^m := by
  rw [rot,zeta,← Complex.exp_nat_mul]
  congr 1
  push_cast; ring

private theorem root_mod {d : ℕ} (dp : 0<d) (m : ℕ) : zeta d ^ (m%d)=zeta d^m := by
  have dp' : (d:ℂ)≠0 := by exact_mod_cast dp.ne'
  have hp : (zeta d)^d=1 := by
    rw [zeta,←Complex.exp_nat_mul,show (d:ℂ)*(2*Real.pi*Complex.I/d)=2*Real.pi*Complex.I by field_simp,Complex.exp_two_pi_mul_I]
  calc
    _ = zeta d ^ (m%d) * ((zeta d)^d)^(m/d) := by rw [hp,one_pow,mul_one]
    _ = _ := by rw [←pow_mul,←pow_add,Nat.mod_add_div]

private theorem power_inj {d : ℕ} (hd : 0<d) {i j : Fin d} (eq : zeta d^i.val=zeta d^j.val) : i=j := by
  simp only [zeta,←Complex.exp_nat_mul] at eq
  obtain ⟨n,en⟩ := Complex.exp_eq_exp_iff_exists_int.mp eq
  have non : (2*(Real.pi:ℂ)*Complex.I)≠0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have ec : (i.val:ℂ)/d=(j.val:ℂ)/d+n := by
    apply mul_right_cancel₀ non
    linear_combination en
  have er : (i.val:ℝ)/d=(j.val:ℝ)/d+n := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_intCast] using ec
  have dr : 0<(d:ℝ) := by exact_mod_cast hd
  have il : (i.val:ℝ)/d<1 := (div_lt_one dr).mpr (by exact_mod_cast i.isLt)
  have jl : (j.val:ℝ)/d<1 := (div_lt_one dr).mpr (by exact_mod_cast j.isLt)
  have ni : (-1:ℝ)<n := by linarith [show 0≤(i.val:ℝ)/d by positivity]
  have nj : (n:ℝ)<1 := by linarith [show 0≤(j.val:ℝ)/d by positivity]
  have ii : (-1:ℤ)<n := by exact_mod_cast ni
  have jj : n<(1:ℤ) := by exact_mod_cast nj
  have nz : n=0 := by omega
  rw [nz,Int.cast_zero,add_zero] at er
  exact Fin.ext (by exact_mod_cast (div_left_inj' dr.ne').mp er)

/-- Cross product of vectors in their respective radial frames. Rotation
of both the point and its tangent leaves its radial-frame vector fixed. -/
def wedge (p q : ℂ) : ℝ := p.re*q.im-p.im*q.re
def radial (p v : ℂ) : ℂ := conj p*v

theorem radial_wedge_of_opposite_speeds {u v : ℂ}
    (ur : 0<u.re) (vr : v.re<0) (same : (0<u.im ∧ 0<v.im) ∨ (u.im<0 ∧ v.im<0)) :
    wedge u v ≠ 0 := by
  unfold wedge
  rcases same with h|h
  · have a := mul_pos ur h.2
    have b := mul_neg_of_pos_of_neg h.1 vr
    linarith
  · have a := mul_neg_of_pos_of_neg ur h.2
    have b := mul_pos_of_neg_of_neg h.1 vr
    linarith

private theorem radial_rot {w : ℂ} (hw : ‖w‖=1) (x v : ℂ) :
    radial (w*x) (w*v)=radial x v := by
  unfold radial
  rw [map_mul]
  have h : conj w*w=1 := by
    rw [mul_comm,Complex.mul_conj,←Complex.sq_norm,hw]; norm_num
  linear_combination (conj x*v)*h

private theorem wedge_radial (p u v : ℂ) :
    wedge (radial p u) (radial p v)=Complex.normSq p*wedge u v := by
  simp [wedge,radial,Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

/-- Distinct parameter labels, exactly two preimages, and nonparallel
velocities in the image plane. -/
def Ordinary {A : Type*} (Z V : A→ℂ) (y : ℂ) : Prop :=
  ∃a b : A,a≠b ∧ Z a=y ∧ Z b=y ∧ (∀c,Z c=y → c=a ∨ c=b) ∧ wedge (V a) (V b)≠0

/-- Two radial arms on one support block. Parameter zero denotes the
outer tip; no separation or transversality is needed at the tip itself. -/
structure Arms {A : Type*} (Z V : A→ℂ) where
  left : ℝ→A
  right : ℝ→A
  radius : ℝ→ℝ
  delta : ℝ→ℝ
  cont : ContinuousOn delta (Icc 0 1)
  atTip : delta 0=0
  width : 1/200≤delta 1
  rad_inj : InjOn radius (Ioc 0 1)
  positive : ∀x∈Ioc 0 1, 0<radius x
  normLeft : ∀x∈Ioc 0 1, ‖Z (left x)‖=radius x
  normRight : ∀x∈Ioc 0 1, ‖Z (right x)‖=radius x
  distinct : ∀x∈Ioc 0 1,left x≠right x
  exhaustion : ∀x∈Ioc 0 1,∀t,‖Z t‖=radius x → t=left x ∨ t=right x
  phase : ∀x∈Ioc 0 1,Z (right x)=rot (delta x)*Z (left x)
  cross : ∀x∈Ioc 0 1,wedge (radial (Z (right x)) (V (right x))) (radial (Z (left x)) (V (left x)))≠0

namespace Arms
variable {A : Type*} {Z V : A→ℂ} (a : Arms Z V)

private theorem grid_exists {d : ℕ} (hd : 0<d) (j : Fin (d/200)) :
    ∃x∈Ioc (0:ℝ) 1, a.delta x=((j.val+1:ℕ):ℝ)/d := by
  have jd : j.val+1≤d/200 := j.isLt
  have h := (Nat.mul_le_mul_right 200 jd).trans (Nat.div_mul_le_self d 200)
  have n : (0:ℝ)<d := by exact_mod_cast hd
  have gt : 0<((j.val+1:ℕ):ℝ)/d := by positivity
  have bound : ((j.val+1:ℕ):ℝ)/d ≤ 1/200 := by
    apply (div_le_iff₀ n).mpr
    have raw : ((j.val+1:ℕ):ℝ)*200≤d := by exact_mod_cast h
    linarith
  obtain ⟨x,hx,eq⟩ := intermediate_value_Icc (show (0:ℝ)≤1 by norm_num) a.cont
    (show ((j.val+1:ℕ):ℝ)/d∈Icc (a.delta 0) (a.delta 1) from ⟨by rw [a.atTip]; exact gt.le,bound.trans a.width⟩)
  refine ⟨x,⟨lt_of_le_of_ne hx.1 (fun e=>?_ ),hx.2⟩,eq⟩
  subst x; linarith only [a.atTip,gt,eq]

include a in
/-- A genuine set of distinct ordinary double image points of the d
rotated blocks, with at least d floor(d/200) elements. -/
theorem many_ordinary {d : ℕ} (hd : 0<d) :
    ∃ S : Finset ℂ, S.card=d*(d/200) ∧ ∀ y∈S, Ordinary (copies Z d) (copies V d) y := by
  classical
  choose x hx hit using (fun j : Fin (d/200) => grid_exists a hd j)
  let Y := fun ij : Fin d × Fin (d/200) => copies Z d (ij.1,a.right (x ij.2))
  have unit (m : ℕ) : ‖zeta d^m‖=1 := by rw [norm_pow,zeta_norm,one_pow]
  have sizes (i : Fin d) (t : A) : ‖copies Z d (i,t)‖=‖Z t‖ := by
    simp only [copies,norm_mul,unit,one_mul]
  have separate {u v : Fin d} {w : ℂ} (nz : w≠0) (eq : zeta d ^ u.val*w=zeta d ^ v.val*w) : u=v :=
    power_inj hd (mul_right_cancel₀ nz eq)
  have dn (j : Fin (d/200)) : Z (a.right (x j))≠0 := fun bad=>by
    have h := a.normRight _ (hx j); rw [bad,norm_zero] at h
    linarith only [h,a.positive _ (hx j)]
  have inj : Function.Injective Y := by
    rintro ⟨i,j⟩ ⟨k,l⟩ eq
    have same := congrArg norm eq
    change ‖copies Z d (i,a.right (x j))‖=‖copies Z d (k,a.right (x l))‖ at same
    rw [sizes,sizes,a.normRight _ (hx j),a.normRight _ (hx l)] at same
    have xeq := a.rad_inj (hx j) (hx l) same
    have ee := congrArg a.delta xeq
    rw [hit j,hit l] at ee
    have dne : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    have idx := (div_left_inj' dne).mp ee
    have jl : j=l := Fin.ext (by exact_mod_cast Nat.add_right_cancel (show j.val+1=l.val+1 by exact_mod_cast idx))
    subst l
    exact Prod.ext (separate (dn j) eq) rfl
  let S := Finset.univ.image Y
  refine ⟨S,?_,?_⟩
  · simp [S,Finset.card_image_of_injective _ inj,Fintype.card_prod]
  · intro y hy
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hy
    let r := x j
    let u := a.right r
    let v := a.left r
    let k : Fin d := ⟨(i.val+(j.val+1))%d,Nat.mod_lt _ hd⟩
    have hr : r∈Ioc 0 1 := hx j
    have ph : Z u=zeta d^(j.val+1)*Z v := by
      dsimp [u,v]; rw [a.phase r hr,hit j,rot_fraction]
    have point : copies Z d (k,v)=copies Z d (i,u) := by
      change zeta d^((i.val+(j.val+1))%d)*Z v=zeta d^i.val*Z u
      rw [root_mod hd,pow_add,ph,mul_assoc]
    have nz : Z v≠0 := fun bad=>by
      have h := a.normLeft r hr
      change ‖Z v‖=a.radius r at h
      rw [bad,norm_zero] at h; linarith only [h,a.positive r hr]
    refine ⟨(i,u),(k,v),fun eq=>a.distinct r hr (congrArg Prod.snd eq).symm,
      rfl,point,?_,?_⟩
    · rintro ⟨w,t⟩ eq
      have raw := congrArg norm eq
      change ‖copies Z d (w,t)‖=‖copies Z d (i,u)‖ at raw
      rw [sizes,sizes,a.normRight r hr] at raw
      rcases a.exhaustion r hr t raw with ev|eu
      · change t=v at ev; subst t
        exact Or.inr (Prod.ext (separate nz (eq.trans point.symm)) rfl)
      · change t=u at eu; subst t
        exact Or.inl (Prod.ext (separate (dn j) eq) rfl)
    · intro zero
      have transv := a.cross r hr
      have one := radial_rot (unit i.val) (Z u) (V u)
      have two := radial_rot (unit k.val) (Z v) (V v)
      change radial (copies Z d (i,u)) (copies V d (i,u))=radial (Z u) (V u) at one
      change radial (copies Z d (k,v)) (copies V d (k,v))=radial (Z v) (V v) at two
      change wedge (radial (Z u) (V u)) (radial (Z v) (V v))≠0 at transv
      rw [←one,←two,point,wedge_radial,zero,mul_zero] at transv
      exact transv rfl

end Arms
end SolitonClassification.Rotating.ArmCount
#print axioms SolitonClassification.Rotating.ArmCount.Arms.many_ordinary
