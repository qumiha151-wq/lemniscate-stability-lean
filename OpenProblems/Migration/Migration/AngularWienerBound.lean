import Migration.AngularReconstruction

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.AngularGauge

variable {B : Type*} [NormedCommRing B]

private theorem product_diff {a b c d : B} {M N : ℝ} (ha : ‖a‖≤M) (hd : ‖d‖≤N) :
    ‖a*b-c*d‖≤M*‖b-d‖+‖a-c‖*N := calc
  _ = ‖a*(b-d)+(a-c)*d‖ := by congr 1; ring
  _ ≤ ‖a*(b-d)‖+‖(a-c)*d‖ := norm_add_le .. 
  _ ≤ _ := add_le_add ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _)))
    ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _)))

private theorem sq_bound {a : B} {V : ℝ} (ha : ‖a‖≤V) : ‖a^2‖≤V^2 := by
  rw [pow_two,pow_two]
  exact (norm_mul_le ..).trans (mul_self_le_mul_self (norm_nonneg _) ha)

private theorem sq_diff {a b : B} {M : ℝ} (ha : ‖a‖≤M) (hb : ‖b‖≤M) :
    ‖a^2-b^2‖≤2*M*‖a-b‖ := by
  have p := product_diff (b:=a) (c:=b) ha hb
  rw [pow_two,pow_two]; linarith only [p]

variable [NormedAlgebra ℝ B]

def angularNonlinearity (D : B →L[ℝ] B) (v w : B) : B :=
  (-(5/2) : ℝ) • (v^2*w)+v*D (w^2-(1/2:ℝ) • v^4)

/-- A contractive primitive and a submultiplicative algebra suffice for
the derivative loss estimate of the actual equiarclength angle equation. -/
theorem angular_lipschitz (D : B →L[ℝ] B) (op : ∀a,‖D a‖≤‖a‖)
    {v w v' w' : B} {V W : ℝ} (av : ‖v‖≤V) (av' : ‖v'‖≤V)
    (aw : ‖w‖≤W) (aw' : ‖w'‖≤W) :
    ‖angularNonlinearity D v w-angularNonlinearity D v' w'‖ ≤
    (5*V*W+W^2+(5/2)*V^4)*‖v-v'‖+((5/2)*V^2+2*V*W)*‖w-w'‖ := by
  let S := fun a b : B => b^2-(1/2:ℝ) • a^4
  have vn := (norm_nonneg _).trans av
  have wn := (norm_nonneg _).trans aw
  have v2 := sq_diff av av'
  have w2 := sq_diff aw aw'
  have v4 : ‖v^4-v'^4‖≤4*V^3*‖v-v'‖ := by
    have t := (sq_diff (sq_bound av) (sq_bound av')).trans
      (mul_le_mul_of_nonneg_left v2 (show 0≤2*V^2 by positivity))
    rw [show v^4=(v^2)^2 by ring,show v'^4=(v'^2)^2 by ring]
    linarith only [t]
  have setbound : ‖D (S v' w')‖≤W^2+V^4/2 := by
    apply (op _).trans
    refine (norm_sub_le ..).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    have fourth := sq_bound (sq_bound av')
    rw [show v'^4=(v'^2)^2 by ring]
    linarith only [fourth,sq_bound aw']
  have ds : ‖D (S v w)-D (S v' w')‖≤ 2*W*‖w-w'‖+2*V^3*‖v-v'‖ := by
    rw [← D.map_sub]
    apply (op _).trans
    have ef : S v w-S v' w'=(w^2-w'^2)-(1/2:ℝ) • (v^4-v'^4) := by
      dsimp [S]; rw [smul_sub]; abel
    rw [ef]
    refine (norm_sub_le ..).trans ?_
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by norm_num : 0≤(1/2:ℝ))]
    linarith only [v4,w2]
  have p := product_diff (b:=w) (c:=v'^2) (sq_bound av) aw'
  have q := product_diff (b:=D (S v w)) (c:=v') av setbound
  have u := mul_le_mul_of_nonneg_right v2 wn
  have z := mul_le_mul_of_nonneg_left ds vn
  have ident : angularNonlinearity D v w-angularNonlinearity D v' w'=
      (-(5/2):ℝ) • (v^2*w-v'^2*w') + (v*D (S v w)-v'*D (S v' w')) := by
    unfold angularNonlinearity; dsimp [S]; rw [smul_sub]; abel
  rw [ident]
  apply (norm_add_le ..).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (by norm_num : (-(5/2):ℝ)≤0)]
  linarith only [p,q,u,z]

/-- The uniform first-contact estimate on a closed time interval. -/
theorem slab_barrier {h r q : ℝ} {err : ℝ→ℝ}
    (ct : ContinuousOn err (Icc 0 h)) (start : err 0<r) (small : q<r)
    (cap : ∀t∈Icc 0 h,(∀s∈Icc 0 t,err s≤r) → err t≤q) :
    ∀t∈Icc 0 h,err t<r := by
  intro t ht
  by_contra! no
  have sub : Icc (0:ℝ) t ⊆ Icc 0 h := fun _ m => ⟨m.1,m.2.trans ht.2⟩
  have ev := intermediate_value_Icc ht.1 (ct.mono sub) (show r∈Icc (err 0) (err t) from ⟨start.le,no⟩)
  let closed := (Icc 0 t) ∩ err ⁻¹' ({r} : Set ℝ)
  have cl : IsClosed closed := (ct.mono sub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have cc : IsCompact closed := isCompact_Icc.of_isClosed_subset cl inter_subset_left
  obtain ⟨s,hs,min⟩ := cc.exists_isMinOn (show closed.Nonempty by
    obtain ⟨s,hs,eq⟩ := ev
    exact ⟨s,hs,eq⟩) continuous_id.continuousOn
  have sr : err s=r := hs.2
  have bound (u : ℝ) (hu : u∈Icc 0 s) : err u≤r := by
    by_contra! gt
    have us : Icc (0:ℝ) u ⊆ Icc 0 h := fun _ m=>sub ⟨m.1,(m.2.trans hu.2).trans hs.1.2⟩
    obtain ⟨k,hk,ek⟩ := intermediate_value_Icc hu.1 (ct.mono us) (show r∈Icc (err 0) (err u) from ⟨start.le,gt.le⟩)
    have ks : s≤k := min (show k∈closed from ⟨⟨hk.1,(hk.2.trans hu.2).trans hs.1.2⟩,ek⟩)
    have ku : k=u := le_antisymm hk.2 (hu.2.trans ks)
    exact gt.ne' (ku ▸ ek)
  linarith only [cap s (sub hs.1) bound,sr,small]

end MigrationGeometry.AngularGauge
#print axioms MigrationGeometry.AngularGauge.angular_lipschitz
#print axioms MigrationGeometry.AngularGauge.slab_barrier
