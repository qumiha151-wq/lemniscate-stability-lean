import LengthGrowth.ActualFlow.MulticoverPeriodic

noncomputable section
open MeasureTheory Set Function
namespace LengthGrowth.Multicover

private theorem numerical_impossible {A V P : ℝ} (big : 7/4≤A) (cap : V≤6/5) (six : 6≤P)
    (estimate : A^2≤V/P+V*Real.sqrt ((A^2+4*A+1)/2)) : False := by
  let K := (A^2+4*A+1)/2
  have kp : 0≤K := by dsimp [K]; nlinarith only [big,sq_nonneg A]
  have m : V/P≤1/5 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h := mul_le_mul_of_nonneg_right cap (Real.sqrt_nonneg K)
  change A^2≤V/P+V*Real.sqrt K at estimate
  have first : 5*A^2-1≤6*Real.sqrt K := by linarith
  have a2 : (7/4:ℝ)^2≤A^2 := pow_le_pow_left₀ (by norm_num) big 2
  have z := pow_le_pow_left₀ (by nlinarith only [a2] : 0≤5*A^2-1) first 2
  let x:=A-7/4
  have pos : 0≤x := sub_nonneg.mpr big
  have poly : 0<25*A^4-28*A^2-72*A-17 := by
    rw [show 25*A^4-28*A^2-72*A-17=25*x^4+175*x^3+(3451/8)*x^2+(5855/16)*x+1465/256 by dsimp[x];ring]
    positivity
  rw [mul_pow,Real.sq_sqrt kp] at z
  dsimp [K] at z
  nlinarith only [z,poly]

def normalizedForce (u u₂ : Fn) : Fn := u₂+(1/2:ℝ) • (u^3)

theorem strict_record (P : ℝ) (six : 6≤P) (u u₁ u₂ : Fn) (pu : Periodic u P) (pu₁ : Periodic u₁ P)
    (du : ∀t,HasDerivAt u (u₁ t) t) (du₁ : ∀t,HasDerivAt u₁ (u₂ t) t)
    (unit : mass P (u^2)=P) (posV : 0<mass P ((u-1)^2)) (cap : mass P ((u-1)^2)≤6/5) :
    (1/2:ℝ)*mass P (u*normalizedForce u u₂)<mass P ((normalizedForce u u₂)^2) := by
  by_contra! record
  let v : Fn := u-1
  let f := normalizedForce u u₂
  let r : Fn := (4:ℝ) • f-u-1
  let V := mass P (v^2)
  have hp : 0<P := by linarith
  obtain ⟨y,hy,peak⟩ := isCompact_Icc.exists_isMaxOn (show (Icc (0:ℝ) P).Nonempty from ⟨0,le_rfl,hp.le⟩)
    v.continuous.abs.continuousOn
  let A := |v y|
  have ap : 0≤A := abs_nonneg _
  have dz := deriv_mass_zero P u₁ u₂ pu₁ du₁
  have poly : r^2 + (7:ℝ) • v^2 + (4:ℝ) • v^3 - (16:ℝ) • f^2 + (8:ℝ) • (u*f) =
       (-8:ℝ) • u₂ - (4:ℝ) • (u^2-1) := by
    ext t; simp [r,f,v,normalizedForce,smul_eq_mul]; ring
  have identity := congrArg (mass P) poly
  simp only [map_add,map_sub,map_smul,smul_eq_mul,unit,mass_one,dz] at identity
  have cub : -A*V≤mass P (v^3) := by
    have mono := mass_mono P hp.le ((-A) • v^2) (v^3) (by
      intro t ht
      simp only [ContinuousMap.smul_apply,ContinuousMap.pow_apply,smul_eq_mul]
      have bound : |v t|≤A := peak ht
      nlinarith only [mul_nonneg (by linarith only [(abs_le.mp bound).1] : 0≤v t+A) (sq_nonneg (v t))])
    rw [map_smul,smul_eq_mul] at mono
    exact mono
  change mass P (f^2)≤(1/2:ℝ)*mass P (u*f) at record
  have resid : mass P (r^2)≤(4*A-7)*V := by dsimp only [V] at *; linarith only [identity,record,cub]
  have rv := mass_sq_nonneg P hp.le r
  have big : 7/4≤A := by
    by_contra! small
    have bad := mul_neg_of_neg_of_pos (by linarith : 4*A-7<0) posV
    exact (not_lt_of_ge (rv.trans resid)) bad
  have nv : 0≤norm2 P v := Real.sqrt_nonneg _
  have nr : norm2 P r≤(2*A-3)*norm2 P v := by
    apply le_of_sq_le_sq _ (mul_nonneg (by linarith) nv)
    rw [mul_pow,norm_sq P hp.le r,norm_sq P hp.le v]
    exact resid.trans (mul_le_mul_of_nonneg_right (by nlinarith only [sq_nonneg (A-2)]) posV.le)
  let q : Fn := (2:ℝ) • v^3+(6:ℝ) • v^2+(5:ℝ) • v
  have nq : norm2 P q≤(2*A^2+6*A+5)*norm2 P v := by
    apply norm_pointwise P hp.le (by positivity)
    intro t ht
    have bound : |v t|≤A := peak ht
    have hsq := pow_le_pow_left₀ (abs_nonneg _) bound 2
    rw [sq_abs] at hsq
    have h1 := (abs_le.mp bound).2
    have h2 := (abs_le.mp bound).1
    have factor : |2*(v t)^2+6*v t+5|≤2*A^2+6*A+5 := abs_le.mpr ⟨by nlinarith only [h2,sq_nonneg (v t),sq_nonneg A],by linarith⟩
    change |q t|≤_
    rw [show q t=(2*(v t)^2+6*v t+5)*v t by simp [q,smul_eq_mul];ring,abs_mul]
    exact mul_le_mul_of_nonneg_right factor (abs_nonneg _)
  have sub : (4:ℝ) • u₂=r-q := by ext t; simp [r,q,f,v,normalizedForce,smul_eq_mul];ring
  have mulnorm := norm_sub P hp.le r q
  rw [←sub,norm_smul P hp.le (by norm_num)] at mulnorm
  let K := (A^2+4*A+1)/2
  have d2 : norm2 P u₂ ≤ K*norm2 P v := by dsimp [K]; linarith only [mulnorm,nr,nq]
  have kp : 0≤K := by dsimp [K];positivity
  have pv : Periodic v P := fun t=>by simp [v,pu t]
  have dv (t) : HasDerivAt v (u₁ t) t := (du t).sub_const 1
  have g := gradient_norm_sq P hp.le v u₁ u₂ pv pu₁ dv du₁
  have d1 : norm2 P u₁ ≤ Real.sqrt K*norm2 P v := by
    apply le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg _) nv)
    rw [mul_pow,Real.sq_sqrt kp]
    exact g.trans ((mul_le_mul_of_nonneg_left d2 nv).trans_eq (by ring))
  have e := sup_square P hp v u₁ pv pu₁ dv y hy
  have bound := mul_le_mul_of_nonneg_left d1 nv
  apply numerical_impossible (V:=V) big cap six
  change A^2≤V/P+V*Real.sqrt K
  have left : A^2=(v y)^2 := sq_abs _
  have vv : norm2 P v*(Real.sqrt K*norm2 P v)=V*Real.sqrt K := by
    rw [show norm2 P v*(Real.sqrt K*norm2 P v)=(norm2 P v)^2*Real.sqrt K by ring,norm_sq P hp.le]
  exact left.trans_le (e.trans (add_le_add_right (bound.trans_eq vv) _))

end LengthGrowth.Multicover
#print axioms LengthGrowth.Multicover.strict_record
