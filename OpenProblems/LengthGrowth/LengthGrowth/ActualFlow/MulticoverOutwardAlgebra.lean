import LengthGrowth.ActualFlow.MulticoverSharpLength

noncomputable section
open Set
namespace LengthGrowth.Multicover.Outward

structure Integrals where
  turn : ℝ
  square : ℝ
  rate : ℝ
  diss : ℝ

def Errors (R u : ℝ) (v : Integrals) : Prop :=
  |v.turn|≤R ∧ |v.square-(9/8)*u|≤R ∧ |v.rate-(81/256)*u|≤R ∧ |v.diss-(729/4096)*u|≤R

def defect (m u : ℝ) (v:Integrals) :=
  4*((Real.pi*m-v.turn)*(u+2+v.square-2*v.turn)+(u+2)*v.square-v.turn^2)

def outwardRate (m u : ℝ) (v:Integrals) :=
  (Real.pi*m-v.turn)*(2*v.rate-4*v.diss+v.square-(u+2))+2*v.square*v.rate-4*(u+2)*v.diss

theorem uniform_outward {m u R:ℝ} (hr:1≤R) (hm:1000*R≤m) (hu:512*R≤u)
    (v:Integrals) (h:Errors R u v) : 0<outwardRate m u v := by
  rcases h with ⟨ha,hb,hj,hd⟩
  let x:=v.square-9/8*u
  let y:=v.rate-81/256*u
  let z:=v.diss-729/4096*u
  have bx : -R≤x ∧ x≤R:=abs_le.mp hb
  have by' : -R≤y ∧ y≤R:=abs_le.mp hj
  have bz : -R≤z ∧ z≤R:=abs_le.mp hd
  have rp : 0<R:=by linarith
  have mp : 0<m:=by linarith
  have up : 0<u:=by linarith
  have mix : u/40≤2*v.rate-4*v.diss+v.square-(u+2):=by
    dsimp only [x,y,z] at bx by' bz
    linarith
  have t : 880*R<Real.pi*m-v.turn:=by
    linarith only [mul_lt_mul_of_pos_right Real.pi_gt_three mp,hm,(abs_le.mp ha).2,rp]
  have tpos : 0<Real.pi*m-v.turn:=by linarith only [t,rp]
  have lower:=mul_le_mul_of_nonneg_left mix tpos.le
  have big:=mul_lt_mul_of_pos_right t up
  have xy : -(R*R)≤x*y:=by
    have a:=mul_le_mul hb hj (abs_nonneg _) rp.le
    rw [←abs_mul] at a
    exact (abs_le.mp a).1
  have co : -12*R≤9/4*y+81/128*x-4*z-729/512:=by linarith
  have diff : 2*v.square*v.rate-4*(u+2)*v.diss=
      (9/4*y+81/128*x-4*z-729/512)*u+2*x*y-8*z:=by dsimp only [x,y,z];ring
  have tail : -22*u*R≤2*v.square*v.rate-4*(u+2)*v.diss:=by
    rw [diff]
    have ur:=mul_le_mul_of_nonneg_right (by linarith : R≤u) rp.le
    have ur':=mul_le_mul_of_nonneg_right (by linarith : 1≤u) rp.le
    linarith only [mul_le_mul_of_nonneg_right co up.le,xy,bz.2,ur,ur']
  unfold outwardRate
  linarith only [big,lower,tail]

theorem defect_lower {m u R:ℝ} (hr:1≤R) (hm:1000*R≤m) (hu:512*R≤u)
    (v:Integrals) (h:Errors R u v) : u^2≤defect m u v := by
  rcases h with ⟨ha,hb,_,_⟩
  have rp : 0≤R:=by linarith
  have mp : 0<m:=by linarith
  have up : 0<u:=by linarith
  have a:=abs_le.mp ha
  have b:=abs_le.mp hb
  have t : 0≤Real.pi*m-v.turn:=by linarith only [mul_lt_mul_of_pos_right Real.pi_gt_three mp,hm,a.2,rp]
  have vp : u≤v.square:=by linarith
  have term:=mul_nonneg t (by linarith : 0≤u+2+v.square-2*v.turn)
  have sq:=pow_le_pow_left₀ (abs_nonneg _) ha 2
  rw [sq_abs] at sq
  have ur:=pow_le_pow_left₀ rp (by linarith : R≤u/2) 2
  have prod:=mul_le_mul_of_nonneg_left vp (by linarith : 0≤u+2)
  unfold defect
  nlinarith only [sq,ur,term,prod,up,sq_nonneg u]

theorem initial_defect_upper {m R:ℝ} (hr:1≤R) (hm:1000*R≤m) (v:Integrals)
    (h:Errors R (512*R) v) : defect m (512*R) v≤30000*R*m := by
  rcases h with ⟨ha,hb,_,_⟩
  have rp : 0<R:=by linarith
  have mp : 0<m:=by linarith
  have a:=abs_le.mp ha
  have b:=abs_le.mp hb
  have t : Real.pi*m-v.turn≤5*m:=by linarith only [mul_lt_mul_of_pos_right Real.pi_lt_four mp,hm,a.1,rp]
  have fact : 512*R+2+v.square-2*v.turn≤1100*R:=by linarith
  have nn : 0≤512*R+2+v.square-2*v.turn:=by linarith
  have t1:=mul_le_mul t fact nn (by positivity)
  have t2:=mul_le_mul (by linarith : 512*R+2≤514*R) (by linarith : v.square≤580*R)
    (by linarith : 0≤v.square) (by positivity)
  have rm:=mul_le_mul_of_nonneg_left hm rp.le
  unfold defect
  nlinarith only [t1,t2,rm,sq_nonneg v.turn,mul_nonneg rp.le mp.le]

theorem crosses_every_high_boundary (v : ℝ→Integrals) (R : ℝ) (hr : 1≤R)
    (error : ∀u,512*R≤u → Errors R u (v u))
    (cont : ∀m,ContinuousOn (fun u=>defect m u (v u)) (Ici (512*R)))
    {m K:ℝ} (hm:1000*R≤m) (hk:30000*R*m≤K) :
    ∃u,512*R≤u ∧ defect m u (v u)=K ∧ 0<outwardRate m u (v u) := by
  let a:=512*R
  let b:=K+a+1
  have kp : 0≤K:=by
    have mp : 0≤m:=by linarith
    linarith only [hk,mul_nonneg (show 0≤30000*R by linarith) mp]
  have ab : a≤b:=by dsimp only [b];linarith
  have ba : 512*R≤b:=ab
  have bot:=initial_defect_upper hr hm (v a) (error a le_rfl)
  have top:=defect_lower hr hm ba (v b) (error b ba)
  have comp : K≤b^2:=by
    have b1 : 1≤b:=by dsimp [b,a];linarith
    have bK : K≤b:=by dsimp [b,a];linarith
    nlinarith only [b1,bK,sq_nonneg (b-1)]
  obtain ⟨u,hu,eq⟩:=intermediate_value_Icc ab ((cont m).mono Icc_subset_Ici_self)
    (show K∈Icc (defect m a (v a)) (defect m b (v b)) from ⟨bot.trans hk,comp.trans top⟩)
  exact ⟨u,hu.1,eq,uniform_outward hr hm hu.1 (v u) (error u hu.1)⟩

end LengthGrowth.Multicover.Outward
#print axioms LengthGrowth.Multicover.Outward.crosses_every_high_boundary
