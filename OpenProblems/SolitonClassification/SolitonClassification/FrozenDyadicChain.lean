import SolitonClassification.FrozenDyadicRow

/-! Physical error transport for a succession of exact integer joins. -/
namespace ClosedSimilarity.FrozenStress.Endpoint
open IntegerPoly Set
noncomputable section
set_option exponentiation.threshold 1024

structure Mark where
  k : ℤ
  v : ℤ
  p : ℤ
  q : ℤ
  deriving DecidableEq

def markState (m : Mark) : State := ![(m.k:ℝ)/S,(m.v:ℝ)/(8*S),(m.p:ℝ)/S,(m.q:ℝ)/S]
def startMark (r : Row) : Mark :=
  ⟨r.k.headD 0,r.v.headD 0,r.p.headD 0,r.q.headD 0⟩
def finishMark (r : Row) : Mark := ⟨r.k.sum,r.v.sum,r.p.sum,r.q.sum⟩
def clock (n : ℕ) : ℝ := (n:ℝ)/32
def budget (t : ℝ) : ℝ := (1/2^432)/13*(Real.exp (13*t)-1)
def Transports (i j : ℕ) (a b : Mark) : Prop :=
  ∀ (z : Orbit),z.radial 0=0 → |z.transverse 0|≤1 →
    ‖state z (clock i)-markState a‖≤budget (clock i) →
    ‖state z (clock j)-markState b‖≤budget (clock j)

theorem Transports.trans {i j k : ℕ} {a b c : Mark}
    (h : Transports i j a b) (g : Transports j k b c) : Transports i k a c :=
  fun z zr zb ha => g z zr zb (h z zr zb ha)

private theorem value_zero (p : P) : value p 0=(p.headD 0:ℤ) := by
  cases p <;> simp [value,List.headD]

private theorem value_one (p : P) : value p 1=(p.sum:ℤ) := by
  induction p with
  | nil => simp [value]
  | cons a p ih => simp [value,ih]

theorem transport_one (r : Row) (j : ℕ) (hj : j<640) (hr : Good r) :
    Transports j (j+1) (startMark r) (finishMark r) := by
  let a := clock j
  let b := clock (j+1)
  have step : b=a+1/32 := by simp only [a,b,clock,Nat.cast_add,Nat.cast_one]; ring
  have a0 : 0≤a := by dsimp [a,clock]; positivity
  have b20 : b≤20 := by
    have hj' : ((j+1:ℕ):ℝ)≤640 := by exact_mod_cast (show j+1≤640 by omega)
    dsimp [b,clock]
    linarith
  have ha : r.atTime a a=markState (startMark r) := by
    simp only [Row.atTime,startMark,markState,sub_self,mul_zero,value_zero]
  have hb : r.atTime a b=markState (finishMark r) := by
    have e : 32*(b-a)=1 := by rw [step]; ring
    simp only [Row.atTime,finishMark,markState,e,value_one]
  intro z zr zb hstart
  have hc : Continuous (state z) := continuous_iff_continuousAt.mpr (fun t => (state_deriv z t).continuousAt)
  have hp : Continuous (r.atTime a) := continuous_iff_continuousAt.mpr (fun t => (r.derivative a t).continuousAt)
  have interval (t : ℝ) (ht : t∈Ico a b) : |32*(t-a)|≤1 := by
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2]
  have error := norm_le_gronwallBound_of_norm_deriv_right_le (K:=13) (ε:=1/2^432)
    ((hc.sub hp).continuousOn (s:=Icc a b))
    (fun t _ => (state_deriv z t).hasDerivWithinAt.sub (r.derivative a t).hasDerivWithinAt)
    (δ:=budget a) (by simpa only [Pi.sub_apply,ha] using hstart) (fun t ht => by
      have bound := orbit_tube z zr zb (t:=t) (show t∈Icc 0 20 from
        ⟨a0.trans ht.1,ht.2.le.trans b20⟩)
      have f := field_comparison (state z t) (r.atTime a t) bound
        (r.cap hr a t (interval t ht)) (unit_bounds z t).1 (unit_bounds z t).2
      have d := r.defect hr a t (interval t ht)
      rw [norm_sub_rev] at d
      simp only [T,Nat.cast_pow,Nat.cast_ofNat] at d
      exact (norm_sub_le_norm_sub_add_norm_sub _ (field (r.atTime a t)) _).trans (add_le_add f d))
    b ⟨by linarith,le_rfl⟩
  change ‖state z b-markState (finishMark r)‖≤budget b
  simp only [Pi.sub_apply,hb,gronwallBound_of_K_ne_0 (by norm_num : (13:ℝ)≠0)] at error
  apply error.trans_eq
  unfold budget
  calc
    _ = 1/2^432/13*(Real.exp (13*a)*Real.exp (13*(b-a))-1) := by ring
    _ = _ := by rw [←Real.exp_add]; ring_nf

theorem budget_end : budget (clock 640)≤1/2^20 := by
  have e : Real.exp (1/16)≤16/15 := by
    exact (Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ)≤1/16) (by norm_num)).trans (by norm_num)
  have one : Real.exp 1 ≤ 3 := by
    rw [show (1:ℝ)=(16:ℕ)*(1/16:ℝ) by norm_num,Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le e 16).trans (by norm_num)
  have large : Real.exp (13*clock 640)≤(3:ℝ)^260 := by
    rw [show 13*clock 640=(260:ℕ)*(1:ℝ) by norm_num [clock], Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le one 260
  unfold budget
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right large 1) (by positivity)).trans (by norm_num)

theorem zero_to_twenty {a b : Mark} (h : Transports 0 640 a b) (z : Orbit)
    (zr : z.radial 0=0) (zb : |z.transverse 0|≤1) (init : state z 0=markState a) :
    ‖state z 20-markState b‖≤1/2^20 := by
  have he := h z zr zb (by simp [clock,budget,init])
  exact (show ‖state z 20-markState b‖≤budget (clock 640) from by convert! he using 1; norm_num [clock]).trans budget_end

end
end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.transport_one
#print axioms ClosedSimilarity.FrozenStress.Endpoint.zero_to_twenty
