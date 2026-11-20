import SolitonClassification.FrozenStress
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace ClosedSimilarity.FrozenStress.Incoming
open Set

/-- h and I are respectively the radial and transverse stresses divided by
    the square root of the amplitude. Thus r is the square root of amplitude. -/
def r (I h : ℝ) := Real.sqrt (h^2+I^2)
def numerator (U w I h : ℝ) := U*w*(h^2-I^2)+U^3*h*I
def height (U w I h : ℝ) := r I h*h+numerator U w I h/(3*(r I h)^3)

lemma components (I h : ℝ) : |h| ≤ r I h ∧ |I| ≤ r I h := by
  constructor <;> rw [←Real.sqrt_sq_eq_abs] <;> apply Real.sqrt_le_sqrt <;>
    linarith [sq_nonneg h,sq_nonneg I]

lemma height_eq (U w R a b : ℝ) (hR : 0 < R) (unit : a^2+b^2=1) :
    height U w (R*b) (R*a) = R^2*a+chi U w a b/R := by
  have rr : r (R*b) (R*a) = R := by
    unfold r
    rw [show (R*a)^2+(R*b)^2=R^2 by nlinarith only [congrArg (fun x : ℝ => R^2*x) unit],
      Real.sqrt_sq hR.le]
  unfold height numerator chi
  rw [rr]
  field_simp [hR.ne']

/-- The coordinate chart works uniformly in the transverse stress, including
    impacts arbitrarily close to tangency. -/
theorem height_derivative {U w I h : ℝ} (hU : |U| ≤ 2) (hw : |w| ≤ 1) (large : 4 ≤ r I h) :
    ∃ v ≥ (1:ℝ), HasDerivAt (height U w I) v h := by
  let R := r I h
  have pos : 0 < R := lt_of_lt_of_le (by norm_num) large
  have ss : 0 < h^2+I^2 := Real.sqrt_pos.mp pos
  have dr : HasDerivAt (r I) (h/R) h := by
    convert! (((hasDerivAt_id h).pow 2).add_const (I^2)).sqrt ss.ne' using 1
    dsimp [R,r]; ring
  let Q := numerator U w I h
  let Q' := 2*U*w*h+U^3*I
  have dq : HasDerivAt (numerator U w I) Q' h := by
    convert! ((((hasDerivAt_id h).pow 2).sub_const (I^2)).const_mul (U*w)).add
      (((hasDerivAt_id h).const_mul (U^3)).mul_const I) using 1
    dsimp [Q']; ring
  let v := R+h^2/R+Q'/(3*R^3)-Q*h/R^5
  have dv : HasDerivAt (height U w I) v h := by
    convert! (dr.mul (hasDerivAt_id h)).add
      (dq.div ((dr.pow 3).const_mul 3) (show 3*R^3 ≠ 0 by positivity)) using 1
    dsimp [v,Q,R] at *
    field_simp [pos.ne']; ring
  obtain ⟨hx,hy⟩ := components I h
  change |h| ≤ R at hx
  change |I| ≤ R at hy
  have uw : |U*w| ≤ 2 := by simpa only [abs_mul,mul_one] using
    (mul_le_mul hU hw (abs_nonneg _) (by norm_num : (0:ℝ)≤2))
  have u3 : |U^3| ≤ 8 := by rw [abs_pow]; nlinarith only [pow_le_pow_left₀ (abs_nonneg U) hU 3]
  have rr : R^2=h^2+I^2 := Real.sq_sqrt ss.le
  have diff : |h^2-I^2| ≤ R^2 := abs_le.mpr ⟨by linarith [sq_nonneg h],by linarith [sq_nonneg I]⟩
  have qcap : |Q| ≤ 10*R^2 := by
    unfold Q numerator
    apply (abs_add_le _ _).trans
    rw [abs_mul (U*w),abs_mul (U^3*h),abs_mul (U^3)]
    nlinarith only [mul_le_mul uw diff (abs_nonneg _) (by norm_num),
      mul_le_mul (mul_le_mul u3 hx (abs_nonneg _) (by norm_num)) hy (abs_nonneg _) (by positivity)]
  have qpcap : |Q'| ≤ 12*R := by
    dsimp [Q']
    apply (abs_add_le _ _).trans
    rw [show 2*U*w*h = 2*(U*w)*h by ring,abs_mul (2*(U*w)),abs_mul (2:ℝ),abs_mul (U^3)]
    rw [abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith only [mul_le_mul (show 2*|U*w| ≤ 4 by linarith) hx (abs_nonneg _) (by norm_num),
      mul_le_mul u3 hy (abs_nonneg _) (by norm_num)]
  have first : |Q'/(3*R^3)| ≤ 4/R^2 := by
    rw [abs_div,abs_of_pos (by positivity : 0 < 3*R^3)]
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ 12*R := qpcap
      _ = _ := by field_simp [pos.ne']; ring
  have second : |Q*h/R^5| ≤ 10/R^2 := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < R^5)]
    apply (div_le_iff₀ (by positivity)).mpr
    convert mul_le_mul qcap hx (abs_nonneg _) (by positivity) using 1
    field_simp
  have big : 16 ≤ R^2 := by nlinarith only [large, sq_nonneg (R-4)]
  have err : 4/R^2+10/R^2 ≤ 1 := by rw [←add_div]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  exact ⟨v,by dsimp [v]; linarith [(abs_le.mp first).1,(abs_le.mp second).2,div_nonneg (sq_nonneg h) pos.le],dv⟩

theorem height_injective {U w I x y : ℝ} (hU : |U| ≤ 2) (hw : |w| ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (rx : 4 ≤ r I x) (ry : 4 ≤ r I y)
    (same : height U w I x = height U w I y) : x=y := by
  have inc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (r0 : 4 ≤ r I a) :
      height U w I a < height U w I b := by
    have hh (t : ℝ) (ht : t ∈ Icc a b) := height_derivative (I := I) (h := t) hU hw
      (r0.trans (Real.sqrt_le_sqrt (by nlinarith only [pow_le_pow_left₀ ha ht.1 2])))
    apply strictMonoOn_of_deriv_pos (convex_Icc a b)
      (fun t ht => by obtain ⟨_,_,der⟩ := hh t ht; exact der.continuousAt.continuousWithinAt)
      (fun t ht => by
        obtain ⟨_,lo,der⟩ := hh t (interior_subset ht)
        rw [der.deriv]; linarith) ⟨le_rfl,hab.le⟩ ⟨hab.le,le_rfl⟩ hab
  rcases lt_trichotomy x y with h | h | h
  · exact (ne_of_lt (inc hx h rx) same).elim
  · exact h
  · exact (ne_of_lt (inc hy h ry) same.symm).elim

/-- On the incoming branch the oscillator point, raw impact and corrected
    radial height determine the stress amplitude and both frame coordinates. -/
theorem recover_frame {U w R R' a a' b b' : ℝ} (hU : |U| ≤ 2) (hw : |w| ≤ 1)
    (r1 : 4 ≤ R) (r2 : 4 ≤ R') (a1 : 0 ≤ a) (a2 : 0 ≤ a')
    (u1 : a^2+b^2=1) (u2 : a'^2+b'^2=1) (i : R*b=R'*b')
    (e : R^2*a+chi U w a b/R=R'^2*a'+chi U w a' b'/R') :
    R=R' ∧ a=a' ∧ b=b' := by
  have p : 0 < R := by linarith
  have p' : 0 < R' := by linarith
  have roots {l x y : ℝ} (hl : 0 ≤ l) (hu : x^2+y^2=1) :
      r (l*y) (l*x)=l := by
    unfold r
    rw [show (l*x)^2+(l*y)^2 = l^2 by linear_combination l^2*hu,Real.sqrt_sq hl]
  have hr := roots p.le u1
  have hr' := roots p'.le u2
  have eq : height U w (R*b) (R*a) = height U w (R*b) (R'*a') := by
    calc
      _ = _ := height_eq U w R a b p u1
      _ = _ := e
      _ = height U w (R'*b') (R'*a') := (height_eq U w R' a' b' p' u2).symm
      _ = _ := by rw [i]
  have m := height_injective hU hw (mul_nonneg p.le a1) (mul_nonneg p'.le a2)
    (hr.symm ▸ r1) (show 4 ≤ r (R*b) (R'*a') by rw [i,hr']; exact r2) eq
  have same : R = R' := by calc
    _ = r (R*b) (R*a) := hr.symm
    _ = r (R'*b') (R'*a') := by rw [i,m]
    _ = _ := hr'
  subst R'
  exact ⟨rfl,mul_left_cancel₀ p.ne' m,mul_left_cancel₀ p.ne' i⟩

end ClosedSimilarity.FrozenStress.Incoming
#print axioms ClosedSimilarity.FrozenStress.Incoming.height_injective
#print axioms ClosedSimilarity.FrozenStress.Incoming.recover_frame
