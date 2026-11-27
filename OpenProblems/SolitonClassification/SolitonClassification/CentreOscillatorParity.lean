import SolitonClassification.CrossingParity
import SolitonClassification.SupportFlowContinuity

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace ClosedSimilarity.CentreOscillator
open GlobalSupport

/-- The actual zero-driving global centre solution, in fast-scale coordinates. -/
def state : ℝ → Phase := solution 0 ![0,1,0,0]
def U (s : ℝ) := state s 0
def w (s : ℝ) := state s 1
def G (s : ℝ) := ∫ x in (0:ℝ)..s, U x ^ 2 / 2

private theorem start : state 0 = ![0,1,0,0] := solution_zero .. 
private theorem ode (s : ℝ) : HasDerivAt state (rhs 0 (state s)) s := solution_derivative ..

theorem support_zero (s : ℝ) : state s 2 = 0 ∧ state s 3 = 0 := by
  let P := fun x => state x 2
  let Q := fun x => state x 3
  have d (x) : HasDerivAt (fun u => P u ^ 2 + Q u ^ 2) 0 x := by
    have p : HasDerivAt P (-U x * Q x) x := hasDerivAt_pi.mp (ode x) 2
    have q : HasDerivAt Q (U x * P x) x := by
      simpa [rhs, U, P] using hasDerivAt_pi.mp (ode x) 3
    convert! (p.pow 2).add (q.pow 2) using 1
    ring
  have h := is_const_of_deriv_eq_zero (fun x => (d x).differentiableAt)
    (fun x => (d x).deriv) s 0
  have eq : (state s 2)^2 + (state s 3)^2 = 0 := by simpa [P,Q,start] using h
  exact ⟨by nlinarith [sq_nonneg (state s 3)], by nlinarith [sq_nonneg (state s 2)]⟩

theorem dU (s : ℝ) : HasDerivAt U (w s) s := hasDerivAt_pi.mp (ode s) 0
theorem dw (s : ℝ) : HasDerivAt w (-(U s)^3/2) s := by
  have h : HasDerivAt w (-(U s)^3/2 - state s 2) s := hasDerivAt_pi.mp (ode s) 1
  rwa [(support_zero s).1, sub_zero] at h

private theorem cU : Continuous U := continuous_iff_continuousAt.mpr fun s => (dU s).continuousAt
private theorem cw : Continuous w := continuous_iff_continuousAt.mpr fun s => (dw s).continuousAt
private theorem U0 : U 0 = 0 := by simp [U,start]
private theorem w0 : w 0 = 1 := by simp [w,start]

theorem dG (s : ℝ) : HasDerivAt G (U s ^ 2 / 2) s := by
  have c : Continuous (fun x => U x ^ 2 / 2) := (cU.pow 2).div_const 2
  exact intervalIntegral.integral_hasDerivAt_right (c.intervalIntegrable ..)
    c.stronglyMeasurable.stronglyMeasurableAtFilter c.continuousAt

private theorem first_turn : ∃ T > 0, w T = 0 ∧ ∀ t ∈ Ioc 0 T, 0 < U t := by
  have eventualTurn : ∃ t ≥ 0, w t ≤ 0 := by
    by_contra! pos
    have inc : StrictMonoOn U (Ici 0) := by
      apply strictMonoOn_of_deriv_pos (convex_Ici _) cU.continuousOn
      intro t ht
      rw [(dU t).deriv]
      exact pos t (interior_subset ht)
    have up : 0 < U 1 := by
      have h := inc (show (0:ℝ) ∈ Ici 0 by simp) (show (1:ℝ) ∈ Ici 0 by norm_num) zero_lt_one
      simpa only [U0] using h
    let c := U 1 ^ 3 / 2
    have cp : 0 < c := by dsimp [c]; positivity
    let f := fun s => w s + c*s
    have df (s) : HasDerivAt f (-U s ^ 3 / 2+c) s := by
      convert! (dw s).add ((hasDerivAt_id s).const_mul c) using 1
      ring
    have dec : AntitoneOn f (Ici 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici _)
        (fun s _ => (df s).continuousAt.continuousWithinAt)
        (fun s _ => (df s).differentiableAt.differentiableWithinAt)
      intro s hs
      have L : 1 ≤ s := interior_subset hs
      have order := inc.monotoneOn (show (1:ℝ)∈ Ici 0 by norm_num)
        (show s∈Ici 0 from zero_le_one.trans L) L
      rw [(df s).deriv]
      dsimp [c]
      linarith [pow_le_pow_left₀ up.le order 3]
    let x := 1+(w 1+1)/c
    have w1 := pos 1 zero_le_one
    have xlo : 1 ≤ x := by dsimp [x]; linarith [div_pos (show 0 < w 1+1 by linarith) cp]
    have neg := dec (show (1:ℝ) ∈ Ici 1 by simp) (show x ∈ Ici 1 from xlo) xlo
    have eq : c*x = c + (w 1+1) := by dsimp [x]; field_simp
    dsimp only [f] at neg
    linarith [pos x (zero_le_one.trans xlo)]
  obtain ⟨b, hb, hit⟩ := eventualTurn
  have ne : ∃ t ∈ Icc 0 b, w t = 0 := intermediate_value_Icc' hb cw.continuousOn
    (show (0:ℝ) ∈ Icc (w b) (w 0) from ⟨hit, by rw [w0]; norm_num⟩)
  let zeros := {x ∈ Icc 0 b | w x = 0}
  have compact : IsCompact zeros := isCompact_Icc.inter_right (isClosed_eq cw continuous_const)
  obtain ⟨T,ht,first⟩ := compact.exists_isMinOn (show zeros.Nonempty from ne) continuous_id.continuousOn
  have tpos : 0 < T := lt_of_le_of_ne ht.1.1 (by intro e; have := e ▸ w0; linarith [ht.2])
  have before (s) (hs : s ∈ Ioo 0 T) : 0 < w s := by
    by_contra! neg
    obtain ⟨x,hx,eq⟩ := intermediate_value_Icc' hs.1.le cw.continuousOn
      (show (0:ℝ)∈ Icc (w s) (w 0) from ⟨neg,by rw [w0]; norm_num⟩)
    have early : T ≤ x := first (show x ∈ zeros from ⟨⟨hx.1, hx.2.trans (hs.2.le.trans ht.1.2)⟩,eq⟩)
    linarith [hs.2,hx.2]
  have inc : StrictMonoOn U (Icc 0 T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) cU.continuousOn
    rw [interior_Icc]
    intro t ht
    rw [(dU t).deriv]
    exact before t ht
  refine ⟨T,tpos,ht.2,fun t h => ?_⟩
  simpa only [U0] using inc (left_mem_Icc.mpr tpos.le) ⟨h.1.le,h.2⟩ h.1

private theorem equal_motion {f g F V : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (g s) s) (hg : ∀ s, HasDerivAt g (-(f s)^3/2) s)
    (hF : ∀ s, HasDerivAt F (V s) s) (hV : ∀ s, HasDerivAt V (-(F s)^3/2) s)
    (at0 : f 0 = F 0) (vel0 : g 0 = V 0) : ∀ t, f t = F t ∧ g t = V t := by
  let pack := fun (a v : ℝ → ℝ) t => (![a t, v t, 0, 0] : Phase)
  have packed (a v : ℝ → ℝ) (da : ∀ s, HasDerivAt a (v s) s)
      (dv : ∀ s, HasDerivAt v (-(a s)^3/2) s) (s) :
      HasDerivAt (pack a v) (rhs 0 (pack a v s)) s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [pack,rhs] using da s
    · simpa [pack,rhs] using dv s
    · simpa [pack,rhs] using hasDerivAt_const s (0:ℝ)
    · simpa [pack,rhs] using hasDerivAt_const s (0:ℝ)
  have uniq := exists_unique_solution 0 (pack F V 0)
  have eq := uniq.unique (y₁ := pack f g) (y₂ := pack F V)
    ⟨by simp [pack,at0,vel0], packed f g hf hg⟩ ⟨rfl,packed F V hF hV⟩
  intro t
  exact ⟨congrFun (congrFun eq t) 0, congrFun (congrFun eq t) 1⟩

/-- The actual zero-drive centre orbit has positive curvature on a positive
    half-period, flips both oscillator coordinates on translation by it,
    and has slopes one and minus one at its endpoints. -/
theorem positive_half_period : ∃ H > 0, (∀ s ∈ Ioo 0 H, 0 < U s) ∧
    (∀ s, U (s+H) = -U s ∧ w (s+H) = -w s) ∧
    U 0 = 0 ∧ w 0 = 1 ∧ U H = 0 ∧ w H = -1 := by
  obtain ⟨T,hT,turn,pos⟩ := first_turn
  have shifted (a : ℝ) (s : ℝ) : HasDerivAt (fun x => U (a+x)) (w (a+s)) s := by
    simpa [Function.comp_def] using (dU (a+s)).comp s ((hasDerivAt_id s).const_add a)
  have shiftw (a : ℝ) (s : ℝ) : HasDerivAt (fun x => w (a+x)) (-(U (a+s))^3/2) s := by
    simpa [Function.comp_def] using (dw (a+s)).comp s ((hasDerivAt_id s).const_add a)
  have revU (s : ℝ) : HasDerivAt (fun x => U (T-x)) (-w (T-s)) s := by
    simpa [Function.comp_def] using (dU (T-s)).comp s ((hasDerivAt_id s).const_sub T)
  have revw (s : ℝ) : HasDerivAt (fun x => -w (T-x)) (-(U (T-s))^3/2) s := by
    convert! ((dw (T-s)).comp s ((hasDerivAt_id s).const_sub T)).neg using 1
    ring
  have reflect := equal_motion (shifted T) (shiftw T) revU revw (by simp) (by simp [turn])
  obtain ⟨uTw,wTw⟩ := reflect T
  rw [sub_self,U0] at uTw
  rw [sub_self,w0] at wTw
  have negw (s) : HasDerivAt (fun x => -w x) (-(-U s)^3/2) s := by
    convert! (dw s).neg using 1
    ring
  have anti := equal_motion (shifted (T+T)) (shiftw (T+T)) (fun s => (dU s).neg) negw
    (by simpa [U0] using uTw) (by simpa [w0] using wTw)
  refine ⟨T+T,by linarith, ?_,fun s => by simpa only [add_comm s (T+T), Pi.neg_apply] using anti s,
    U0,w0,uTw,wTw⟩
  intro s hs
  by_cases ls : s ≤ T
  · exact pos s ⟨hs.1,ls⟩
  · have h := (reflect (s-T)).1
    rw [show T+(s-T)=s by ring, show T-(s-T)=T+T-s by ring] at h
    rw [h]
    exact pos _ ⟨by linarith [hs.2],by linarith⟩

/-- The alternating horizontal variations hold for the actual centre
    orbit without any oscillator or sign hypotheses. -/
theorem true_horizontal_variations :
    ∃ H > 0, ∃ C < 0, ∀ n : ℕ,
      (∫ t in (0:ℝ)..(n:ℝ)*(2*H), CrossingParity.horizontalRate U w G t) = 0 ∧
      (∫ t in (0:ℝ)..((n:ℝ)*(2*H)+H), CrossingParity.horizontalRate U w G t) = C := by
  obtain ⟨H, hp, pos, anti, startU, _, _, _⟩ := positive_half_period
  obtain ⟨neg, all⟩ := CrossingParity.horizontalRate_parity U w G hp cw dU dG
    startU (fun s => (anti s).1) pos
  exact ⟨H, hp, _, neg, all⟩

end ClosedSimilarity.CentreOscillator
#print axioms ClosedSimilarity.CentreOscillator.support_zero
#print axioms ClosedSimilarity.CentreOscillator.positive_half_period
#print axioms ClosedSimilarity.CentreOscillator.true_horizontal_variations
