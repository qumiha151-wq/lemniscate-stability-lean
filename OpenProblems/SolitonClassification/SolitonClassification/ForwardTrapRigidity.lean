import SolitonClassification.ForwardConeEscape
import SolitonClassification.TwelveLocalCycleTests

noncomputable section
namespace ClosedSimilarity.RotatingBifurcation.Cone
open Set Filter Topology

/-- Any compact forward-trapping set in the local spectral chart contains
    a fixed point of the very same pitch. No recurrence assumption on the
    given positive semiorbit is required. -/
theorem local_compact_trap_has_fixed_point
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (A : (Section × ℝ) →L[ℝ] Section) (strict : HasStrictFDerivAt F A base)
    (a u : ℝ) (ha : |a|<1) (hu : 1< |u|)
    (axes : ∀ v : Section, A (v,0) 0=a*v 0 ∧ A (v,0) 1=v 1 ∧ A (v,0) 2=u*v 2) :
    ∃ W ∈ 𝓝 base, ∀ K ⊆ W, IsCompact K → ContinuousOn F K →
      ∀ (ω : ℝ) (x : ℕ → Section), (∀ n, (x n,ω)∈K) → (∀ n, F (x n,ω)=x (n+1)) →
      ∃ y : Section, (y,ω)∈K ∧ F (y,ω)=y := by
  let e := min ((1-|a|)/4) ((|u|-1)/4)
  have ep : 0<e := lt_min (by linarith) (by linarith)
  have s : |a|+2*e<1 := by linarith [show e≤(1-|a|)/4 from min_le_left ..]
  have un : 1+2*e< |u| := by linarith [show e≤(|u|-1)/4 from min_le_right ..]
  let good := {p : (Section×ℝ)×(Section×ℝ) | ‖F p.1-F p.2-A (p.1-p.2)‖≤e*‖p.1-p.2‖}
  have h : good ∈ (𝓝 base) ×ˢ (𝓝 base) := by rw [←nhds_prod_eq]; exact strict.isLittleO.def ep
  obtain ⟨V,hV,Z,hZ,sub⟩ := Filter.mem_prod_iff.mp h
  refine ⟨V∩Z,inter_mem hV hZ,?_⟩
  intro K inW compact cont ω x contained orbit
  let S : Set (Section×ℝ) := K∩{p | p.2=ω}
  have sc : IsCompact S := compact.inter_right (isClosed_eq continuous_snd continuous_const)
  have here (n : ℕ) : (x n,ω)∈S := ⟨contained n,rfl⟩
  obtain ⟨B,_,largest⟩ := sc.exists_isMaxOn (show S.Nonempty from ⟨_,here 0⟩)
    (continuous_fst.norm.continuousOn)
  have cb (n : ℕ) : ‖x n‖≤‖B.1‖ := largest (here n)
  let v := fun n => x (n+1)-x n
  have estimate (n : ℕ) : ‖v (n+1)-A (v n,0)‖≤e*‖v n‖ := by
    have val := sub (show ((x (n+1),ω),(x n,ω))∈V×ˢZ from
      ⟨(inW (contained _)).1,(inW (contained n)).2⟩)
    have diff : (x (n+1),ω)-(x n,ω)=(v n,0) := Prod.ext rfl (sub_self _)
    change ‖F (x (n+1),ω)-F (x n,ω)-A ((x (n+1),ω)-(x n,ω))‖≤e*‖(x (n+1),ω)-(x n,ω)‖ at val
    simpa only [diff,orbit,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)] using val
  have tiny := bounded_orbits_have_small_steps x ‖B.1‖ cb a u e ep.le s un (by
    intro w n
    have each (j : Fin 3) := (norm_le_pi_norm (v (n+1)-A (v n,0)) j).trans (estimate n)
    have parts := axes (v n)
    refine ⟨?_,?_,?_⟩
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.1] using each 0
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.1] using each 1
    · simpa only [Pi.sub_apply,Real.norm_eq_abs,parts.2.2] using each 2)
  have cost : ContinuousOn (fun y : Section×ℝ => ‖F y-y.1‖) S :=
    ((cont.mono fun _ h => h.1).sub continuous_fst.continuousOn).norm
  obtain ⟨y,hy,minimal⟩ := sc.exists_isMinOn (show S.Nonempty from ⟨_,here 0⟩) cost
  have z : ‖F y-y.1‖=0 := by
    by_contra nz
    obtain ⟨n,small⟩ := tiny _ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm nz))
    have min : ‖F y-y.1‖≤‖F (x n,ω)-x n‖ := minimal (here n)
    rw [orbit] at min
    exact small.not_ge min
  obtain ⟨y,p⟩ := y
  obtain ⟨hK,same⟩ := hy
  change p=ω at same
  subst p
  exact ⟨y,hK,sub_eq_zero.mp (norm_eq_zero.mp z)⟩

/-- Under the twelve-box spectral identifications and fixed-point pitch
    rigidity, no compact subset of a sufficiently small section chart can
    contain a positive semiorbit of nonzero pitch. -/
theorem twelve_box_forward_escape (i : Fin 12) (inputs : QuarterBounds.Input → ℝ)
    (box : ∀ j, (QuarterBounds.enclosure i j).Contains (inputs j))
    (F : Section × ℝ → Section) (base : Section × ℝ)
    (A : (Section × ℝ) →L[ℝ] Section) (strict : HasStrictFDerivAt F A base)
    (a u : ℝ) (order : a≤u) (prod : a*u=1)
    (sum : a+u=(QuarterBounds.halfTrace.real inputs)^2-2)
    (axes : ∀ v : Section, A (v,0) 0=a*v 0 ∧ A (v,0) 1=v 1 ∧ A (v,0) 2=u*v 2)
    (fixed : ∀ᶠ y in 𝓝 base, F y=y.1 → y.2=0) :
    ∃ W ∈ 𝓝 base, ∀ K ⊆ W, IsCompact K → ContinuousOn F K →
      ∀ (ω : ℝ) (x : ℕ → Section), (∀ n, (x n,ω)∈K) → (∀ n, F (x n,ω)=x (n+1)) → ω=0 := by
  obtain ⟨_,_,trace⟩ := QuarterBounds.twelve_quarter_boxes i box
  have sq := pow_lt_pow_left₀ trace (by norm_num : (0:ℝ)≤2) (by decide : (2:ℕ)≠0)
  rw [sq_abs] at sq
  have up : 1<u := by linarith
  have ap : 0<a := by
    by_contra! neg
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg neg (zero_le_one.trans up.le),prod]
  have s : |a|<1 := by rw [abs_of_pos ap]; nlinarith only [mul_lt_mul_of_pos_left up ap,prod]
  have un : 1< |u| := by rwa [abs_of_pos (zero_lt_one.trans up)]
  obtain ⟨V,hV,trap⟩ := local_compact_trap_has_fixed_point F base A strict a u s un axes
  refine ⟨V∩{y | F y=y.1 → y.2=0},inter_mem hV fixed,?_⟩
  intro K inside hK ct ω x kept iter
  obtain ⟨y,mem,stop⟩ := trap K (fun _ h => (inside h).1) hK ct ω x kept iter
  exact (inside mem).2 stop

end ClosedSimilarity.RotatingBifurcation.Cone
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.local_compact_trap_has_fixed_point
#print axioms ClosedSimilarity.RotatingBifurcation.Cone.twelve_box_forward_escape
