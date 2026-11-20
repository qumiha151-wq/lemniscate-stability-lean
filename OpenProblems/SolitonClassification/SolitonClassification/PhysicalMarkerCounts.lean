import SolitonClassification.UnboundedClosedExpanders
import SolitonClassification.MarkerCount

noncomputable section
open Set
open SolitonClassification.Reflected.Rectangle
namespace ClosedSimilarity.GlobalSupport.MovingSeam

/-- A linear lower bound on the centre phase and a bounded seam phase force
    arbitrarily many different shooting markers in intervals of linear length. -/
theorem CentreChart.linearly_many_matches {H E B : ℝ} (b32 : 32≤B)
    (w : WindingChart H E) (c : CentreChart H E B)
    (lower : ∀ b : Ici B, (b:ℝ)/8 ≤ c.angle b) :
    ∃ C>0, ∀ N : ℕ, ∃ (β : Fin N→Ici B) (z : Fin N→ChartDomain E) (n : Fin N→ℕ),
      Function.Injective β ∧ ∀ i, (β i:ℝ) ≤ B+C*((N:ℝ)+1) ∧
      (z i).2=c.eps (β i) ∧ c.angle (β i)=w.angle (z i)+(n i:ℝ)*(2*Real.pi) ∧
      c.transverse (β i)=w.transverse (z i) := by
  let incl (x : ℝ) : Ici B := ⟨max B x,show B≤max B x from le_max_left B x⟩
  have ci : Continuous incl := (continuous_const.max continuous_id).subtype_mk _
  let clip := projIcc (-1/4:ℝ) 1 (by norm_num)
  let chart (p : ℝ×ℝ) : ChartDomain E := (clip p.2,c.eps (incl p.1))
  have cj : Continuous chart := (continuous_projIcc.comp continuous_snd).prodMk
    (c.contEps.comp (ci.comp continuous_fst))
  obtain ⟨M,cap⟩ := w.bounded
  let P := 2*Real.pi
  have pos : 0<P := by dsimp [P]; positivity
  obtain ⟨a,ha⟩ := exists_nat_gt ((c.angle (incl B)+M)/P)
  obtain ⟨d,hd⟩ := exists_nat_gt (2*M/P)
  have left : c.angle (incl B)+M < (a:ℝ)*P := (div_lt_iff₀ pos).mp ha
  have space : 2*M < (d:ℝ)*P := (div_lt_iff₀ pos).mp hd
  let L := (a:ℝ)*P+(d:ℝ)*P+|M|+1
  have a0 : 0≤(a:ℝ)*P := mul_nonneg (Nat.cast_nonneg _) pos.le
  have d0 : 0≤(d:ℝ)*P := mul_nonneg (Nat.cast_nonneg _) pos.le
  have LP : 0<L := by dsimp [L]; linarith [abs_nonneg M]
  have dL : (d:ℝ)*P≤L := by dsimp [L]; linarith [abs_nonneg M]
  let C := 8*L
  have cp : 0<C := by dsimp [C]; positivity
  refine ⟨C,cp,?_⟩
  intro N
  let top := B+C*((N:ℝ)+1)
  have endp : B≤top := by dsimp [top]; linarith [mul_nonneg cp.le (by positivity : 0≤(N:ℝ)+1)]
  let n (i : Fin N) : ℕ := a+d*i.val
  let level (i : Fin N) := (n i:ℝ)*P
  have lvl (i : Fin N) : level i = (a:ℝ)*P + ((d:ℝ)*P)*(i.val:ℝ) := by
    dsimp [level,n]
    push_cast
    ring
  have lhit (i : Fin N) : c.angle (incl B)+M < level i := by
    rw [lvl]; linarith [mul_nonneg d0 (Nat.cast_nonneg i.val)]
  have rhit (i : Fin N) : level i+M < c.angle (incl top) := by
    have iN : (i.val:ℝ)≤(N:ℝ) := by exact_mod_cast i.isLt.le
    have btop : (incl top:ℝ)=top := max_eq_right endp
    have loc := lower (incl top)
    rw [btop] at loc
    have step := (mul_le_mul_of_nonneg_left iN d0).trans
      (mul_le_mul_of_nonneg_right dL (Nat.cast_nonneg N))
    have head : (a:ℝ)*P+M < L := by dsimp [L]; linarith [le_abs_self M]
    rw [lvl]
    dsimp [top,C] at loc
    linarith
  have gap (i j : Fin N) (order : i<j) : 2*M < level j-level i := by
    have step : (i.val:ℝ)+1≤(j.val:ℝ) := by exact_mod_cast (show i.val+1≤j.val from order)
    rw [lvl,lvl]
    linarith [mul_le_mul_of_nonneg_left step d0]
  obtain ⟨xs,ys,inj,roots⟩ := separated_matching_markers B top (-1/4) 1 M endp (by norm_num)
    (fun b => c.angle (incl b)) (fun b => c.transverse (incl b)) (w.angle ∘ chart)
    (w.transverse ∘ chart)
    (((c.contAngle.comp (ci.comp continuous_fst)).sub (w.continuous_angle.comp cj)).prodMk
      ((w.continuous_transverse.comp cj).sub (c.contImpact.comp (ci.comp continuous_fst)))).continuousOn
    (fun b _ y _ => cap (chart (b,y)))
    (fun b _ => by
      have lo := w.left (c.eps (incl b))
      have s := (abs_le.mp (c.small (incl b))).1
      have lim : clip (-1/4)=leftCurvature := Subtype.ext (by simp [clip,leftCurvature])
      change w.transverse (clip (-1/4),_) < _
      rw [lim]; linarith)
    (fun b _ => by
      have hi := w.right (c.eps (incl b))
      have s := (abs_le.mp (c.small (incl b))).2
      have lim : clip 1=rightCurvature := Subtype.ext (by simp [clip,rightCurvature])
      change _ < w.transverse (clip 1,_)
      rw [lim]; linarith)
    N level lhit rhit gap
  have orig (i : Fin N) : (incl (xs i):ℝ)=xs i := max_eq_right (roots i).1.1
  refine ⟨fun i => incl (xs i),fun i => chart (xs i,ys i),n,?_,?_⟩
  · intro i j eq
    exact inj (((orig i).symm.trans (congrArg Subtype.val eq)).trans (orig j))
  · intro i
    exact ⟨(orig i).le.trans (roots i).1.2,rfl,(roots i).2.2.1,(roots i).2.2.2⟩

/-- A single common physical section realizes N distinct winding matches before
    marker B+C(N+1), uniformly for every natural number N. -/
theorem exists_linearly_many_physical_matches :
    ∃ H E B C : ℝ, 0<C ∧ 32≤B ∧ ∃ (w : WindingChart H E) (c : CentreChart H E B),
      ∀ N : ℕ, ∃ (β : Fin N→Ici B) (z : Fin N→ChartDomain E) (n : Fin N→ℕ),
        Function.Injective β ∧ ∀ i, (β i:ℝ) ≤ B+C*((N:ℝ)+1) ∧
        (z i).2=c.eps (β i) ∧ c.angle (β i)=w.angle (z i)+(n i:ℝ)*(2*Real.pi) ∧
        c.transverse (β i)=w.transverse (z i) := by
  obtain ⟨H,E,B,b32,w,c,lower⟩ := exists_physical_shooting_charts
  obtain ⟨C,cp,count⟩ := c.linearly_many_matches b32 w lower
  exact ⟨H,E,B,C,cp,b32,w,c,count⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.CentreChart.linearly_many_matches

#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.exists_linearly_many_physical_matches
