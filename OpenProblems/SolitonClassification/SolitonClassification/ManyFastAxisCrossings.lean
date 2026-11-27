import SolitonClassification.FastAxisSeparation
import SolitonClassification.OscillatorCrossingWindows
import SolitonClassification.BoundedCrossingPreimages
import SolitonClassification.MovingCrossingRoots

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.CrossingResponse

private def windowNumber {n : ℕ} (key : Fin n × Bool) : ℕ :=
  2*key.1.val + if key.2 then 2 else 1

private theorem windowNumber_inj (n : ℕ) : Function.Injective (@windowNumber n) := by
  rintro ⟨i,b⟩ ⟨k,c⟩ eq
  cases b <;> cases c <;> simp [windowNumber] at eq ⊢ <;> first
  | apply Fin.ext; omega
  | omega

private theorem windowNumber_pos {n : ℕ} (key : Fin n × Bool) : 0 < windowNumber key := by
  rcases key with ⟨i,b⟩
  cases b <;> simp [windowNumber]

private theorem windowNumber_le {n : ℕ} (key : Fin n × Bool) : windowNumber key ≤ 2*n := by
  rcases key with ⟨i,b⟩
  have h := i.isLt
  cases b <;> simp [windowNumber]
  omega

private theorem moving_coordinate (F : ℝ → ℝ → ℝ)
    (c : Continuous (fun z : ℝ × ℝ => F z.1 z.2)) {e r : ℕ → ℝ} {a : ℝ}
    (he : Tendsto e atTop (𝓝 0)) (hr : Tendsto r atTop (𝓝 a)) :
    Tendsto (fun j => F (e j) (r j)) atTop (𝓝 (F 0 a)) :=
  (c.tendsto (0,a)).comp (he.prodMk_nhds hr)

private theorem choose_crossings (n : ℕ) :
    ∃ B>0, ∀ (e β : ℕ → ℝ),
      Tendsto e atTop (𝓝 0) → Tendsto β atTop (𝓝 0) → (∀ᶠ j in atTop, 0<e j) →
      ∀ Q : ℕ → ℝ → Prop, (∀ a, 0<a → V 0 a≠0 → ∀ r : ℕ → ℝ, Tendsto r atTop (𝓝 a) →
        ∀ᶠ j in atTop, Q j (r j)) →
      ∀ᶠ j in atTop, ∃ r : Fin n → ℝ, Function.Injective (fun i => Y (e j) (r i)) ∧
        ∀ i, r i ∈ Ioo 0 B ∧ 0<Y (e j) (r i) ∧ X (e j) (r i)=β j * Y (e j) (r i) ∧
          tx (e j) (r i)-β j*ty (e j) (r i)≠0 ∧ β j*tx (e j) (r i)+ty (e j) (r i)≠0 ∧ Q j (r i) := by
  classical
  obtain ⟨H,hH,d,hd,C,hC,data⟩ := oscillator_window_data
  let B := (2*(n:ℝ)+1)*H
  have hB : 0<B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro e β he hb ep Q extra
  let a (k : Fin n × Bool) := (windowNumber k:ℝ)*H
  let height (k : Fin n × Bool) := (windowNumber k:ℝ)*d
  have pos (k : Fin n × Bool) : (0:ℝ)<windowNumber k := by exact_mod_cast windowNumber_pos k
  have ap (k) : 0<a k := mul_pos (pos k) hH
  have ab (k) : a k<B := by
    have h : (windowNumber k:ℝ) ≤ 2*(n:ℝ) := by exact_mod_cast windowNumber_le k
    exact mul_lt_mul_of_pos_right (h.trans_lt (lt_add_one _)) hH
  have cp (k) : 0<height k := mul_pos (pos k) hd
  have dt (k : Fin n × Bool) := (data (windowNumber k)).1
  choose r rl axis using fun k => exists_axis_roots (a := a k) (dt k).1 (dt k).2.1 e β he hb
  let y j k := Y (e j) (r k j)
  have yc (k) : Tendsto (fun j => y j k) atTop (𝓝 (height k)) := by
    simpa only [y,height,a,(dt k).2.2] using moving_coordinate Y Y_cont he (rl k)
  have yi : Function.Injective height := by
    intro k m eq
    have h : (windowNumber k:ℝ)=(windowNumber m:ℝ) := mul_right_cancel₀ hd.ne' eq
    exact windowNumber_inj n (by exact_mod_cast h)
  have allHeights := eventually_injective_heights height y yc yi
  have good (k : Fin n × Bool) : ∀ᶠ j in atTop,
      r k j∈Ioo 0 B ∧ 0<y j k ∧ X (e j) (r k j)=β j*y j k ∧
      tx (e j) (r k j)-β j*ty (e j) (r k j)≠0 := by
    have ux := moving_coordinate tx tx_cont he (rl k)
    have vy := moving_coordinate ty ty_cont he (rl k)
    have off := ux.sub (hb.mul vy)
    simp only [zero_mul,sub_zero,(frozen_tangent _).1] at off
    filter_upwards [(rl k).eventually_const_lt (ap k), (rl k).eventually_lt_const (ab k),
      (yc k).eventually_const_lt (cp k), axis k, off.eventually_ne (dt k).2.1] with j lo hi yp hit v
    exact ⟨⟨lo,hi⟩,yp,hit,v⟩
  have odd (i : Fin n) : responseValue (a (i,false))=C := by
    have eqa : a (i,false)=(i.val:ℝ)*(2*H)+H := by simp [a,windowNumber]; ring
    exact eqa ▸ (data i.val).2.2
  have even (i : Fin n) : responseValue (a (i,true))=0 := by
    have eqa : a (i,true)=((i.val+1:ℕ):ℝ)*(2*H) := by simp [a,windowNumber]; ring
    exact eqa ▸ (data (i.val+1)).2.1
  let axial (k : Fin n × Bool) (j : ℕ) := β j*tx (e j) (r k j)+ty (e j) (r k j)
  have pair (i : Fin n) : ∀ᶠ j in atTop, axial (i,false) j ≠ 0 ∨ axial (i,true) j ≠ 0 :=
    eventually_one_transverse (ap _) (ap _) (dt _).1 (dt _).1 (dt _).2.1 (dt _).2.1
      (show responseValue (a (i,false)) ≠ responseValue (a (i,true)) by rw [odd,even]; exact hC.ne)
      he hb (rl _) (rl _) ep (axis _) (axis _)
  have qOK (k : Fin n × Bool) := extra (a k) (ap k) (dt k).2.1 (r k) (rl k)
  filter_upwards [allHeights,eventually_all.mpr good,eventually_all.mpr pair,eventually_all.mpr qOK]
    with j inj ok pairs q
  have choice (i : Fin n) : ∃ b : Bool, axial (i,b) j ≠ 0 := by
    obtain o | t := pairs i
    · exact ⟨false,o⟩
    · exact ⟨true,t⟩
  choose pick hp using choice
  refine ⟨fun i => r (i,pick i) j, fun {i k} eq => congrArg Prod.fst (inj eq),?_⟩
  intro i
  obtain ⟨t,h,ax,v⟩ := ok (i,pick i)
  exact ⟨t,h,ax,v,hp i,q (i,pick i)⟩

/-- Uniformly in every vanishing seam slope and every positive fast parameter
    tending to zero, the actual fast trajectory meets the positive seam in
    arbitrarily many distinct points in a prescribed finite time window.
    Each selected tangent has both components relative to the seam nonzero. -/
theorem many_actual_axis_crossings (n : ℕ) :
    ∃ B>0, ∀ (e β : ℕ → ℝ),
      Tendsto e atTop (𝓝 0) → Tendsto β atTop (𝓝 0) → (∀ᶠ j in atTop, 0<e j) →
      ∀ᶠ j in atTop, ∃ r : Fin n → ℝ, Function.Injective (fun i => Y (e j) (r i)) ∧
        ∀ i, r i ∈ Ioo 0 B ∧ 0<Y (e j) (r i) ∧ X (e j) (r i)=β j * Y (e j) (r i) ∧
          tx (e j) (r i)-β j*ty (e j) (r i)≠0 ∧ β j*tx (e j) (r i)+ty (e j) (r i)≠0 := by
  obtain ⟨B,hB,all⟩ := choose_crossings n
  refine ⟨B,hB,?_⟩
  intro e β he hb ep
  simpa only [and_true] using all e β he hb ep (fun _ _ => True)
    (fun _ _ _ _ _ => Eventually.of_forall fun _ => trivial)

/-- In a growing first quarter, suppose visits to each fixed disk occur
    within uniformly bounded fast time. Every selected positive seam point
    then has exactly one preimage in the quarter, and its opposite has none. -/
theorem many_unique_quarter_crossings (n : ℕ) :
    ∃ B>0, ∀ (e β T : ℕ → ℝ),
      Tendsto e atTop (𝓝 0) → Tendsto β atTop (𝓝 0) → (∀ᶠ j in atTop, 0<e j) →
      (∀ᶠ j in atTop, B≤T j) →
      (∀ R : ℝ, 0≤R → ∃ M : ℝ, ∀ᶠ j in atTop, ∀ t∈Icc (0:ℝ) (T j),
        X (e j) t^2+Y (e j) t^2 ≤ R^2 → t≤M) →
      ∀ᶠ j in atTop, ∃ r : Fin n → ℝ, Function.Injective (fun i => Y (e j) (r i)) ∧
        ∀ i, r i ∈ Ioo 0 B ∧ r i ∈ Ioo 0 (T j) ∧ 0<Y (e j) (r i) ∧
          X (e j) (r i)=β j*Y (e j) (r i) ∧ tx (e j) (r i)-β j*ty (e j) (r i)≠0 ∧
          β j*tx (e j) (r i)+ty (e j) (r i)≠0 ∧ ∀ t∈Icc (0:ℝ) (T j),
            (X (e j) t=X (e j) (r i) → Y (e j) t=Y (e j) (r i) → t=r i) ∧
            ¬ (X (e j) t= -X (e j) (r i) ∧ Y (e j) t= -Y (e j) (r i)) := by
  obtain ⟨B,hB,all⟩ := choose_crossings n
  refine ⟨B,hB,?_⟩
  intro e β T he hb ep long capture
  let Q (j : ℕ) (r : ℝ) := ∀ t∈Icc (0:ℝ) (T j),
    (X (e j) t=X (e j) r → Y (e j) t=Y (e j) r → t=r) ∧
      ¬ (X (e j) t= -X (e j) r ∧ Y (e j) t= -Y (e j) r)
  have sel := all e β he hb ep Q (fun _ ap v r hr =>
    eventually_unique_quarter_preimage ap v e r T he hr capture)
  filter_upwards [sel,long] with j result bt
  obtain ⟨r,inj,ok⟩ := result
  refine ⟨r,inj,?_⟩
  intro i
  obtain ⟨t,height,ax,normal,along,unique⟩ := ok i
  exact ⟨t,⟨t.1,t.2.trans_le bt⟩,height,ax,normal,along,unique⟩

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.many_actual_axis_crossings
#print axioms ClosedSimilarity.CrossingResponse.many_unique_quarter_crossings
