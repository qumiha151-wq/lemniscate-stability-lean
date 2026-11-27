import LengthGrowth.ActualFlow.InflectionEndpointMass
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Tactic.FunProp

noncomputable section
open Set Finset Filter Function
open scoped Topology
namespace LengthGrowth.ActualFlow.TurningEnvelope

abbrev Ends (n : ℕ) := (Fin n→ℝ) × (Fin n→ℝ)

def Ordered {n : ℕ} (P : ℝ) (e : Ends n) : Prop :=
  (∀ i, e.1 i≤e.2 i) ∧ (∀ i j, i<j → e.2 i≤e.1 j) ∧ (∀ i j, e.2 i≤e.1 j+P)

def gain {n : ℕ} (θ : ℝ→ℝ) (e : Ends n) : ℝ := ∑ i, (θ (e.2 i)-θ (e.1 i))

private theorem order_perturb {a b v w x : ℝ} (h : a≤b) (same : a=b → v=w) :
    ∀ᶠ y in 𝓝 x, a+(y-x)*v≤b+(y-x)*w := by
  rcases h.lt_or_eq with lt|eq
  · have cont : Continuous (fun y : ℝ => b+(y-x)*w-(a+(y-x)*v)) := by fun_prop
    have lim : Tendsto (fun y : ℝ => b+(y-x)*w-(a+(y-x)*v)) (𝓝 x) (𝓝 (b-a)) := by simpa using cont.tendsto x
    exact (lim.eventually (lt_mem_nhds (sub_pos.mpr lt))).mono fun y hy => (sub_pos.mp hy).le
  · filter_upwards with y
    rw [eq,same eq]

/-- Move every endpoint with a given circular label together.
    Matching velocities at each active ordering constraint make the
    perturbation admissible, even when an arc and a gap have zero length. -/
theorem variation_ordered {n : ℕ} {P x : ℝ} {e : Ends n} (he : Ordered P e)
    {v : ℝ→ℝ} (per : Periodic v P) :
    ∀ᶠ y in 𝓝 x, Ordered P
      (fun i => e.1 i+(y-x)*v (e.1 i),fun i => e.2 i+(y-x)*v (e.2 i)) := by
  have pair := eventually_all.mpr fun i => order_perturb (x:=x) (he.1 i) (congrArg v)
  have gap : ∀ᶠ y in 𝓝 x,∀i j, i<j → e.2 i+(y-x)*v (e.2 i)≤e.1 j+(y-x)*v (e.1 j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases h : i<j
    · exact (order_perturb (he.2.1 i j h) (congrArg v)).mono fun _ hx _ => hx
    · exact .of_forall fun _ bad => (h bad).elim
  have span : ∀ᶠ y in 𝓝 x,∀i j, e.2 i+(y-x)*v (e.2 i)≤(e.1 j+P)+(y-x)*v (e.1 j) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j =>
      order_perturb (he.2.2 i j) fun eq => (congrArg v eq).trans (per _)
  filter_upwards [pair,gap,span] with y hy hg hs
  exact ⟨hy,hg,fun i j => by linarith only [hs i j]⟩

/-- The time derivative of the total turn at an optimal cyclic endpoint
    array is bounded using only the angular velocities at its local extrema. -/
theorem maximizing_cyclic_rate {n : ℕ} {P : ℝ} (hp : 0<P) (e : Ends n) (he : Ordered P e)
    (θ V : ℝ→ℝ) (shift : ∀ h, Periodic (fun x => θ (x+h)-θ x) P) (vper : Periodic V P)
    {ref rate : ℝ} (pos : 0≤rate)
    (maxV : ∀ x, IsLocalMax θ x → V x≤ref+rate) (minV : ∀ x, IsLocalMin θ x → ref≤V x)
    (optimal : ∀ y : Ends n, Ordered P y → gain θ y≤gain θ e) :
    gain V e≤(n:ℝ)*rate := by
  classical
  let tag := toIcoMod hp 0
  have reduce (f : ℝ→ℝ) (pf : Periodic f P) (x : ℝ) : f (tag x)=f x := by
    unfold tag
    rw [←self_sub_toIcoDiv_zsmul hp 0 x]
    exact pf.sub_zsmul_eq _
  let l := tag ∘ e.1
  let r := tag ∘ e.2
  have opt (a : ℝ) : ∀ᶠ h in 𝓝 a,
      (multiplicity r a-multiplicity l a)*(θ h-θ a)≤0 := by
    let w := fun x => if tag x=a then (1:ℝ) else 0
    have pw : Periodic w P := fun x => by simp [w,tag,toIcoMod_add_right]
    filter_upwards [variation_ordered (x:=a) he pw] with y order
    have h := optimal _ order
    have inc (x : ℝ) : θ (x+(y-a)*w x)-θ x = (if tag x=a then 1 else 0)*(θ y-θ a) := by
      by_cases same : tag x=a
      · have d := reduce _ (shift (y-a)) x
        simpa [w,same,add_sub_cancel] using d.symm
      · simp [w,same]
    have calcChange (u : Fin n→ℝ) :
        (∑i, (θ (u i+(y-a)*w (u i))-θ (u i)))=multiplicity (tag ∘ u) a*(θ y-θ a) := by
      simp_rw [inc,multiplicity,sum_mul,comp_apply]
    have hr := calcChange e.2
    have hl := calcChange e.1
    simp only [sum_sub_distrib] at hr hl
    dsimp [gain] at h
    rw [sum_sub_distrib,sum_sub_distrib] at h
    dsimp only [r,l]
    rw [sub_mul]
    linarith
  have H := rate_of_variations l r θ V pos maxV minV opt
  simpa only [gain,r,l,comp_apply,reduce V vper] using H

end LengthGrowth.ActualFlow.TurningEnvelope
#print axioms LengthGrowth.ActualFlow.TurningEnvelope.maximizing_cyclic_rate
