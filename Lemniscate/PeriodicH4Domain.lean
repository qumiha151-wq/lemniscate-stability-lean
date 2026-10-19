import Lemniscate.PeriodicWeakOperatorEnergy

/-! The actual H4 domain as a complex subspace of periodic L2. Successive weak
derivatives are unique; selecting their witnesses therefore gives genuine linear
derivative maps, independent of any choice of representatives. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_weak_deriv_zero : HasWeakCircleDeriv T 0 0 := by
  intro φ φ₁ hφ
  simp

theorem circle_weak_deriv_add (f f₁ g g₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hg : HasWeakCircleDeriv T g g₁) :
    HasWeakCircleDeriv T (f+g) (f₁+g₁) := by
  intro φ φ₁ hφ
  simp only [inner_add_left, hf φ φ₁ hφ, hg φ φ₁ hφ]
  ring

theorem circle_weak_deriv_smul (c : ℂ) (f f₁ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) : HasWeakCircleDeriv T (c • f) (c • f₁) := by
  intro φ φ₁ hφ
  simp only [inner_smul_left, hf φ φ₁ hφ]
  ring

def circleH4Domain : Submodule ℂ (CircleL2 T) where
  carrier := {f | InCircleH4 T f}
  zero_mem' := ⟨0, 0, 0, 0, circle_weak_deriv_zero T, circle_weak_deriv_zero T,
    circle_weak_deriv_zero T, circle_weak_deriv_zero T⟩
  add_mem' := by
    intro f g hf hg
    rcases hf with ⟨f₁, f₂, f₃, f₄, hf, hf₁, hf₂, hf₃⟩
    rcases hg with ⟨g₁, g₂, g₃, g₄, hg, hg₁, hg₂, hg₃⟩
    exact ⟨f₁+g₁, f₂+g₂, f₃+g₃, f₄+g₄, circle_weak_deriv_add T _ _ _ _ hf hg,
      circle_weak_deriv_add T _ _ _ _ hf₁ hg₁, circle_weak_deriv_add T _ _ _ _ hf₂ hg₂,
      circle_weak_deriv_add T _ _ _ _ hf₃ hg₃⟩
  smul_mem' := by
    intro c f hf
    rcases hf with ⟨f₁, f₂, f₃, f₄, hf, hf₁, hf₂, hf₃⟩
    exact ⟨c • f₁, c • f₂, c • f₃, c • f₄, circle_weak_deriv_smul T c _ _ hf,
      circle_weak_deriv_smul T c _ _ hf₁, circle_weak_deriv_smul T c _ _ hf₂,
      circle_weak_deriv_smul T c _ _ hf₃⟩

structure CircleH4Jet (f : CircleL2 T) where
  first : CircleL2 T
  second : CircleL2 T
  third : CircleL2 T
  fourth : CircleL2 T
  hfirst : HasWeakCircleDeriv T f first
  hsecond : HasWeakCircleDeriv T first second
  hthird : HasWeakCircleDeriv T second third
  hfourth : HasWeakCircleDeriv T third fourth

theorem circle_h4_jet_unique (f : CircleL2 T) (u v : CircleH4Jet T f) : u = v := by
  have h₁ : u.first = v.first := weak_circle_deriv_unique T _ _ _ u.hfirst v.hfirst
  have h₂ : u.second = v.second := weak_circle_deriv_unique T _ _ _ u.hsecond
    (by simpa only [h₁] using v.hsecond)
  have h₃ : u.third = v.third := weak_circle_deriv_unique T _ _ _ u.hthird
    (by simpa only [h₂] using v.hthird)
  have h₄ : u.fourth = v.fourth := weak_circle_deriv_unique T _ _ _ u.hfourth
    (by simpa only [h₃] using v.hfourth)
  cases u
  cases v
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  rfl

noncomputable def circleH4Jet (f : circleH4Domain T) : CircleH4Jet T (f : CircleL2 T) := by
  have h : Nonempty (CircleH4Jet T (f : CircleL2 T)) := by
    rcases f.property with ⟨f₁, f₂, f₃, f₄, hf, hf₁, hf₂, hf₃⟩
    exact ⟨⟨f₁, f₂, f₃, f₄, hf, hf₁, hf₂, hf₃⟩⟩
  exact Classical.choice h

noncomputable def CircleH4Jet.add {f g : CircleL2 T} (u : CircleH4Jet T f) (v : CircleH4Jet T g) :
    CircleH4Jet T (f+g) :=
  ⟨u.first+v.first, u.second+v.second, u.third+v.third, u.fourth+v.fourth,
    circle_weak_deriv_add T _ _ _ _ u.hfirst v.hfirst,
    circle_weak_deriv_add T _ _ _ _ u.hsecond v.hsecond,
    circle_weak_deriv_add T _ _ _ _ u.hthird v.hthird,
    circle_weak_deriv_add T _ _ _ _ u.hfourth v.hfourth⟩

noncomputable def CircleH4Jet.smul (c : ℂ) {f : CircleL2 T} (u : CircleH4Jet T f) :
    CircleH4Jet T (c • f) :=
  ⟨c • u.first, c • u.second, c • u.third, c • u.fourth,
    circle_weak_deriv_smul T c _ _ u.hfirst, circle_weak_deriv_smul T c _ _ u.hsecond,
    circle_weak_deriv_smul T c _ _ u.hthird, circle_weak_deriv_smul T c _ _ u.hfourth⟩

theorem circle_h4_jet_add (f g : circleH4Domain T) :
    circleH4Jet T (f+g) = CircleH4Jet.add T (circleH4Jet T f) (circleH4Jet T g) :=
  circle_h4_jet_unique T _ _ _

theorem circle_h4_jet_smul (c : ℂ) (f : circleH4Domain T) :
    circleH4Jet T (c • f) = CircleH4Jet.smul T c (circleH4Jet T f) :=
  circle_h4_jet_unique T _ _ _

/-- Index 0, 1, 2, 3 denotes derivative order 1, 2, 3, 4. -/
noncomputable def circleH4Derivative (j : Fin 4) : circleH4Domain T →ₗ[ℂ] CircleL2 T where
  toFun f := ![(circleH4Jet T f).first, (circleH4Jet T f).second,
    (circleH4Jet T f).third, (circleH4Jet T f).fourth] j
  map_add' f g := by
    rw [circle_h4_jet_add]
    fin_cases j <;> rfl
  map_smul' c f := by
    rw [circle_h4_jet_smul]
    fin_cases j <;> rfl

theorem circle_h4_mem_h2 (f : circleH4Domain T) : InCircleH2 T (f : CircleL2 T) :=
  ⟨(circleH4Jet T f).first, (circleH4Jet T f).second,
    (circleH4Jet T f).hfirst, (circleH4Jet T f).hsecond⟩

end Lemniscate
