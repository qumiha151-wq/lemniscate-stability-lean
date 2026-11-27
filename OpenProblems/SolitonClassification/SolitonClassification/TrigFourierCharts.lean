import SolitonClassification.TrigRationalChart

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial Set Filter Complex
open scoped Polynomial BigOperators ComplexConjugate
namespace ClosedSimilarity.TrigCurvature

def Admits (u w : ℝ) (f : ℝ → ℝ) : Prop := ∃ n p,Represents u w f n p

private theorem admits_const (u w c : ℝ) : Admits u w (fun _ => c) :=
  ⟨0,C c,fun x => by simp⟩

private theorem admits_add {u w : ℝ} {f g : ℝ → ℝ} (hf : Admits u w f) (hg : Admits u w g) :
    Admits u w (fun s=>f s+g s) := by
  obtain ⟨m,p,hp⟩ := hf
  obtain ⟨n,q,hq⟩ := hg
  refine ⟨m+n,p*Q^n+q*Q^m,fun x => ?_⟩
  simp only [pow_add,eval_add,eval_mul,eval_pow,eval_Q,←hp x,←hq x]
  ring

private theorem admits_neg {u w : ℝ} {f : ℝ → ℝ} (hf : Admits u w f) :
    Admits u w (fun s=> -f s) := by
  obtain ⟨n,p,hp⟩ := hf
  exact ⟨n,-p,fun x => by simp only [eval_neg,←hp x,neg_mul]⟩

private theorem admits_sub {u w : ℝ} {f g : ℝ → ℝ} (hf : Admits u w f) (hg : Admits u w g) :
    Admits u w (fun s=>f s-g s) := by simpa only [sub_eq_add_neg] using admits_add hf (admits_neg hg)

private theorem admits_mul {u w : ℝ} {f g : ℝ → ℝ} (hf : Admits u w f) (hg : Admits u w g) :
    Admits u w (fun s=>f s*g s) := by
  obtain ⟨m,p,hp⟩ := hf
  obtain ⟨n,q,hq⟩ := hg
  exact ⟨m+n,p*q,fun x => by simp only [pow_add,eval_mul,←hp x,←hq x]; ring⟩

private theorem double_arctan (x : ℝ) :
    Real.cos (2*Real.arctan x)=(1-x^2)/(1+x^2) ∧
    Real.sin (2*Real.arctan x)=2*x/(1+x^2) := by
  have hp : 0<1+x^2 := by positivity
  have hr := Real.sq_sqrt hp.le
  have hn := (Real.sqrt_pos.mpr hp).ne'
  constructor
  · rw [Real.cos_two_mul,Real.cos_arctan,div_pow,hr]
    field_simp [hp.ne']
    ring
  · rw [Real.sin_two_mul,Real.cos_arctan,Real.sin_arctan]
    field_simp [hp.ne',hn]
    rw [hr]

private def ComplexAdmits (u w : ℝ) (f : ℝ→ℂ) : Prop :=
  Admits u w (fun s => (f s).re) ∧ Admits u w (fun s => (f s).im)

private theorem complex_const (u w : ℝ) (z : ℂ) : ComplexAdmits u w (fun _=>z) :=
  ⟨admits_const _ _ _,admits_const _ _ _⟩

private theorem complex_add {u w : ℝ} {f g : ℝ → ℂ} (hf : ComplexAdmits u w f)
    (hg : ComplexAdmits u w g) : ComplexAdmits u w (fun s=>f s+g s) :=
  ⟨admits_add hf.1 hg.1,admits_add hf.2 hg.2⟩

private theorem complex_mul {u w : ℝ} {f g : ℝ → ℂ} (hf : ComplexAdmits u w f)
    (hg : ComplexAdmits u w g) : ComplexAdmits u w (fun s=>f s*g s) := by
  constructor
  · exact admits_sub (admits_mul hf.1 hg.1) (admits_mul hf.2 hg.2)
  · simpa only [Complex.mul_im] using
      admits_add (admits_mul hf.1 hg.2) (admits_mul hf.2 hg.1)

private theorem complex_pow {u w : ℝ} {f : ℝ → ℂ} (hf : ComplexAdmits u w f) (n : ℕ) :
    ComplexAdmits u w (fun s=>f s^n) := by
  induction n with
  | zero => simpa only [pow_zero] using complex_const u w 1
  | succ n ih => simpa only [pow_succ] using complex_mul ih hf

private def phase (w s : ℝ) : ℂ := ((w*s:ℝ):ℂ)*Complex.I

private theorem first_mode (u w : ℝ) (hw : w≠0) :
    ComplexAdmits u w (fun s=>Complex.exp (phase w s)) := by
  have arg (x : ℝ) : w*chart u w x=w*u+2*Real.arctan x := by unfold chart; field_simp
  constructor
  · refine ⟨1,C (Real.cos (w*u))*(1-X^2)-C (Real.sin (w*u))*(C 2*X),fun x=>?_⟩
    simp only [phase,Complex.exp_ofReal_mul_I_re,arg,Real.cos_add,
      (double_arctan x).1,(double_arctan x).2,eval_sub,eval_mul,eval_pow,eval_C,eval_one,eval_X,pow_one]
    field_simp [show (1+x^2:ℝ)≠0 by positivity]
  · refine ⟨1,C (Real.sin (w*u))*(1-X^2)+C (Real.cos (w*u))*(C 2*X),fun x=>?_⟩
    simp only [phase,Complex.exp_ofReal_mul_I_im,arg,Real.sin_add,
      (double_arctan x).1,(double_arctan x).2,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_one,eval_X,pow_one]
    field_simp [show (1+x^2:ℝ)≠0 by positivity]

private theorem integer_mode (u w : ℝ) (hw : w≠0) (j : ℤ) :
    ComplexAdmits u w (fun s=>Complex.exp ((j:ℂ)*phase w s)) := by
  have pos := first_mode u w hw
  cases j with
  | ofNat n =>
    change ComplexAdmits u w (fun s=>Complex.exp ((n:ℂ)*phase w s))
    simpa only [Complex.exp_nat_mul] using complex_pow pos n
  | negSucc n =>
    have neg : ComplexAdmits u w (fun s=>Complex.exp (-phase w s)) := by
      have eq : (fun s=>Complex.exp (-phase w s))=fun s=>conj (Complex.exp (phase w s)) := by
        funext s
        rw [←Complex.exp_conj]
        simp [phase]
      rw [eq]
      exact ⟨pos.1,admits_neg pos.2⟩
    have eq : (fun s => Complex.exp (((Int.negSucc n:ℤ):ℂ)*phase w s))=
        fun s => Complex.exp (-phase w s)^(n+1) := by
      funext s
      rw [←Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [eq]
    exact complex_pow neg (n+1)

theorem charts_of_finite_fourier {k : ℝ→ℝ} {P : ℝ} (hp : 0<P)
    (S : Finset ℤ) (c : ℤ → ℂ)
    (fourier : ∀ s : ℝ,(k s:ℂ)=∑ j ∈ S,c j*Complex.exp
      (2*(Real.pi:ℂ)*Complex.I*(j:ℂ)*(s:ℂ)/(P:ℂ))) (u : ℝ) :
    Admits u (2*Real.pi/P) k := by
  let w := 2*Real.pi/P
  have hw : w≠0 := ne_of_gt (by dsimp [w]; positivity)
  have fits (T : Finset ℤ) : ComplexAdmits u w (fun s=>∑j∈T,c j*Complex.exp ((j:ℂ)*phase w s)) := by
    induction T using Finset.induction_on with
    | empty => simpa using complex_const u w 0
    | insert j T hj ih =>
      simpa only [Finset.sum_insert hj] using complex_add
        (complex_mul (complex_const u w (c j)) (integer_mode u w hw j)) ih
  have eq : (fun s=>(∑ j ∈ S,c j*Complex.exp ((j:ℂ)*phase w s)).re)=k := by
    funext s
    rw [← Complex.ofReal_re (k s),fourier s]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    dsimp [phase,w]
    push_cast
    ring
  simpa only [eq] using (fits S).1

end ClosedSimilarity.TrigCurvature
