import Lemniscate.PeriodicSobolevFourierPolynomial

/-! Zero extension to a common finite set of Fourier modes.

One reconstruction identity works at every Sobolev order. It aligns
finite Galerkin approximations without changing any derivative coordinate.
-/
noncomputable section
namespace Lemniscate
open scoped BigOperators

/-- Zero extension of coefficients to the indicated finite ambient set.
The same definition can be used for initial data or coefficient curves. -/
def finiteFourierZeroExtend {R : Type*} [Zero R]
    (I J : Finset ℤ) (a : I → R) : J → R :=
  fun n => if hn : (n:ℤ) ∈ I then a ⟨(n:ℤ),hn⟩ else 0

variable (T : ℝ) [Fact (0 < T)]

/-- Enlarging the finite mode set by zero coefficients preserves the actual
Sobolev reconstruction, simultaneously at every Sobolev order. -/
theorem circle_sobolev_fourier_synthesis_zero_extend
    (m : ℕ) (I J : Finset ℤ) (hIJ : I ⊆ J) (a : I → ℂ) :
    circleSobolevFourierSynthesis T m J (finiteFourierZeroExtend I J a) =
      circleSobolevFourierSynthesis T m I a := by
  let c : ℤ → ℂ := fun n => if hn : n ∈ I then a ⟨n,hn⟩ else 0
  have hJ : circleSobolevFourierSynthesis T m J (finiteFourierZeroExtend I J a) =
      circleSobolevFourierPolynomial T m J c := by
    exact circle_sobolev_fourier_synthesis_restrict T m J c
  have hI : circleSobolevFourierSynthesis T m I a =
      circleSobolevFourierPolynomial T m I c := by
    simpa [c] using circle_sobolev_fourier_synthesis_restrict T m I c
  have hsum : circleSobolevFourierPolynomial T m I c =
      circleSobolevFourierPolynomial T m J c := by
    apply Finset.sum_subset hIJ
    intro n _ hn
    simp only [c,dif_neg hn,zero_smul]
  exact hJ.trans (hsum.symm.trans hI.symm)

/-- The difference of two finite reconstructions is reconstructed on their
union from the difference of the zero-extended coefficients. -/
theorem circle_sobolev_fourier_synthesis_sub_common_set
    (m : ℕ) (I K : Finset ℤ) (a : I → ℂ) (b : K → ℂ) :
    circleSobolevFourierSynthesis T m I a-circleSobolevFourierSynthesis T m K b =
      circleSobolevFourierSynthesis T m (I ∪ K)
        (finiteFourierZeroExtend I (I ∪ K) a-finiteFourierZeroExtend K (I ∪ K) b) := by
  rw [map_sub,
    circle_sobolev_fourier_synthesis_zero_extend T m I (I ∪ K) Finset.subset_union_left a,
    circle_sobolev_fourier_synthesis_zero_extend T m K (I ∪ K) Finset.subset_union_right b]

end Lemniscate
