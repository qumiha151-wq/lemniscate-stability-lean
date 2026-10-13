import Lemniscate.GeometricTails

/-! Exact convergence and sums for moments four through six, used in the
sine constraint and the adjoint-vector tail estimates. -/
namespace Lemniscate

theorem hasSum_geometric_moment_four (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^4*z^n) (z*(1+11*z+11*z^2+z^3)/(1-z)^5) := by
  have hden : 1-z ≠ 0 := by
    have hlt : z < 1 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 4 hz
  let s := ∑' n : ℕ, (n:ℝ)^4*z^n
  have h0 := hasSum_geometric_moment_zero z hz
  have h1 := hasSum_geometric_moment_one z hz
  have h2 := hasSum_geometric_moment_two z hz
  have h3 := hasSum_geometric_moment_three z hz
  have hnext : HasSum (fun n : ℕ => ((n:ℝ)+1)^4*z^n)
      (s+4*(z*(1+4*z+z^2)/(1-z)^4)+6*(z*(1+z)/(1-z)^3)+4*(z/(1-z)^2)+1*(1/(1-z))) := by
    convert! ((((hs.hasSum.add (h3.mul_left 4)).add (h2.mul_left 6)).add (h1.mul_left 4)).add (h0.mul_left 1)) using 1
    ext n
    ring
  have heq : s = z*(s+4*(z*(1+4*z+z^2)/(1-z)^4)+6*(z*(1+z)/(1-z)^3)+4*(z/(1-z)^2)+1*(1/(1-z))) := by
    calc
      s = ∑' n : ℕ, ((n+1:ℕ):ℝ)^4*z^(n+1) := by
        simpa only [Nat.cast_zero, zero_pow (by decide : 4 ≠ 0), zero_mul, zero_add]
          using hs.tsum_eq_zero_add
      _ = _ := by
        convert! (hnext.mul_left z).tsum_eq using 1
        congr 1
        ext n
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  have hsval : s = z*(1+11*z+11*z^2+z^3)/(1-z)^5 := by
    have hf : (1-z)*s = z*(4*(z*(1+4*z+z^2)/(1-z)^4)+6*(z*(1+z)/(1-z)^3)+4*(z/(1-z)^2)+1*(1/(1-z))) := by linarith
    field_simp [hden] at hf ⊢
    nlinarith [hf]
  simpa only [← hsval] using hs.hasSum

theorem hasSum_geometric_moment_five (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^5*z^n) (z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6) := by
  have hden : 1-z ≠ 0 := by
    have hlt : z < 1 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 5 hz
  let s := ∑' n : ℕ, (n:ℝ)^5*z^n
  have h0 := hasSum_geometric_moment_zero z hz
  have h1 := hasSum_geometric_moment_one z hz
  have h2 := hasSum_geometric_moment_two z hz
  have h3 := hasSum_geometric_moment_three z hz
  have h4 := hasSum_geometric_moment_four z hz
  have hnext : HasSum (fun n : ℕ => ((n:ℝ)+1)^5*z^n)
      (s+5*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+10*(z*(1+4*z+z^2)/(1-z)^4)+10*(z*(1+z)/(1-z)^3)+5*(z/(1-z)^2)+1*(1/(1-z))) := by
    convert! (((((hs.hasSum.add (h4.mul_left 5)).add (h3.mul_left 10)).add (h2.mul_left 10)).add (h1.mul_left 5)).add (h0.mul_left 1)) using 1
    ext n
    ring
  have heq : s = z*(s+5*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+10*(z*(1+4*z+z^2)/(1-z)^4)+10*(z*(1+z)/(1-z)^3)+5*(z/(1-z)^2)+1*(1/(1-z))) := by
    calc
      s = ∑' n : ℕ, ((n+1:ℕ):ℝ)^5*z^(n+1) := by
        simpa only [Nat.cast_zero, zero_pow (by decide : 5 ≠ 0), zero_mul, zero_add]
          using hs.tsum_eq_zero_add
      _ = _ := by
        convert! (hnext.mul_left z).tsum_eq using 1
        congr 1
        ext n
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  have hsval : s = z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6 := by
    have hf : (1-z)*s = z*(5*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+10*(z*(1+4*z+z^2)/(1-z)^4)+10*(z*(1+z)/(1-z)^3)+5*(z/(1-z)^2)+1*(1/(1-z))) := by linarith
    field_simp [hden] at hf ⊢
    nlinarith [hf]
  simpa only [← hsval] using hs.hasSum

theorem hasSum_geometric_moment_six (z : ℝ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^6*z^n) (z*(1+57*z+302*z^2+302*z^3+57*z^4+z^5)/(1-z)^7) := by
  have hden : 1-z ≠ 0 := by
    have hlt : z < 1 := lt_of_le_of_lt (le_abs_self z) hz
    linarith
  have hs := summable_pow_mul_geometric_of_norm_lt_one 6 hz
  let s := ∑' n : ℕ, (n:ℝ)^6*z^n
  have h0 := hasSum_geometric_moment_zero z hz
  have h1 := hasSum_geometric_moment_one z hz
  have h2 := hasSum_geometric_moment_two z hz
  have h3 := hasSum_geometric_moment_three z hz
  have h4 := hasSum_geometric_moment_four z hz
  have h5 := hasSum_geometric_moment_five z hz
  have hnext : HasSum (fun n : ℕ => ((n:ℝ)+1)^6*z^n)
      (s+6*(z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6)+15*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+20*(z*(1+4*z+z^2)/(1-z)^4)+15*(z*(1+z)/(1-z)^3)+6*(z/(1-z)^2)+1*(1/(1-z))) := by
    convert! ((((((hs.hasSum.add (h5.mul_left 6)).add (h4.mul_left 15)).add (h3.mul_left 20)).add (h2.mul_left 15)).add (h1.mul_left 6)).add (h0.mul_left 1)) using 1
    ext n
    ring
  have heq : s = z*(s+6*(z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6)+15*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+20*(z*(1+4*z+z^2)/(1-z)^4)+15*(z*(1+z)/(1-z)^3)+6*(z/(1-z)^2)+1*(1/(1-z))) := by
    calc
      s = ∑' n : ℕ, ((n+1:ℕ):ℝ)^6*z^(n+1) := by
        simpa only [Nat.cast_zero, zero_pow (by decide : 6 ≠ 0), zero_mul, zero_add]
          using hs.tsum_eq_zero_add
      _ = _ := by
        convert! (hnext.mul_left z).tsum_eq using 1
        congr 1
        ext n
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  have hsval : s = z*(1+57*z+302*z^2+302*z^3+57*z^4+z^5)/(1-z)^7 := by
    have hf : (1-z)*s = z*(6*(z*(1+26*z+66*z^2+26*z^3+z^4)/(1-z)^6)+15*(z*(1+11*z+11*z^2+z^3)/(1-z)^5)+20*(z*(1+4*z+z^2)/(1-z)^4)+15*(z*(1+z)/(1-z)^3)+6*(z/(1-z)^2)+1*(1/(1-z))) := by linarith
    field_simp [hden] at hf ⊢
    nlinarith [hf]
  simpa only [← hsval] using hs.hasSum

end Lemniscate

