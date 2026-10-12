import Lemniscate

/-! Print dependencies of substantive public results after compiling them.
Only standard Lean foundational axioms are acceptable. In particular neither
sorryAx nor Lean.ofReduceBool may occur in this output. -/
#print axioms Lemniscate.linearization_zero_order
#print axioms Lemniscate.weighted_young
#print axioms Lemniscate.garding_interpolation
#print axioms Lemniscate.multiple_cover_gap
#print axioms Lemniscate.degree_six_conversion
#print axioms Lemniscate.degree_four_conversion
#print axioms Lemniscate.bernstein_lower_bound
#print axioms Lemniscate.bernstein_absolute_majorant
#print axioms Lemniscate.CoarseArithmetic.cosine_rows
#print axioms Lemniscate.CoarseArithmetic.mul_sound
#print axioms Lemniscate.CoarseArithmetic.absUpper_sound
#print axioms Lemniscate.NeutralCoerciveOperator.kernel_is_neutral
#print axioms Lemniscate.NeutralCoerciveOperator.no_generalized_neutral
#print axioms Lemniscate.NeutralCoerciveOperator.nonzero_eigenvalue_bound
#print axioms Lemniscate.OddArithmetic.all_odd_bernstein_comparisons
#print axioms Lemniscate.OddArithmetic.all_odd_zero_comparisons
#print axioms Lemniscate.shiftedQuartic_uniform_bound
#print axioms Lemniscate.rotation_kernel
#print axioms Lemniscate.weighted_row_dissipation
#print axioms Lemniscate.physical_decay_identity
#print axioms Lemniscate.normalizedTime_at_unit_scale
#print axioms Lemniscate.OddArithmetic.odd_rows_positive_on_interval
#print axioms Lemniscate.HighFrequency.cosine_high_bound
#print axioms Lemniscate.HighFrequency.sine_high_bound
#print axioms Lemniscate.HighFrequency.odd_high_bound
#print axioms Lemniscate.HighFrequency.even_high_bound
#print axioms Lemniscate.complex_weighted_row_dissipation
