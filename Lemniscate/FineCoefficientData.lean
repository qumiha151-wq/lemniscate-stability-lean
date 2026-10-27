import Lemniscate.RefinedFourierEnclosure

/-! Explicit rational coefficient intervals; each endpoint is checked against
the proved analytic interval, not trusted as external numerical data. -/
namespace Lemniscate.CoarseArithmetic

def fineCoefficientData (j : ℕ) : Interval :=
  ([⟨456946581044463625364084482477/10^30,456946581044463625384636663210/10^30⟩,
    ⟨248605493237684325773105584004/10^30,248605493237684325781997237296/10^30⟩,
    ⟨21446385033543847991831365779/10^30,21446385033543847993092853802/10^30⟩,
    ⟨1390168655881868682647734381/10^30,1390168655881868682761673875/10^30⟩,
    ⟨80099512370182701405582361/10^30,80099512370182701414000950/10^30⟩,
    ⟨4326767225613839899326773/10^30,4326767225613839899881649/10^30⟩,
    ⟨224371878280849036711673/10^30,224371878280849036745640/10^30⟩,
    ⟨11311986010170610277964/10^30,11311986010170610279940/10^30⟩,
    ⟨558668844393654763243/10^30,558668844393654763354/10^30⟩,
    ⟨27160053500411431451/10^30,27160053500411431458/10^30⟩,
    ⟨1304102591118289978/10^30,1304102591118289979/10^30⟩,
    ⟨61990921058175324/10^30,61990921058175325/10^30⟩,
    ⟨2922404286222486/10^30,2922404286222487/10^30⟩,
    ⟨136812584955059/10^30,136812584955060/10^30⟩,
    ⟨6366993083988/10^30,6366993083989/10^30⟩,
    ⟨294795770054/10^30,294795770055/10^30⟩,
    ⟨13588565665/10^30,13588565666/10^30⟩,
    ⟨623916113/10^30,623916114/10^30⟩,
    ⟨28547851/10^30,28547852/10^30⟩,
    ⟨1302201/10^30,1302202/10^30⟩,
    ⟨59234/10^30,59235/10^30⟩,
    ⟨2687/10^30,2688/10^30⟩,
    ⟨121/10^30,122/10^30⟩,
    ⟨5/10^30,6/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩,
    ⟨0/10^30,1/10^30⟩] : List Interval).getD j (point 0)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fine_coefficient_data_comparisons : ∀ j : Fin 59,
    if j.val = 0 then
      (fineCoefficientData 0).lo ≤ refinedConstantInterval.lo ∧
        refinedConstantInterval.hi ≤ (fineCoefficientData 0).hi
    else
      (fineCoefficientData j.val).lo ≤ (refinedPositiveInterval j.val).lo ∧
        (refinedPositiveInterval j.val).hi ≤ (fineCoefficientData j.val).hi := by decide +kernel

theorem fine_coefficient_data_sound (j : Fin 59) :
    Contains (fineCoefficientData j.val) (fourierCoefficient thetaParameter nome j.val) := by
  have hd := fine_coefficient_data_comparisons j
  by_cases hj : j.val = 0
  · rw [if_pos hj] at hd
    simpa [hj,fourierCoefficient] using
      refined_constant_fourier_enclosure.mono (J := fineCoefficientData 0) hd.1 hd.2
  · rw [if_neg hj] at hd
    simpa only [fourierCoefficient,if_neg hj] using
      (refined_positive_fourier_enclosure j.val (Nat.pos_of_ne_zero hj)).mono
        (J := fineCoefficientData j.val) hd.1 hd.2

end Lemniscate.CoarseArithmetic
