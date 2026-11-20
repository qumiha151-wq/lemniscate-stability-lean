import SolitonClassification.FrozenEndpointDecode
import SolitonClassification.FrozenEndpointConsequences
import SolitonClassification.FrozenDyadicNegative00
import SolitonClassification.FrozenDyadicNegative01
import SolitonClassification.FrozenDyadicNegative02
import SolitonClassification.FrozenDyadicNegative03
import SolitonClassification.FrozenDyadicNegative04
import SolitonClassification.FrozenDyadicNegative05
import SolitonClassification.FrozenDyadicNegative06
import SolitonClassification.FrozenDyadicNegative07
import SolitonClassification.FrozenDyadicNegative08
import SolitonClassification.FrozenDyadicNegative09
import SolitonClassification.FrozenDyadicNegative10
import SolitonClassification.FrozenDyadicNegative11
import SolitonClassification.FrozenDyadicNegative12
import SolitonClassification.FrozenDyadicNegative13
import SolitonClassification.FrozenDyadicNegative14
import SolitonClassification.FrozenDyadicNegative15
import SolitonClassification.FrozenDyadicNegative16
import SolitonClassification.FrozenDyadicNegative17
import SolitonClassification.FrozenDyadicNegative18
import SolitonClassification.FrozenDyadicNegative19
import SolitonClassification.FrozenDyadicNegative20
import SolitonClassification.FrozenDyadicNegative21
import SolitonClassification.FrozenDyadicNegative22
import SolitonClassification.FrozenDyadicNegative23
import SolitonClassification.FrozenDyadicNegative24
import SolitonClassification.FrozenDyadicNegative25
import SolitonClassification.FrozenDyadicNegative26
import SolitonClassification.FrozenDyadicNegative27
import SolitonClassification.FrozenDyadicNegative28
import SolitonClassification.FrozenDyadicNegative29
import SolitonClassification.FrozenDyadicNegative30
import SolitonClassification.FrozenDyadicNegative31
import SolitonClassification.FrozenDyadicNegative32
import SolitonClassification.FrozenDyadicNegative33
import SolitonClassification.FrozenDyadicNegative34
import SolitonClassification.FrozenDyadicNegative35
import SolitonClassification.FrozenDyadicNegative36
import SolitonClassification.FrozenDyadicNegative37
import SolitonClassification.FrozenDyadicNegative38
import SolitonClassification.FrozenDyadicNegative39
import SolitonClassification.FrozenDyadicPositive00
import SolitonClassification.FrozenDyadicPositive01
import SolitonClassification.FrozenDyadicPositive02
import SolitonClassification.FrozenDyadicPositive03
import SolitonClassification.FrozenDyadicPositive04
import SolitonClassification.FrozenDyadicPositive05
import SolitonClassification.FrozenDyadicPositive06
import SolitonClassification.FrozenDyadicPositive07
import SolitonClassification.FrozenDyadicPositive08
import SolitonClassification.FrozenDyadicPositive09
import SolitonClassification.FrozenDyadicPositive10
import SolitonClassification.FrozenDyadicPositive11
import SolitonClassification.FrozenDyadicPositive12
import SolitonClassification.FrozenDyadicPositive13
import SolitonClassification.FrozenDyadicPositive14
import SolitonClassification.FrozenDyadicPositive15
import SolitonClassification.FrozenDyadicPositive16
import SolitonClassification.FrozenDyadicPositive17
import SolitonClassification.FrozenDyadicPositive18
import SolitonClassification.FrozenDyadicPositive19
import SolitonClassification.FrozenDyadicPositive20
import SolitonClassification.FrozenDyadicPositive21
import SolitonClassification.FrozenDyadicPositive22
import SolitonClassification.FrozenDyadicPositive23
import SolitonClassification.FrozenDyadicPositive24
import SolitonClassification.FrozenDyadicPositive25
import SolitonClassification.FrozenDyadicPositive26
import SolitonClassification.FrozenDyadicPositive27
import SolitonClassification.FrozenDyadicPositive28
import SolitonClassification.FrozenDyadicPositive29
import SolitonClassification.FrozenDyadicPositive30
import SolitonClassification.FrozenDyadicPositive31
import SolitonClassification.FrozenDyadicPositive32
import SolitonClassification.FrozenDyadicPositive33
import SolitonClassification.FrozenDyadicPositive34
import SolitonClassification.FrozenDyadicPositive35
import SolitonClassification.FrozenDyadicPositive36
import SolitonClassification.FrozenDyadicPositive37
import SolitonClassification.FrozenDyadicPositive38
import SolitonClassification.FrozenDyadicPositive39

noncomputable section
namespace ClosedSimilarity.FrozenStress.Endpoint

theorem negative_end_to_end
    (z : Orbit) (hk : z.k 0=(-1/4)) (hv : z.v 0=0) (hp : z.p 0=1) (hq : z.q 0=0) :
    13 < -z.radial 20 ∧ -0.10 < correctedImpact z.root z.shape z.slope z.along z.across 20 ∧ correctedImpact z.root z.shape z.slope z.along z.across 20 < -0.09 ∧ |z.root 20*z.across 20| < 0.25 := by
  exact negative_from_transport (((((((((((((((((((((((((((((((((((((((negative_transport_0_16.trans negative_transport_16_32).trans negative_transport_32_48).trans negative_transport_48_64).trans negative_transport_64_80).trans negative_transport_80_96).trans negative_transport_96_112).trans negative_transport_112_128).trans negative_transport_128_144).trans negative_transport_144_160).trans negative_transport_160_176).trans negative_transport_176_192).trans negative_transport_192_208).trans negative_transport_208_224).trans negative_transport_224_240).trans negative_transport_240_256).trans negative_transport_256_272).trans negative_transport_272_288).trans negative_transport_288_304).trans negative_transport_304_320).trans negative_transport_320_336).trans negative_transport_336_352).trans negative_transport_352_368).trans negative_transport_368_384).trans negative_transport_384_400).trans negative_transport_400_416).trans negative_transport_416_432).trans negative_transport_432_448).trans negative_transport_448_464).trans negative_transport_464_480).trans negative_transport_480_496).trans negative_transport_496_512).trans negative_transport_512_528).trans negative_transport_528_544).trans negative_transport_544_560).trans negative_transport_560_576).trans negative_transport_576_592).trans negative_transport_592_608).trans negative_transport_608_624).trans negative_transport_624_640) z hk hv hp hq

theorem positive_end_to_end
    (z : Orbit) (hk : z.k 0=1) (hv : z.v 0=0) (hp : z.p 0=1) (hq : z.q 0=0) :
    12 < -z.radial 20 ∧ 0.8 < correctedImpact z.root z.shape z.slope z.along z.across 20 := by
  exact positive_from_transport (((((((((((((((((((((((((((((((((((((((positive_transport_0_16.trans positive_transport_16_32).trans positive_transport_32_48).trans positive_transport_48_64).trans positive_transport_64_80).trans positive_transport_80_96).trans positive_transport_96_112).trans positive_transport_112_128).trans positive_transport_128_144).trans positive_transport_144_160).trans positive_transport_160_176).trans positive_transport_176_192).trans positive_transport_192_208).trans positive_transport_208_224).trans positive_transport_224_240).trans positive_transport_240_256).trans positive_transport_256_272).trans positive_transport_272_288).trans positive_transport_288_304).trans positive_transport_304_320).trans positive_transport_320_336).trans positive_transport_336_352).trans positive_transport_352_368).trans positive_transport_368_384).trans positive_transport_384_400).trans positive_transport_400_416).trans positive_transport_416_432).trans positive_transport_432_448).trans positive_transport_448_464).trans positive_transport_464_480).trans positive_transport_480_496).trans positive_transport_496_512).trans positive_transport_512_528).trans positive_transport_528_544).trans positive_transport_544_560).trans positive_transport_560_576).trans positive_transport_576_592).trans positive_transport_592_608).trans positive_transport_608_624).trans positive_transport_624_640) z hk hv hp hq

theorem realized_terminal_bounds : TerminalBounds := by
  obtain ⟨nk,nv,np,nq⟩ := GlobalSupport.seam_initial (-1/4)
  obtain ⟨pk,pv,pp,pq⟩ := GlobalSupport.seam_initial 1
  have neg := negative_end_to_end _ nk nv np nq
  have pos := positive_end_to_end _ pk pv pp pq
  exact ⟨⟨neg.1,neg.2.1,neg.2.2.1⟩,pos⟩

theorem realized_seams_on_both_tails (s : ℝ) (hs : 20 ≤ |s|) :
    (GlobalSupport.seam (-1/4)).rawI s < -0.002 ∧
    0.52 < (GlobalSupport.seam 1).rawI s :=
  realized_terminal_bounds.both_tails s hs

theorem exists_transverse_zero_pair {t : ℝ} (ht : 20≤t) :
    ∃ c ∈ Set.Ioo (-1/4 : ℝ) 1,
      (GlobalSupport.seam c).transverse t=0 ∧ (GlobalSupport.seam c).transverse (-t)=0 ∧
      (GlobalSupport.seam c).radial t<0 ∧ 0<(GlobalSupport.seam c).radial (-t) :=
  realized_terminal_bounds.opposite_sections ht

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.negative_end_to_end
#print axioms ClosedSimilarity.FrozenStress.Endpoint.positive_end_to_end
#print axioms ClosedSimilarity.FrozenStress.Endpoint.realized_seams_on_both_tails
#print axioms ClosedSimilarity.FrozenStress.Endpoint.exists_transverse_zero_pair
