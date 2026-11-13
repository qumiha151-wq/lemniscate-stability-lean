module
import all SolitonClassification.Rotating.BoundedODE
import all SolitonClassification.Rotating.Field
import all SolitonClassification.Rotating.TaylorCoefficients
import all SolitonClassification.Rotating.ResidualODE
import all SolitonClassification.Rotating.FlowFoundation
import all SolitonClassification.Rotating.MidpointDerivative
import all SolitonClassification.Rotating.DerivativeVariation
import all SolitonClassification.Rotating.FlowDifferentiability
import all SolitonClassification.Rotating.PartialDerivatives
import all SolitonClassification.Rotating.FlowJoint
import all SolitonClassification.Rotating.FlowVariational
import all SolitonClassification.Rotating.FlowVariationalODE
import all SolitonClassification.Rotating.FieldHessian
import all SolitonClassification.Rotating.VariationConstants
import all SolitonClassification.Rotating.VariationConstantsWithin
import all SolitonClassification.Rotating.QuantitativeVariation
import all SolitonClassification.Rotating.FlowInverse
import all SolitonClassification.Rotating.FlowInverseODE
import all SolitonClassification.Rotating.FlowMetricCoordinates
import all SolitonClassification.Rotating.ReferenceInversePerturbation
import all SolitonClassification.Rotating.PointMatrixInverse
import all SolitonClassification.Rotating.MatrixColumnNorm
import all SolitonClassification.Rotating.RationalBall
import all SolitonClassification.Rotating.MatrixRowNorm
import all SolitonClassification.Rotating.PointMatrixCertificate
import all SolitonClassification.Rotating.FixedBall
import all SolitonClassification.Rotating.FixedField
import all SolitonClassification.Rotating.CandidateInitial
import all SolitonClassification.Rotating.PointMatrixGridBudget
import all SolitonClassification.Rotating.FlowTube
import all SolitonClassification.Rotating.FixedTaylor
import all SolitonClassification.Rotating.TaylorDataCertificate
import all SolitonClassification.Rotating.FixedEndpointReset
import all SolitonClassification.Rotating.VariationTaylor
import all SolitonClassification.Rotating.VariationDataCertificate
import all SolitonClassification.Rotating.MixedOrderVariation
import all SolitonClassification.Rotating.VariationLinearity
import all SolitonClassification.Rotating.AnalyticMajorantScalar
import all SolitonClassification.Rotating.AnalyticMajorantVector
import all SolitonClassification.Rotating.AnalyticMajorantVectorActual
import all SolitonClassification.Rotating.UniversalVariationMajorantScalar
import all SolitonClassification.Rotating.UniversalVariationMajorantVector
import all SolitonClassification.Rotating.UniversalVariationMajorantActual
import all SolitonClassification.Rotating.UniversalVariationMajorantResidual
import all SolitonClassification.Rotating.AnalyticMajorantBudget
import all SolitonClassification.Rotating.UniversalVariationMajorantBudget
import all SolitonClassification.Rotating.VariationOperatorBounds
import all SolitonClassification.Rotating.UniversalVariationTrueTailNeighborhood
import all SolitonClassification.Rotating.PolynomialEnvelope
import all SolitonClassification.Rotating.ResidualDataCertificate
import all SolitonClassification.Rotating.TrueLocalStateTail
import all SolitonClassification.Rotating.UniversalPolynomialTube
import all SolitonClassification.Rotating.UniversalTaylorResidual
import all SolitonClassification.Rotating.TrueLocalVariationTail
import all SolitonClassification.Rotating.SignedLocalTail
import all SolitonClassification.Rotating.UniversalTrueStateTail
import all SolitonClassification.Rotating.UniversalVariationTrueTail
import all SolitonClassification.Rotating.UniversalVariationOperatorTail
import all SolitonClassification.Rotating.ReferencePolynomialMatrix
import all SolitonClassification.Rotating.UniversalVariationOrder22
import all SolitonClassification.Rotating.ReferencePolynomialMatrix22
import all SolitonClassification.Rotating.FlowBootstrapGeometry
import all SolitonClassification.Rotating.RotatingGridMargin
import all SolitonClassification.Rotating.FlowMetricSegment
import all SolitonClassification.Rotating.FlowBootstrapCoordinates
import all SolitonClassification.Rotating.FlowBootstrapSegment
import all SolitonClassification.Rotating.FlowMetricReset
import all SolitonClassification.Rotating.FlowBootstrapReset
import all SolitonClassification.Rotating.FlowMetricDiscrete
import all SolitonClassification.Rotating.FlowBootstrapBudget
import all SolitonClassification.Rotating.FlowMetricGridData
import all SolitonClassification.Rotating.FlowMetricGlobal
import all SolitonClassification.Rotating.FlowBootstrapGridData
import all SolitonClassification.Rotating.PolynomialGridAssembly
import all SolitonClassification.Rotating.UniversalStateOrders
import all SolitonClassification.Rotating.UniversalReducedVariation
import all SolitonClassification.Rotating.RotatingGridMarginOrders
import all SolitonClassification.Rotating.FlowBootstrapGlobal
import all SolitonClassification.Rotating.FlowBootstrapNeighborhood
import all SolitonClassification.Rotating.BanachRoot
import all SolitonClassification.Rotating.ShootingRoot
import all SolitonClassification.Rotating.ActualShooting
import all SolitonClassification.Rotating.RotatingGridHorizon
import all SolitonClassification.Rotating.ExtendedPolynomialReference42
import all SolitonClassification.Rotating.ExtendedPolynomialGridAssembly42
import all SolitonClassification.Rotating.ExtendedPolynomialGridEndpoints42
import all SolitonClassification.Rotating.PolynomialPointGridBlock

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for (name,_) in (← getEnv).constants do
    let userName := privateToUserName name
    if (`SolitonClassification.Rotating).isPrefixOf userName then
      for ax in (← collectAxioms name) do
        unless #[`propext,`Classical.choice,`Quot.sound].contains ax do
          throwError "Full generic module audit failed: {name} depends on {ax}"
      count := count+1
      if userName != name then privateCount := privateCount+1
  logInfo m!"Full generic module audit: {count} declarations ({privateCount} private), standard axioms only."
