import SolitonClassification.Rotating.ReferencePolynomialMatrix
import SolitonClassification.Rotating.VariationStructure
import SolitonClassification.Rotating.UniversalVariationOrder22
import SolitonClassification.Rotating.FlowMetricDeviationAudit
import SolitonClassification.Rotating.UniversalTrueStateTail
import SolitonClassification.Rotating.LocalKernelAudit
import SolitonClassification.Rotating.FlowMetricAudit
import SolitonClassification.Rotating.FlowInverseAudit
import SolitonClassification.ScalarReflection
import SolitonClassification.Rotating.ActualFlowAudit
import SolitonClassification.Rotating.CoreAudit
import SolitonClassification.ScalarParameterUniqueness
import SolitonClassification.CircleLinearization
import SolitonClassification.NoClosedTranslators
import SolitonClassification.ScalarReconstructionCurve
import SolitonClassification.ScalarReconstructionEquivalence
import SolitonClassification.OddLocalRigidity
import SolitonClassification.SupportODE
import SolitonClassification.OneSignCurvature
import SolitonClassification.SolitonDilation

/-!
Closed self-similar solution classification: partial classification.
The verified module derives actual unit-speed, signed-curvature, support,
soliton, and closure identities from the support-coordinate ODE.
It permits a nonzero rotation coefficient. No periodic-orbit existence or
complete classification theorem is asserted.
OneSignCurvature additionally proves that actual periodic similarity ODE
profiles with one-sign curvature are centered circles. Nonconstant profiles
must have both positive and negative excursions larger than half their RMS
curvature. Actual closed reconstruction retains explicit angle holonomy.
This is an independent Lake project and imports no other open-problem project.
-/
